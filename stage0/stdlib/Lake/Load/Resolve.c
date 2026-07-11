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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(lean_object* v_toUpdate_1195_, lean_object* v_as_1196_, size_t v_i_1197_, size_t v_stop_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_fst_1203_; lean_object* v_snd_1204_; uint8_t v___x_1210_; 
v___x_1210_ = lean_usize_dec_eq(v_i_1197_, v_stop_1198_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; uint8_t v_inherited_1212_; 
v___x_1211_ = lean_array_uget_borrowed(v_as_1196_, v_i_1197_);
v_inherited_1212_ = lean_ctor_get_uint8(v___x_1211_, sizeof(void*)*5);
if (v_inherited_1212_ == 0)
{
lean_object* v_name_1213_; uint8_t v___x_1214_; 
v_name_1213_ = lean_ctor_get(v___x_1211_, 0);
v___x_1214_ = l_Lean_NameSet_contains(v_toUpdate_1195_, v_name_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_box(0);
lean_inc(v___x_1211_);
lean_inc(v_name_1213_);
v___x_1216_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1213_, v___x_1211_, v___y_1200_);
v_fst_1203_ = v___x_1215_;
v_snd_1204_ = v___x_1216_;
goto v___jp_1202_;
}
else
{
goto v___jp_1208_;
}
}
else
{
goto v___jp_1208_;
}
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_b_1199_);
lean_ctor_set(v___x_1217_, 1, v___y_1200_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
v___jp_1202_:
{
size_t v___x_1205_; size_t v___x_1206_; 
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_add(v_i_1197_, v___x_1205_);
v_i_1197_ = v___x_1206_;
v_b_1199_ = v_fst_1203_;
v___y_1200_ = v_snd_1204_;
goto _start;
}
v___jp_1208_:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_box(0);
v_fst_1203_ = v___x_1209_;
v_snd_1204_ = v___y_1200_;
goto v___jp_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg___boxed(lean_object* v_toUpdate_1219_, lean_object* v_as_1220_, lean_object* v_i_1221_, lean_object* v_stop_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
size_t v_i_boxed_1226_; size_t v_stop_boxed_1227_; lean_object* v_res_1228_; 
v_i_boxed_1226_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_stop_boxed_1227_ = lean_unbox_usize(v_stop_1222_);
lean_dec(v_stop_1222_);
v_res_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1219_, v_as_1220_, v_i_boxed_1226_, v_stop_boxed_1227_, v_b_1223_, v___y_1224_);
lean_dec_ref(v_as_1220_);
lean_dec(v_toUpdate_1219_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1229_, size_t v_i_1230_, size_t v_stop_1231_, lean_object* v_b_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_eq(v_i_1230_, v_stop_1231_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; 
v___x_1236_ = lean_array_uget_borrowed(v_as_1229_, v_i_1230_);
lean_inc_ref(v___y_1233_);
lean_inc(v___x_1236_);
v___x_1237_ = lean_apply_2(v___y_1233_, v___x_1236_, lean_box(0));
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1230_, v___x_1238_);
v_i_1230_ = v___x_1239_;
v_b_1232_ = v___x_1237_;
goto _start;
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_b_1232_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1242_, lean_object* v_i_1243_, lean_object* v_stop_1244_, lean_object* v_b_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
size_t v_i_boxed_1248_; size_t v_stop_boxed_1249_; lean_object* v_res_1250_; 
v_i_boxed_1248_ = lean_unbox_usize(v_i_1243_);
lean_dec(v_i_1243_);
v_stop_boxed_1249_ = lean_unbox_usize(v_stop_1244_);
lean_dec(v_stop_1244_);
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1242_, v_i_boxed_1248_, v_stop_boxed_1249_, v_b_1245_, v___y_1246_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v_as_1242_);
return v_res_1250_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1258_ = lean_array_get_size(v___x_1257_);
return v___x_1258_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_nat_dec_lt(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1263_ = lean_nat_dec_le(v___x_1262_, v___x_1262_);
return v___x_1263_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8(void){
_start:
{
lean_object* v___x_1264_; size_t v___x_1265_; 
v___x_1264_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1265_ = lean_usize_of_nat(v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1268_, lean_object* v_toUpdate_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___y_1274_; lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v_packages_1295_; lean_object* v___x_1296_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v_val_1301_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___x_1349_; lean_object* v_baseName_1350_; lean_object* v_dir_1351_; lean_object* v_config_1352_; lean_object* v_relManifestFile_1353_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; uint8_t v___y_1358_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; uint8_t v_fst_1382_; lean_object* v_snd_1383_; lean_object* v_packagesDir_x3f_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1432_; lean_object* v___y_1433_; uint8_t v___x_1436_; lean_object* v_rootName_1437_; lean_object* v_fst_1439_; lean_object* v_snd_1440_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_val_1491_; lean_object* v___x_1517_; 
v_packages_1295_ = lean_ctor_get(v_ws_1268_, 4);
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1349_ = lean_array_fget_borrowed(v_packages_1295_, v___x_1296_);
v_baseName_1350_ = lean_ctor_get(v___x_1349_, 1);
v_dir_1351_ = lean_ctor_get(v___x_1349_, 4);
v_config_1352_ = lean_ctor_get(v___x_1349_, 6);
v_relManifestFile_1353_ = lean_ctor_get(v___x_1349_, 9);
v___x_1436_ = 0;
lean_inc(v_baseName_1350_);
v_rootName_1437_ = l_Lean_Name_toString(v_baseName_1350_, v___x_1436_);
lean_inc_ref(v_relManifestFile_1353_);
lean_inc_ref(v_dir_1351_);
v___x_1488_ = l_Lake_joinRelative(v_dir_1351_, v_relManifestFile_1353_);
v___x_1489_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1517_ = l_Lake_Manifest_load(v___x_1488_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 1);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
v_val_1491_ = v___x_1523_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1517_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1517_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 0);
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
v_val_1491_ = v___x_1531_;
goto v___jp_1490_;
}
}
}
v___jp_1273_:
{
if (lean_obj_tag(v_fst_1275_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_snd_1276_);
v_a_1277_ = lean_ctor_get(v_fst_1275_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_fst_1275_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1279_ = v_fst_1275_;
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v_fst_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1281_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1282_ = lean_io_error_to_string(v_a_1277_);
v___x_1283_ = lean_string_append(v___x_1281_, v___x_1282_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = 3;
v___x_1285_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set_uint8(v___x_1285_, sizeof(void*)*1, v___x_1284_);
lean_inc_ref(v___y_1274_);
v___x_1286_ = lean_apply_2(v___y_1274_, v___x_1285_, lean_box(0));
v___x_1287_ = lean_box(0);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
lean_ctor_set(v___x_1279_, 0, v___x_1287_);
v___x_1289_ = v___x_1279_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec_ref(v_fst_1275_);
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v_snd_1276_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
v___jp_1297_:
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = lean_array_get_size(v___y_1300_);
v___x_1303_ = lean_nat_dec_lt(v___x_1296_, v___x_1302_);
if (v___x_1303_ == 0)
{
v___y_1274_ = v___y_1299_;
v_fst_1275_ = v_val_1301_;
v_snd_1276_ = v___y_1298_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_nat_dec_le(v___x_1302_, v___x_1302_);
if (v___x_1305_ == 0)
{
if (v___x_1303_ == 0)
{
v___y_1274_ = v___y_1299_;
v_fst_1275_ = v_val_1301_;
v_snd_1276_ = v___y_1298_;
goto v___jp_1273_;
}
else
{
size_t v___x_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = ((size_t)0ULL);
v___x_1307_ = lean_usize_of_nat(v___x_1302_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1300_, v___x_1306_, v___x_1307_, v___x_1304_, v___y_1299_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_dec_ref_known(v___x_1308_, 1);
v___y_1274_ = v___y_1299_;
v_fst_1275_ = v_val_1301_;
v_snd_1276_ = v___y_1298_;
goto v___jp_1273_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v_val_1301_);
lean_dec(v___y_1298_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
else
{
size_t v___x_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = ((size_t)0ULL);
v___x_1318_ = lean_usize_of_nat(v___x_1302_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1300_, v___x_1317_, v___x_1318_, v___x_1304_, v___y_1299_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_dec_ref_known(v___x_1319_, 1);
v___y_1274_ = v___y_1299_;
v_fst_1275_ = v_val_1301_;
v_snd_1276_ = v___y_1298_;
goto v___jp_1273_;
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_val_1301_);
lean_dec(v___y_1298_);
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
v___jp_1328_:
{
if (lean_obj_tag(v___y_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_a_1333_ = lean_ctor_get(v___y_1332_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___y_1332_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___y_1332_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___y_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 1);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
v___y_1298_ = v___y_1329_;
v___y_1299_ = v___y_1330_;
v___y_1300_ = v___y_1331_;
v_val_1301_ = v___x_1338_;
goto v___jp_1297_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_a_1341_ = lean_ctor_get(v___y_1332_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___y_1332_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___y_1332_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___y_1332_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set_tag(v___x_1343_, 0);
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
v___y_1298_ = v___y_1329_;
v___y_1299_ = v___y_1330_;
v___y_1300_ = v___y_1331_;
v_val_1301_ = v___x_1346_;
goto v___jp_1297_;
}
}
}
}
v___jp_1354_:
{
if (v___y_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v___y_1356_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___y_1355_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
else
{
lean_object* v_toWorkspaceConfig_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_toWorkspaceConfig_1362_ = lean_ctor_get(v_config_1352_, 0);
v___x_1363_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1364_ = lean_string_append(v___x_1363_, v___y_1356_);
v___x_1365_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
lean_inc_ref(v_toWorkspaceConfig_1362_);
v___x_1367_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1362_);
lean_inc_ref(v_dir_1351_);
v___x_1368_ = l_Lake_joinRelative(v_dir_1351_, v___x_1367_);
v___x_1369_ = lean_string_append(v___x_1366_, v___x_1368_);
v___x_1370_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
v___x_1372_ = 1;
v___x_1373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*1, v___x_1372_);
lean_inc_ref(v___y_1357_);
v___x_1374_ = lean_apply_2(v___y_1357_, v___x_1373_, lean_box(0));
v___x_1375_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1368_);
v___x_1376_ = l_Lake_createParentDirs(v___x_1368_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref_known(v___x_1376_, 1);
v___x_1377_ = lean_io_rename(v___y_1356_, v___x_1368_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___y_1356_);
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1357_;
v___y_1331_ = v___x_1375_;
v___y_1332_ = v___x_1377_;
goto v___jp_1328_;
}
else
{
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___y_1356_);
v___y_1329_ = v___y_1355_;
v___y_1330_ = v___y_1357_;
v___y_1331_ = v___x_1375_;
v___y_1332_ = v___x_1376_;
goto v___jp_1328_;
}
}
}
v___jp_1378_:
{
lean_object* v_toWorkspaceConfig_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; uint8_t v___x_1389_; 
v_toWorkspaceConfig_1384_ = lean_ctor_get(v_config_1352_, 0);
v___x_1385_ = l_System_FilePath_normalize(v___y_1379_);
lean_inc_ref(v_toWorkspaceConfig_1384_);
v___x_1386_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1384_);
v___x_1387_ = l_System_FilePath_normalize(v___x_1386_);
v___x_1388_ = lean_string_dec_eq(v___x_1385_, v___x_1387_);
lean_dec_ref(v___x_1387_);
lean_dec_ref(v___x_1385_);
v___x_1389_ = lean_bool_not(v___x_1388_);
if (v___x_1389_ == 0)
{
v___y_1355_ = v_snd_1383_;
v___y_1356_ = v___y_1380_;
v___y_1357_ = v___y_1381_;
v___y_1358_ = v___x_1389_;
goto v___jp_1354_;
}
else
{
v___y_1355_ = v_snd_1383_;
v___y_1356_ = v___y_1380_;
v___y_1357_ = v___y_1381_;
v___y_1358_ = v_fst_1382_;
goto v___jp_1354_;
}
}
v___jp_1390_:
{
if (lean_obj_tag(v_packagesDir_x3f_1391_) == 1)
{
lean_object* v_val_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v_val_1394_ = lean_ctor_get(v_packagesDir_x3f_1391_, 0);
lean_inc_n(v_val_1394_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1391_, 1);
lean_inc_ref(v_dir_1351_);
v___x_1395_ = l_Lake_joinRelative(v_dir_1351_, v_val_1394_);
v___x_1396_ = l_System_FilePath_pathExists(v___x_1395_);
v___x_1397_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1398_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1398_ == 0)
{
v___y_1379_ = v_val_1394_;
v___y_1380_ = v___x_1395_;
v___y_1381_ = v___y_1393_;
v_fst_1382_ = v___x_1396_;
v_snd_1383_ = v___y_1392_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1400_ == 0)
{
if (v___x_1398_ == 0)
{
v___y_1379_ = v_val_1394_;
v___y_1380_ = v___x_1395_;
v___y_1381_ = v___y_1393_;
v_fst_1382_ = v___x_1396_;
v_snd_1383_ = v___y_1392_;
goto v___jp_1378_;
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1397_, v___x_1401_, v___x_1402_, v___x_1399_, v___y_1393_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_dec_ref_known(v___x_1403_, 1);
v___y_1379_ = v_val_1394_;
v___y_1380_ = v___x_1395_;
v___y_1381_ = v___y_1393_;
v_fst_1382_ = v___x_1396_;
v_snd_1383_ = v___y_1392_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v___x_1395_);
lean_dec(v_val_1394_);
lean_dec(v___y_1392_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1397_, v___x_1412_, v___x_1413_, v___x_1399_, v___y_1393_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_dec_ref_known(v___x_1414_, 1);
v___y_1379_ = v_val_1394_;
v___y_1380_ = v___x_1395_;
v___y_1381_ = v___y_1393_;
v_fst_1382_ = v___x_1396_;
v_snd_1383_ = v___y_1392_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___x_1395_);
lean_dec(v_val_1394_);
lean_dec(v___y_1392_);
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_packagesDir_x3f_1391_);
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___y_1392_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
v___jp_1426_:
{
lean_object* v_packagesDir_x3f_1430_; 
v_packagesDir_x3f_1430_ = lean_ctor_get(v___y_1427_, 2);
lean_inc(v_packagesDir_x3f_1430_);
lean_dec_ref(v___y_1427_);
v_packagesDir_x3f_1391_ = v_packagesDir_x3f_1430_;
v___y_1392_ = v___y_1428_;
v___y_1393_ = v___y_1429_;
goto v___jp_1390_;
}
v___jp_1431_:
{
if (lean_obj_tag(v___y_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v_snd_1435_; 
v_a_1434_ = lean_ctor_get(v___y_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___y_1433_, 1);
v_snd_1435_ = lean_ctor_get(v_a_1434_, 1);
lean_inc(v_snd_1435_);
lean_dec(v_a_1434_);
v___y_1427_ = v___y_1432_;
v___y_1428_ = v_snd_1435_;
v___y_1429_ = v_a_1271_;
goto v___jp_1426_;
}
else
{
lean_dec_ref(v___y_1432_);
return v___y_1433_;
}
}
v___jp_1438_:
{
if (lean_obj_tag(v_fst_1439_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1473_; 
v_a_1441_ = lean_ctor_get(v_fst_1439_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_fst_1439_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1443_ = v_fst_1439_;
v_isShared_1444_ = v_isSharedCheck_1473_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v_fst_1439_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1473_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
if (lean_obj_tag(v_a_1441_) == 11)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_dec_ref_known(v_a_1441_, 2);
v___x_1445_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1446_ = lean_string_append(v_rootName_1437_, v___x_1445_);
v___x_1447_ = 1;
v___x_1448_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set_uint8(v___x_1448_, sizeof(void*)*1, v___x_1447_);
lean_inc_ref(v_a_1271_);
v___x_1449_ = lean_apply_2(v_a_1271_, v___x_1448_, lean_box(0));
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_snd_1440_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1450_);
v___x_1452_ = v___x_1443_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1269_) == 0)
{
lean_object* v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec(v_snd_1440_);
lean_dec_ref(v_rootName_1437_);
v___x_1454_ = lean_io_error_to_string(v_a_1441_);
v___x_1455_ = 3;
v___x_1456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*1, v___x_1455_);
lean_inc_ref(v_a_1271_);
v___x_1457_ = lean_apply_2(v_a_1271_, v___x_1456_, lean_box(0));
v___x_1458_ = lean_box(0);
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 1);
lean_ctor_set(v___x_1443_, 0, v___x_1458_);
v___x_1460_ = v___x_1443_;
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
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1462_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_1463_ = lean_string_append(v_rootName_1437_, v___x_1462_);
v___x_1464_ = lean_io_error_to_string(v_a_1441_);
v___x_1465_ = lean_string_append(v___x_1463_, v___x_1464_);
lean_dec_ref(v___x_1464_);
v___x_1466_ = 2;
v___x_1467_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set_uint8(v___x_1467_, sizeof(void*)*1, v___x_1466_);
lean_inc_ref(v_a_1271_);
v___x_1468_ = lean_apply_2(v_a_1271_, v___x_1467_, lean_box(0));
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_snd_1440_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1469_);
v___x_1471_ = v___x_1443_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1437_);
if (lean_obj_tag(v_toUpdate_1269_) == 0)
{
lean_object* v_a_1474_; lean_object* v_packagesDir_x3f_1475_; lean_object* v_packages_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_a_1474_ = lean_ctor_get(v_fst_1439_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v_fst_1439_, 1);
v_packagesDir_x3f_1475_ = lean_ctor_get(v_a_1474_, 2);
v_packages_1476_ = lean_ctor_get(v_a_1474_, 3);
v___x_1477_ = lean_array_get_size(v_packages_1476_);
v___x_1478_ = lean_nat_dec_lt(v___x_1296_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_inc(v_packagesDir_x3f_1475_);
lean_dec(v_a_1474_);
v_packagesDir_x3f_1391_ = v_packagesDir_x3f_1475_;
v___y_1392_ = v_snd_1440_;
v___y_1393_ = v_a_1271_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_nat_dec_le(v___x_1477_, v___x_1477_);
if (v___x_1480_ == 0)
{
if (v___x_1478_ == 0)
{
lean_inc(v_packagesDir_x3f_1475_);
lean_dec(v_a_1474_);
v_packagesDir_x3f_1391_ = v_packagesDir_x3f_1475_;
v___y_1392_ = v_snd_1440_;
v___y_1393_ = v_a_1271_;
goto v___jp_1390_;
}
else
{
size_t v___x_1481_; size_t v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = ((size_t)0ULL);
v___x_1482_ = lean_usize_of_nat(v___x_1477_);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1269_, v_packages_1476_, v___x_1481_, v___x_1482_, v___x_1479_, v_snd_1440_);
v___y_1432_ = v_a_1474_;
v___y_1433_ = v___x_1483_;
goto v___jp_1431_;
}
}
else
{
size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = lean_usize_of_nat(v___x_1477_);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1269_, v_packages_1476_, v___x_1484_, v___x_1485_, v___x_1479_, v_snd_1440_);
v___y_1432_ = v_a_1474_;
v___y_1433_ = v___x_1486_;
goto v___jp_1431_;
}
}
}
else
{
lean_object* v_a_1487_; 
v_a_1487_ = lean_ctor_get(v_fst_1439_, 0);
lean_inc(v_a_1487_);
lean_dec_ref_known(v_fst_1439_, 1);
v___y_1427_ = v_a_1487_;
v___y_1428_ = v_snd_1440_;
v___y_1429_ = v_a_1271_;
goto v___jp_1426_;
}
}
}
v___jp_1490_:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1492_ == 0)
{
v_fst_1439_ = v_val_1491_;
v_snd_1440_ = v_a_1270_;
goto v___jp_1438_;
}
else
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1494_ == 0)
{
if (v___x_1492_ == 0)
{
v_fst_1439_ = v_val_1491_;
v_snd_1440_ = v_a_1270_;
goto v___jp_1438_;
}
else
{
size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1489_, v___x_1495_, v___x_1496_, v___x_1493_, v_a_1271_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref_known(v___x_1497_, 1);
v_fst_1439_ = v_val_1491_;
v_snd_1440_ = v_a_1270_;
goto v___jp_1438_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v_val_1491_);
lean_dec_ref(v_rootName_1437_);
lean_dec(v_a_1270_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
size_t v___x_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1489_, v___x_1506_, v___x_1507_, v___x_1493_, v_a_1271_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_dec_ref_known(v___x_1508_, 1);
v_fst_1439_ = v_val_1491_;
v_snd_1440_ = v_a_1270_;
goto v___jp_1438_;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec_ref(v_val_1491_);
lean_dec_ref(v_rootName_1437_);
lean_dec(v_a_1270_);
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1534_, lean_object* v_toUpdate_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1534_, v_toUpdate_1535_, v_a_1536_, v_a_1537_);
lean_dec_ref(v_a_1537_);
lean_dec(v_toUpdate_1535_);
lean_dec_ref(v_ws_1534_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_toUpdate_1540_, lean_object* v_as_1541_, size_t v_i_1542_, size_t v_stop_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1540_, v_as_1541_, v_i_1542_, v_stop_1543_, v_b_1544_, v___y_1545_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_toUpdate_1549_, lean_object* v_as_1550_, lean_object* v_i_1551_, lean_object* v_stop_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
size_t v_i_boxed_1557_; size_t v_stop_boxed_1558_; lean_object* v_res_1559_; 
v_i_boxed_1557_ = lean_unbox_usize(v_i_1551_);
lean_dec(v_i_1551_);
v_stop_boxed_1558_ = lean_unbox_usize(v_stop_1552_);
lean_dec(v_stop_1552_);
v_res_1559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_toUpdate_1549_, v_as_1550_, v_i_boxed_1557_, v_stop_boxed_1558_, v_b_1553_, v___y_1554_, v___y_1555_);
lean_dec_ref(v___y_1555_);
lean_dec_ref(v_as_1550_);
lean_dec(v_toUpdate_1549_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1560_, lean_object* v_as_1561_, size_t v_i_1562_, size_t v_stop_1563_, lean_object* v_b_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_fst_1568_; lean_object* v_snd_1569_; lean_object* v___y_1574_; lean_object* v_name_1575_; uint8_t v___x_1578_; 
v___x_1578_ = lean_usize_dec_eq(v_i_1562_, v_stop_1563_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v_name_1580_; lean_object* v_scope_1581_; lean_object* v_configFile_1582_; lean_object* v_manifestFile_x3f_1583_; lean_object* v_src_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1607_; 
v___x_1579_ = lean_array_uget(v_as_1561_, v_i_1562_);
v_name_1580_ = lean_ctor_get(v___x_1579_, 0);
v_scope_1581_ = lean_ctor_get(v___x_1579_, 1);
v_configFile_1582_ = lean_ctor_get(v___x_1579_, 2);
v_manifestFile_x3f_1583_ = lean_ctor_get(v___x_1579_, 3);
v_src_1584_ = lean_ctor_get(v___x_1579_, 4);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1586_ = v___x_1579_;
v_isShared_1587_ = v_isSharedCheck_1607_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_src_1584_);
lean_inc(v_manifestFile_x3f_1583_);
lean_inc(v_configFile_1582_);
lean_inc(v_scope_1581_);
lean_inc(v_name_1580_);
lean_dec(v___x_1579_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1607_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
uint8_t v___x_1588_; 
v___x_1588_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1580_, v___y_1565_);
if (v___x_1588_ == 0)
{
uint8_t v___x_1589_; 
v___x_1589_ = 1;
if (lean_obj_tag(v_src_1584_) == 0)
{
lean_object* v_dir_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1602_; 
v_dir_1590_ = lean_ctor_get(v_src_1584_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_src_1584_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1592_ = v_src_1584_;
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_dir_1590_);
lean_dec(v_src_1584_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1602_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_relPkgDir_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v_relPkgDir_1594_ = lean_ctor_get(v_dep_1560_, 1);
lean_inc_ref(v_relPkgDir_1594_);
v___x_1595_ = l_Lake_joinRelative(v_relPkgDir_1594_, v_dir_1590_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
lean_inc(v_name_1580_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 4, v___x_1597_);
v___x_1599_ = v___x_1586_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_name_1580_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_scope_1581_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_configFile_1582_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_manifestFile_x3f_1583_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_ctor_set_uint8(v___x_1599_, sizeof(void*)*5, v___x_1589_);
v___y_1574_ = v___x_1599_;
v_name_1575_ = v_name_1580_;
goto v___jp_1573_;
}
}
}
}
else
{
lean_object* v___x_1604_; 
lean_inc(v_name_1580_);
if (v_isShared_1587_ == 0)
{
v___x_1604_ = v___x_1586_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_name_1580_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_scope_1581_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_configFile_1582_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_manifestFile_x3f_1583_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_src_1584_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*5, v___x_1589_);
v___y_1574_ = v___x_1604_;
v_name_1575_ = v_name_1580_;
goto v___jp_1573_;
}
}
}
else
{
lean_object* v___x_1606_; 
lean_del_object(v___x_1586_);
lean_dec_ref(v_src_1584_);
lean_dec(v_manifestFile_x3f_1583_);
lean_dec_ref(v_configFile_1582_);
lean_dec_ref(v_scope_1581_);
lean_dec(v_name_1580_);
v___x_1606_ = lean_box(0);
v_fst_1568_ = v___x_1606_;
v_snd_1569_ = v___y_1565_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v_dep_1560_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_b_1564_);
lean_ctor_set(v___x_1608_, 1, v___y_1565_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
v___jp_1567_:
{
size_t v___x_1570_; size_t v___x_1571_; 
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_i_1562_, v___x_1570_);
v_i_1562_ = v___x_1571_;
v_b_1564_ = v_fst_1568_;
v___y_1565_ = v_snd_1569_;
goto _start;
}
v___jp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1575_, v___y_1574_, v___y_1565_);
v_fst_1568_ = v___x_1576_;
v_snd_1569_ = v___x_1577_;
goto v___jp_1567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1610_, lean_object* v_as_1611_, lean_object* v_i_1612_, lean_object* v_stop_1613_, lean_object* v_b_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
size_t v_i_boxed_1617_; size_t v_stop_boxed_1618_; lean_object* v_res_1619_; 
v_i_boxed_1617_ = lean_unbox_usize(v_i_1612_);
lean_dec(v_i_1612_);
v_stop_boxed_1618_ = lean_unbox_usize(v_stop_1613_);
lean_dec(v_stop_1613_);
v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1610_, v_as_1611_, v_i_boxed_1617_, v_stop_boxed_1618_, v_b_1614_, v___y_1615_);
lean_dec_ref(v_as_1611_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_manifestEntry_1626_; lean_object* v_pkgDir_1627_; lean_object* v_name_1628_; lean_object* v_manifestFile_x3f_1629_; lean_object* v___y_1631_; lean_object* v_fst_1632_; lean_object* v_snd_1633_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v_val_1693_; lean_object* v___y_1721_; 
v_manifestEntry_1626_ = lean_ctor_get(v_dep_1622_, 4);
v_pkgDir_1627_ = lean_ctor_get(v_dep_1622_, 0);
v_name_1628_ = lean_ctor_get(v_manifestEntry_1626_, 0);
v_manifestFile_x3f_1629_ = lean_ctor_get(v_manifestEntry_1626_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1629_) == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1627_);
v___x_1742_ = l_Lake_joinRelative(v_pkgDir_1627_, v___x_1741_);
v___y_1721_ = v___x_1742_;
goto v___jp_1720_;
}
else
{
lean_object* v_val_1743_; lean_object* v___x_1744_; 
v_val_1743_ = lean_ctor_get(v_manifestFile_x3f_1629_, 0);
lean_inc(v_val_1743_);
lean_inc_ref(v_pkgDir_1627_);
v___x_1744_ = l_Lake_joinRelative(v_pkgDir_1627_, v_val_1743_);
v___y_1721_ = v___x_1744_;
goto v___jp_1720_;
}
v___jp_1630_:
{
if (lean_obj_tag(v_fst_1632_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1663_; 
lean_inc(v_name_1628_);
lean_dec_ref(v_dep_1622_);
v_a_1634_ = lean_ctor_get(v_fst_1632_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_fst_1632_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1636_ = v_fst_1632_;
v_isShared_1637_ = v_isSharedCheck_1663_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v_fst_1632_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1663_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
if (lean_obj_tag(v_a_1634_) == 11)
{
uint8_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
lean_dec_ref_known(v_a_1634_, 2);
v___x_1638_ = 0;
v___x_1639_ = l_Lean_Name_toString(v_name_1628_, v___x_1638_);
v___x_1640_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
v___x_1642_ = lean_string_append(v___x_1641_, v___y_1631_);
lean_dec_ref(v___y_1631_);
v___x_1643_ = 2;
v___x_1644_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*1, v___x_1643_);
lean_inc_ref(v_a_1624_);
v___x_1645_ = lean_apply_2(v_a_1624_, v___x_1644_, lean_box(0));
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v_snd_1633_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1646_);
v___x_1648_ = v___x_1636_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
else
{
uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_dec_ref(v___y_1631_);
v___x_1650_ = 0;
v___x_1651_ = l_Lean_Name_toString(v_name_1628_, v___x_1650_);
v___x_1652_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1653_ = lean_string_append(v___x_1651_, v___x_1652_);
v___x_1654_ = lean_io_error_to_string(v_a_1634_);
v___x_1655_ = lean_string_append(v___x_1653_, v___x_1654_);
lean_dec_ref(v___x_1654_);
v___x_1656_ = 2;
v___x_1657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set_uint8(v___x_1657_, sizeof(void*)*1, v___x_1656_);
lean_inc_ref(v_a_1624_);
v___x_1658_ = lean_apply_2(v_a_1624_, v___x_1657_, lean_box(0));
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_snd_1633_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v___x_1659_);
v___x_1661_ = v___x_1636_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v___y_1631_);
v_a_1664_ = lean_ctor_get(v_fst_1632_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_fst_1632_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1666_ = v_fst_1632_;
v_isShared_1667_ = v_isSharedCheck_1688_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v_fst_1632_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1688_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_packages_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_packages_1668_ = lean_ctor_get(v_a_1664_, 3);
lean_inc_ref(v_packages_1668_);
lean_dec(v_a_1664_);
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = lean_array_get_size(v_packages_1668_);
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_nat_dec_lt(v___x_1669_, v___x_1670_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_dec_ref(v_packages_1668_);
lean_dec_ref(v_dep_1622_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v_snd_1633_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1673_);
v___x_1675_ = v___x_1666_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
uint8_t v___x_1677_; 
v___x_1677_ = lean_nat_dec_le(v___x_1670_, v___x_1670_);
if (v___x_1677_ == 0)
{
if (v___x_1672_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec_ref(v_packages_1668_);
lean_dec_ref(v_dep_1622_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1671_);
lean_ctor_set(v___x_1678_, 1, v_snd_1633_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set_tag(v___x_1666_, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1678_);
v___x_1680_ = v___x_1666_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
lean_del_object(v___x_1666_);
v___x_1682_ = ((size_t)0ULL);
v___x_1683_ = lean_usize_of_nat(v___x_1670_);
v___x_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1622_, v_packages_1668_, v___x_1682_, v___x_1683_, v___x_1671_, v_snd_1633_);
lean_dec_ref(v_packages_1668_);
return v___x_1684_;
}
}
else
{
size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
lean_del_object(v___x_1666_);
v___x_1685_ = ((size_t)0ULL);
v___x_1686_ = lean_usize_of_nat(v___x_1670_);
v___x_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1622_, v_packages_1668_, v___x_1685_, v___x_1686_, v___x_1671_, v_snd_1633_);
lean_dec_ref(v_packages_1668_);
return v___x_1687_;
}
}
}
}
}
v___jp_1689_:
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = lean_array_get_size(v___y_1691_);
v___x_1695_ = lean_nat_dec_lt(v___y_1690_, v___x_1694_);
if (v___x_1695_ == 0)
{
v___y_1631_ = v___y_1692_;
v_fst_1632_ = v_val_1693_;
v_snd_1633_ = v_a_1623_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = lean_box(0);
v___x_1697_ = lean_nat_dec_le(v___x_1694_, v___x_1694_);
if (v___x_1697_ == 0)
{
if (v___x_1695_ == 0)
{
v___y_1631_ = v___y_1692_;
v_fst_1632_ = v_val_1693_;
v_snd_1633_ = v_a_1623_;
goto v___jp_1630_;
}
else
{
size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = lean_usize_of_nat(v___x_1694_);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1691_, v___x_1698_, v___x_1699_, v___x_1696_, v_a_1624_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_dec_ref_known(v___x_1700_, 1);
v___y_1631_ = v___y_1692_;
v_fst_1632_ = v_val_1693_;
v_snd_1633_ = v_a_1623_;
goto v___jp_1630_;
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec_ref(v_val_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v_a_1623_);
lean_dec_ref(v_dep_1622_);
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
else
{
size_t v___x_1709_; size_t v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = lean_usize_of_nat(v___x_1694_);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1691_, v___x_1709_, v___x_1710_, v___x_1696_, v_a_1624_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_dec_ref_known(v___x_1711_, 1);
v___y_1631_ = v___y_1692_;
v_fst_1632_ = v_val_1693_;
v_snd_1633_ = v_a_1623_;
goto v___jp_1630_;
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v_val_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v_a_1623_);
lean_dec_ref(v_dep_1622_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
v___jp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1721_);
v___x_1724_ = l_Lake_Manifest_load(v___y_1721_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 1);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v___y_1690_ = v___x_1722_;
v___y_1691_ = v___x_1723_;
v___y_1692_ = v___y_1721_;
v_val_1693_ = v___x_1730_;
goto v___jp_1689_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1724_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1724_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 0);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
v___y_1690_ = v___x_1722_;
v___y_1691_ = v___x_1723_;
v___y_1692_ = v___y_1721_;
v_val_1693_ = v___x_1738_;
goto v___jp_1689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1745_, v_a_1746_, v_a_1747_);
lean_dec_ref(v_a_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1750_, lean_object* v_as_1751_, size_t v_i_1752_, size_t v_stop_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1750_, v_as_1751_, v_i_1752_, v_stop_1753_, v_b_1754_, v___y_1755_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1759_, lean_object* v_as_1760_, lean_object* v_i_1761_, lean_object* v_stop_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
size_t v_i_boxed_1767_; size_t v_stop_boxed_1768_; lean_object* v_res_1769_; 
v_i_boxed_1767_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_stop_boxed_1768_ = lean_unbox_usize(v_stop_1762_);
lean_dec(v_stop_1762_);
v_res_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1759_, v_as_1760_, v_i_boxed_1767_, v_stop_boxed_1768_, v_b_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v_as_1760_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1771_, lean_object* v_pkg_1772_, lean_object* v_dep_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_name_1777_; lean_object* v___x_1778_; 
v_name_1777_ = lean_ctor_get(v_dep_1773_, 0);
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1774_, v_name_1777_);
if (lean_obj_tag(v___x_1778_) == 1)
{
lean_object* v_val_1779_; lean_object* v_lakeEnv_1780_; lean_object* v_packages_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_config_1784_; lean_object* v_dir_1785_; lean_object* v_toWorkspaceConfig_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec_ref(v_dep_1773_);
lean_dec_ref(v_pkg_1772_);
v_val_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v_lakeEnv_1780_ = lean_ctor_get(v_ws_1771_, 0);
lean_inc_ref(v_lakeEnv_1780_);
v_packages_1781_ = lean_ctor_get(v_ws_1771_, 4);
lean_inc_ref(v_packages_1781_);
lean_dec_ref(v_ws_1771_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_array_fget(v_packages_1781_, v___x_1782_);
lean_dec_ref(v_packages_1781_);
v_config_1784_ = lean_ctor_get(v___x_1783_, 6);
lean_inc_ref(v_config_1784_);
v_dir_1785_ = lean_ctor_get(v___x_1783_, 4);
lean_inc_ref(v_dir_1785_);
lean_dec(v___x_1783_);
v_toWorkspaceConfig_1786_ = lean_ctor_get(v_config_1784_, 0);
lean_inc_ref(v_toWorkspaceConfig_1786_);
lean_dec_ref(v_config_1784_);
v___x_1787_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1786_);
v___x_1788_ = l_Lake_PackageEntry_materialize(v_val_1779_, v_lakeEnv_1780_, v_dir_1785_, v___x_1787_, v_a_1775_);
lean_dec_ref(v_lakeEnv_1780_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1797_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_a_1789_);
lean_ctor_set(v___x_1793_, 1, v_a_1774_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1793_);
v___x_1795_ = v___x_1791_;
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
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_a_1774_);
v_a_1798_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1788_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1788_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_wsIdx_1806_; lean_object* v_relDir_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; uint8_t v___x_1810_; lean_object* v___y_1812_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
lean_dec(v___x_1778_);
v_wsIdx_1806_ = lean_ctor_get(v_pkg_1772_, 0);
lean_inc(v_wsIdx_1806_);
v_relDir_1807_ = lean_ctor_get(v_pkg_1772_, 5);
lean_inc_ref(v_relDir_1807_);
lean_dec_ref(v_pkg_1772_);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_nat_dec_eq(v_wsIdx_1806_, v___x_1808_);
lean_dec(v_wsIdx_1806_);
v___x_1810_ = lean_bool_not(v___x_1809_);
v___x_1841_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1842_ = lean_string_dec_eq(v_relDir_1807_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lake_joinRelative(v_relDir_1807_, v___x_1841_);
v___y_1812_ = v___x_1843_;
goto v___jp_1811_;
}
else
{
v___y_1812_ = v_relDir_1807_;
goto v___jp_1811_;
}
v___jp_1811_:
{
lean_object* v_lakeEnv_1813_; lean_object* v_packages_1814_; lean_object* v___x_1815_; lean_object* v_config_1816_; lean_object* v_dir_1817_; lean_object* v_toWorkspaceConfig_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v_lakeEnv_1813_ = lean_ctor_get(v_ws_1771_, 0);
lean_inc_ref(v_lakeEnv_1813_);
v_packages_1814_ = lean_ctor_get(v_ws_1771_, 4);
lean_inc_ref(v_packages_1814_);
lean_dec_ref(v_ws_1771_);
v___x_1815_ = lean_array_fget(v_packages_1814_, v___x_1808_);
lean_dec_ref(v_packages_1814_);
v_config_1816_ = lean_ctor_get(v___x_1815_, 6);
lean_inc_ref(v_config_1816_);
v_dir_1817_ = lean_ctor_get(v___x_1815_, 4);
lean_inc_ref(v_dir_1817_);
lean_dec(v___x_1815_);
v_toWorkspaceConfig_1818_ = lean_ctor_get(v_config_1816_, 0);
lean_inc_ref(v_toWorkspaceConfig_1818_);
lean_dec_ref(v_config_1816_);
v___x_1819_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1818_);
v___x_1820_ = l_Lake_Dependency_materialize(v_dep_1773_, v___x_1810_, v_lakeEnv_1813_, v_dir_1817_, v___x_1819_, v___y_1812_, v_a_1775_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1832_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1832_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1832_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_manifestEntry_1825_; lean_object* v_name_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v_manifestEntry_1825_ = lean_ctor_get(v_a_1821_, 4);
v_name_1826_ = lean_ctor_get(v_manifestEntry_1825_, 0);
lean_inc_ref(v_manifestEntry_1825_);
lean_inc(v_name_1826_);
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1826_, v_manifestEntry_1825_, v_a_1774_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_a_1821_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1828_);
v___x_1830_ = v___x_1823_;
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
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec(v_a_1774_);
v_a_1833_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1820_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1820_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1844_, lean_object* v_pkg_1845_, lean_object* v_dep_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1844_, v_pkg_1845_, v_dep_1846_, v_a_1847_, v_a_1848_);
lean_dec_ref(v_a_1848_);
return v_res_1850_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1851_; 
v___x_1851_ = 4;
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1852_, lean_object* v_tc_x3f_1853_, uint8_t v_fixed_1854_, lean_object* v_self_1855_){
_start:
{
lean_object* v_clashes_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_clashes_1856_ = lean_ctor_get(v_self_1855_, 2);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_self_1855_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; lean_object* v_unused_1865_; 
v_unused_1864_ = lean_ctor_get(v_self_1855_, 1);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_self_1855_, 0);
lean_dec(v_unused_1865_);
v___x_1858_ = v_self_1855_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_clashes_1856_);
lean_dec(v_self_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_tc_x3f_1853_);
lean_ctor_set(v___x_1858_, 0, v_src_1852_);
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_src_1852_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_tc_x3f_1853_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_clashes_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_ctor_set_uint8(v___x_1861_, sizeof(void*)*3, v_fixed_1854_);
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1866_, lean_object* v_tc_x3f_1867_, lean_object* v_fixed_1868_, lean_object* v_self_1869_){
_start:
{
uint8_t v_fixed_boxed_1870_; lean_object* v_res_1871_; 
v_fixed_boxed_1870_ = lean_unbox(v_fixed_1868_);
v_res_1871_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1866_, v_tc_x3f_1867_, v_fixed_boxed_1870_, v_self_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1872_, lean_object* v_ver_1873_, uint8_t v_fixed_1874_, lean_object* v_self_1875_){
_start:
{
lean_object* v_src_1876_; lean_object* v_tc_x3f_1877_; lean_object* v_clashes_1878_; uint8_t v_fixed_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1888_; 
v_src_1876_ = lean_ctor_get(v_self_1875_, 0);
v_tc_x3f_1877_ = lean_ctor_get(v_self_1875_, 1);
v_clashes_1878_ = lean_ctor_get(v_self_1875_, 2);
v_fixed_1879_ = lean_ctor_get_uint8(v_self_1875_, sizeof(void*)*3);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_self_1875_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1881_ = v_self_1875_;
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_clashes_1878_);
lean_inc(v_tc_x3f_1877_);
lean_inc(v_src_1876_);
lean_dec(v_self_1875_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1888_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1883_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1883_, 0, v_src_1872_);
lean_ctor_set(v___x_1883_, 1, v_ver_1873_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*2, v_fixed_1874_);
v___x_1884_ = lean_array_push(v_clashes_1878_, v___x_1883_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 2, v___x_1884_);
v___x_1886_ = v___x_1881_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_src_1876_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_tc_x3f_1877_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v___x_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1887_, sizeof(void*)*3, v_fixed_1879_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1889_, lean_object* v_ver_1890_, lean_object* v_fixed_1891_, lean_object* v_self_1892_){
_start:
{
uint8_t v_fixed_boxed_1893_; lean_object* v_res_1894_; 
v_fixed_boxed_1893_ = lean_unbox(v_fixed_1891_);
v_res_1894_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1889_, v_ver_1890_, v_fixed_boxed_1893_, v_self_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v_as_1899_, size_t v_i_1900_, size_t v_stop_1901_, lean_object* v_b_1902_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_usize_dec_eq(v_i_1900_, v_stop_1901_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v_src_1905_; lean_object* v_ver_1906_; uint8_t v_fixed_1907_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1923_; 
v___x_1904_ = lean_array_uget_borrowed(v_as_1899_, v_i_1900_);
v_src_1905_ = lean_ctor_get(v___x_1904_, 0);
v_ver_1906_ = lean_ctor_get(v___x_1904_, 1);
v_fixed_1907_ = lean_ctor_get_uint8(v___x_1904_, sizeof(void*)*2);
if (v_fixed_1907_ == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1923_ = v___x_1927_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1928_; 
v___x_1928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1923_ = v___x_1928_;
goto v___jp_1922_;
}
v___jp_1908_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; size_t v___x_1919_; size_t v___x_1920_; 
v___x_1912_ = lean_string_append(v___y_1909_, v___y_1911_);
lean_dec_ref(v___y_1911_);
v___x_1913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1914_ = lean_string_append(v___x_1912_, v___x_1913_);
v___x_1915_ = 1;
lean_inc(v_src_1905_);
v___x_1916_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1905_, v___x_1915_);
v___x_1917_ = lean_string_append(v___x_1914_, v___x_1916_);
lean_dec_ref(v___x_1916_);
v___x_1918_ = lean_string_append(v___x_1917_, v___y_1910_);
v___x_1919_ = ((size_t)1ULL);
v___x_1920_ = lean_usize_add(v_i_1900_, v___x_1919_);
v_i_1900_ = v___x_1920_;
v_b_1902_ = v___x_1918_;
goto _start;
}
v___jp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_toString_1926_; 
v___x_1924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1925_ = lean_string_append(v_b_1902_, v___x_1924_);
v_toString_1926_ = lean_ctor_get(v_ver_1906_, 0);
lean_inc_ref(v_toString_1926_);
v___y_1909_ = v___x_1925_;
v___y_1910_ = v___y_1923_;
v___y_1911_ = v_toString_1926_;
goto v___jp_1908_;
}
}
else
{
return v_b_1902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v_as_1929_, lean_object* v_i_1930_, lean_object* v_stop_1931_, lean_object* v_b_1932_){
_start:
{
size_t v_i_boxed_1933_; size_t v_stop_boxed_1934_; lean_object* v_res_1935_; 
v_i_boxed_1933_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_stop_boxed_1934_ = lean_unbox_usize(v_stop_1931_);
lean_dec(v_stop_1931_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1929_, v_i_boxed_1933_, v_stop_boxed_1934_, v_b_1932_);
lean_dec_ref(v_as_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v_as_1936_, size_t v_i_1937_, size_t v_stop_1938_, lean_object* v_b_1939_){
_start:
{
uint8_t v___x_1940_; 
v___x_1940_ = lean_usize_dec_eq(v_i_1937_, v_stop_1938_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; lean_object* v_src_1942_; lean_object* v_ver_1943_; uint8_t v_fixed_1944_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1960_; 
v___x_1941_ = lean_array_uget_borrowed(v_as_1936_, v_i_1937_);
v_src_1942_ = lean_ctor_get(v___x_1941_, 0);
v_ver_1943_ = lean_ctor_get(v___x_1941_, 1);
v_fixed_1944_ = lean_ctor_get_uint8(v___x_1941_, sizeof(void*)*2);
if (v_fixed_1944_ == 0)
{
lean_object* v___x_1964_; 
v___x_1964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1960_ = v___x_1964_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1965_; 
v___x_1965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1960_ = v___x_1965_;
goto v___jp_1959_;
}
v___jp_1945_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; size_t v___x_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
v___x_1949_ = lean_string_append(v___y_1946_, v___y_1948_);
lean_dec_ref(v___y_1948_);
v___x_1950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1951_ = lean_string_append(v___x_1949_, v___x_1950_);
v___x_1952_ = 1;
lean_inc(v_src_1942_);
v___x_1953_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1942_, v___x_1952_);
v___x_1954_ = lean_string_append(v___x_1951_, v___x_1953_);
lean_dec_ref(v___x_1953_);
v___x_1955_ = lean_string_append(v___x_1954_, v___y_1947_);
v___x_1956_ = ((size_t)1ULL);
v___x_1957_ = lean_usize_add(v_i_1937_, v___x_1956_);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1936_, v___x_1957_, v_stop_1938_, v___x_1955_);
return v___x_1958_;
}
v___jp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_toString_1963_; 
v___x_1961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1962_ = lean_string_append(v_b_1939_, v___x_1961_);
v_toString_1963_ = lean_ctor_get(v_ver_1943_, 0);
lean_inc_ref(v_toString_1963_);
v___y_1946_ = v___x_1962_;
v___y_1947_ = v___y_1960_;
v___y_1948_ = v_toString_1963_;
goto v___jp_1945_;
}
}
else
{
return v_b_1939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v_as_1966_, lean_object* v_i_1967_, lean_object* v_stop_1968_, lean_object* v_b_1969_){
_start:
{
size_t v_i_boxed_1970_; size_t v_stop_boxed_1971_; lean_object* v_res_1972_; 
v_i_boxed_1970_ = lean_unbox_usize(v_i_1967_);
lean_dec(v_i_1967_);
v_stop_boxed_1971_ = lean_unbox_usize(v_stop_1968_);
lean_dec(v_stop_1968_);
v_res_1972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v_as_1966_, v_i_boxed_1970_, v_stop_boxed_1971_, v_b_1969_);
lean_dec_ref(v_as_1966_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_1973_, lean_object* v_as_1974_, size_t v_i_1975_, size_t v_stop_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_){
_start:
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_usize_dec_eq(v_i_1975_, v_stop_1976_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; lean_object* v_relPkgDir_1982_; lean_object* v_manifestEntry_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1981_ = lean_array_uget_borrowed(v_as_1974_, v_i_1975_);
v_relPkgDir_1982_ = lean_ctor_get(v___x_1981_, 1);
v_manifestEntry_1983_ = lean_ctor_get(v___x_1981_, 4);
lean_inc_ref(v_relPkgDir_1982_);
lean_inc_ref(v___x_1973_);
v___x_1984_ = l_Lake_joinRelative(v___x_1973_, v_relPkgDir_1982_);
v___x_1985_ = l_Lake_toolchainFileName;
v___x_1986_ = l_System_FilePath_join(v___x_1984_, v___x_1985_);
v___x_1987_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1986_);
lean_dec_ref(v___x_1986_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v_a_1990_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
if (lean_obj_tag(v_a_1988_) == 1)
{
lean_object* v_tc_x3f_1994_; 
v_tc_x3f_1994_ = lean_ctor_get(v_b_1977_, 1);
if (lean_obj_tag(v_tc_x3f_1994_) == 1)
{
lean_object* v_val_1995_; lean_object* v_src_1996_; lean_object* v_clashes_1997_; uint8_t v_fixed_1998_; lean_object* v_val_1999_; uint8_t v___x_2000_; uint8_t v___y_2002_; 
v_val_1995_ = lean_ctor_get(v_a_1988_, 0);
v_src_1996_ = lean_ctor_get(v_b_1977_, 0);
v_clashes_1997_ = lean_ctor_get(v_b_1977_, 2);
v_fixed_1998_ = lean_ctor_get_uint8(v_b_1977_, sizeof(void*)*3);
v_val_1999_ = lean_ctor_get(v_tc_x3f_1994_, 0);
v___x_2000_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1981_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2009_; 
v___x_2009_ = l_Lake_ToolchainVer_ble(v_val_1995_, v_val_1999_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; 
lean_inc_ref(v_clashes_1997_);
lean_inc(v_src_1996_);
lean_inc_ref(v_tc_x3f_1994_);
lean_dec_ref(v_b_1977_);
v___x_2010_ = lean_bool_not(v_fixed_1998_);
if (v___x_2010_ == 0)
{
v___y_2002_ = v___x_2010_;
goto v___jp_2001_;
}
else
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lake_ToolchainVer_blt(v_val_1999_, v_val_1995_);
v___y_2002_ = v___x_2011_;
goto v___jp_2001_;
}
}
else
{
lean_dec_ref_known(v_a_1988_, 1);
v_a_1990_ = v_b_1977_;
goto v___jp_1989_;
}
}
else
{
if (v_fixed_1998_ == 0)
{
lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2026_; 
lean_inc_ref(v_clashes_1997_);
lean_inc(v_src_1996_);
lean_inc_ref(v_tc_x3f_1994_);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_b_1977_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; 
v_unused_2027_ = lean_ctor_get(v_b_1977_, 2);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_b_1977_, 1);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_b_1977_, 0);
lean_dec(v_unused_2029_);
v___x_2013_ = v_b_1977_;
v_isShared_2014_ = v_isSharedCheck_2026_;
goto v_resetjp_2012_;
}
else
{
lean_dec(v_b_1977_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2026_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lake_ToolchainVer_ble(v_val_1999_, v_val_1995_);
if (v___x_2015_ == 0)
{
lean_object* v_name_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_inc(v_val_1995_);
lean_dec_ref_known(v_a_1988_, 1);
v_name_2016_ = lean_ctor_get(v_manifestEntry_1983_, 0);
lean_inc(v_name_2016_);
v___x_2017_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2017_, 0, v_name_2016_);
lean_ctor_set(v___x_2017_, 1, v_val_1995_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*2, v___x_2000_);
v___x_2018_ = lean_array_push(v_clashes_1997_, v___x_2017_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 2, v___x_2018_);
v___x_2020_ = v___x_2013_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_src_1996_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_tc_x3f_1994_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v___x_2018_);
lean_ctor_set_uint8(v_reuseFailAlloc_2021_, sizeof(void*)*3, v_fixed_1998_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
v_a_1990_ = v___x_2020_;
goto v___jp_1989_;
}
}
else
{
lean_object* v_name_2022_; lean_object* v___x_2024_; 
lean_dec(v_src_1996_);
lean_dec_ref_known(v_tc_x3f_1994_, 1);
v_name_2022_ = lean_ctor_get(v_manifestEntry_1983_, 0);
lean_inc(v_name_2022_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_a_1988_);
lean_ctor_set(v___x_2013_, 0, v_name_2022_);
v___x_2024_ = v___x_2013_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_name_2022_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_a_1988_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_clashes_1997_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*3, v___x_2000_);
v_a_1990_ = v___x_2024_;
goto v___jp_1989_;
}
}
}
}
else
{
uint8_t v___x_2030_; 
lean_inc_n(v_val_1995_, 2);
lean_dec_ref_known(v_a_1988_, 1);
lean_inc(v_val_1999_);
v___x_2030_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_1999_, v_val_1995_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2040_; 
lean_inc_ref(v_clashes_1997_);
lean_inc(v_src_1996_);
lean_inc_ref(v_tc_x3f_1994_);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_b_1977_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; lean_object* v_unused_2042_; lean_object* v_unused_2043_; 
v_unused_2041_ = lean_ctor_get(v_b_1977_, 2);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_b_1977_, 1);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_b_1977_, 0);
lean_dec(v_unused_2043_);
v___x_2032_ = v_b_1977_;
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v_b_1977_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_name_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_name_2034_ = lean_ctor_get(v_manifestEntry_1983_, 0);
lean_inc(v_name_2034_);
v___x_2035_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2035_, 0, v_name_2034_);
lean_ctor_set(v___x_2035_, 1, v_val_1995_);
lean_ctor_set_uint8(v___x_2035_, sizeof(void*)*2, v___x_2000_);
v___x_2036_ = lean_array_push(v_clashes_1997_, v___x_2035_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 2, v___x_2036_);
v___x_2038_ = v___x_2032_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_src_1996_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_tc_x3f_1994_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v___x_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2039_, sizeof(void*)*3, v_fixed_1998_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
v_a_1990_ = v___x_2038_;
goto v___jp_1989_;
}
}
}
else
{
lean_dec(v_val_1995_);
v_a_1990_ = v_b_1977_;
goto v___jp_1989_;
}
}
}
v___jp_2001_:
{
if (v___y_2002_ == 0)
{
lean_object* v_name_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_inc(v_val_1995_);
lean_dec_ref_known(v_a_1988_, 1);
v_name_2003_ = lean_ctor_get(v_manifestEntry_1983_, 0);
lean_inc(v_name_2003_);
v___x_2004_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2004_, 0, v_name_2003_);
lean_ctor_set(v___x_2004_, 1, v_val_1995_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*2, v___x_2000_);
v___x_2005_ = lean_array_push(v_clashes_1997_, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2006_, 0, v_src_1996_);
lean_ctor_set(v___x_2006_, 1, v_tc_x3f_1994_);
lean_ctor_set(v___x_2006_, 2, v___x_2005_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*3, v_fixed_1998_);
v_a_1990_ = v___x_2006_;
goto v___jp_1989_;
}
else
{
lean_object* v_name_2007_; lean_object* v___x_2008_; 
lean_dec(v_src_1996_);
lean_dec_ref_known(v_tc_x3f_1994_, 1);
v_name_2007_ = lean_ctor_get(v_manifestEntry_1983_, 0);
lean_inc(v_name_2007_);
v___x_2008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2008_, 0, v_name_2007_);
lean_ctor_set(v___x_2008_, 1, v_a_1988_);
lean_ctor_set(v___x_2008_, 2, v_clashes_1997_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*3, v___x_2000_);
v_a_1990_ = v___x_2008_;
goto v___jp_1989_;
}
}
}
else
{
lean_object* v_clashes_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2053_; 
v_clashes_2044_ = lean_ctor_get(v_b_1977_, 2);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_b_1977_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2054_ = lean_ctor_get(v_b_1977_, 1);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_b_1977_, 0);
lean_dec(v_unused_2055_);
v___x_2046_ = v_b_1977_;
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_clashes_2044_);
lean_dec(v_b_1977_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2053_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_name_2048_; uint8_t v___x_2049_; lean_object* v___x_2051_; 
v_name_2048_ = lean_ctor_get(v_manifestEntry_1983_, 0);
v___x_2049_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1981_);
lean_inc(v_name_2048_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v_a_1988_);
lean_ctor_set(v___x_2046_, 0, v_name_2048_);
v___x_2051_ = v___x_2046_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_name_2048_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_a_1988_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_clashes_2044_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*3, v___x_2049_);
v_a_1990_ = v___x_2051_;
goto v___jp_1989_;
}
}
}
}
else
{
lean_dec(v_a_1988_);
v_a_1990_ = v_b_1977_;
goto v___jp_1989_;
}
v___jp_1989_:
{
size_t v___x_1991_; size_t v___x_1992_; 
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_add(v_i_1975_, v___x_1991_);
v_i_1975_ = v___x_1992_;
v_b_1977_ = v_a_1990_;
goto _start;
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_b_1977_);
lean_dec_ref(v___x_1973_);
v_a_2056_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2058_ = v___x_1987_;
v_isShared_2059_ = v_isSharedCheck_2068_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1987_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2068_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2060_ = lean_io_error_to_string(v_a_2056_);
v___x_2061_ = 3;
v___x_2062_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2062_, 0, v___x_2060_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*1, v___x_2061_);
lean_inc_ref(v___y_1978_);
v___x_2063_ = lean_apply_2(v___y_1978_, v___x_2062_, lean_box(0));
v___x_2064_ = lean_box(0);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2064_);
v___x_2066_ = v___x_2058_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v___x_2069_; 
lean_dec_ref(v___x_1973_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_b_1977_);
return v___x_2069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2070_, lean_object* v_as_2071_, lean_object* v_i_2072_, lean_object* v_stop_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
size_t v_i_boxed_2077_; size_t v_stop_boxed_2078_; lean_object* v_res_2079_; 
v_i_boxed_2077_ = lean_unbox_usize(v_i_2072_);
lean_dec(v_i_2072_);
v_stop_boxed_2078_ = lean_unbox_usize(v_stop_2073_);
lean_dec(v_stop_2073_);
v_res_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2070_, v_as_2071_, v_i_boxed_2077_, v_stop_boxed_2078_, v_b_2074_, v___y_2075_);
lean_dec_ref(v___y_2075_);
lean_dec_ref(v_as_2071_);
return v_res_2079_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v___x_2090_ = lean_unsigned_to_nat(4u);
v___x_2091_ = lean_mk_empty_array_with_capacity(v___x_2090_);
v___x_2092_ = lean_array_push(v___x_2091_, v___x_2089_);
return v___x_2092_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2094_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6);
v___x_2095_ = lean_array_push(v___x_2094_, v___x_2093_);
return v___x_2095_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10(void){
_start:
{
uint32_t v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = 4;
v___x_2101_ = lean_uint32_to_uint8(v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2119_, lean_object* v_rootDeps_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___y_2124_; lean_object* v_lakeEnv_2129_; lean_object* v_lakeArgs_x3f_2130_; lean_object* v_packages_2131_; lean_object* v___y_2133_; uint8_t v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2278_; lean_object* v___y_2279_; uint8_t v___y_2280_; lean_object* v___x_2283_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; uint8_t v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2311_; uint8_t v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___x_2319_; lean_object* v_baseName_2320_; lean_object* v_dir_2321_; lean_object* v_config_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_lakeEnv_2129_ = lean_ctor_get(v_ws_2119_, 0);
lean_inc_ref(v_lakeEnv_2129_);
v_lakeArgs_x3f_2130_ = lean_ctor_get(v_ws_2119_, 3);
lean_inc(v_lakeArgs_x3f_2130_);
v_packages_2131_ = lean_ctor_get(v_ws_2119_, 4);
lean_inc_ref(v_packages_2131_);
lean_dec_ref(v_ws_2119_);
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_array_fget(v_packages_2131_, v___x_2283_);
lean_dec_ref(v_packages_2131_);
v_baseName_2320_ = lean_ctor_get(v___x_2319_, 1);
lean_inc(v_baseName_2320_);
v_dir_2321_ = lean_ctor_get(v___x_2319_, 4);
lean_inc_ref_n(v_dir_2321_, 2);
v_config_2322_ = lean_ctor_get(v___x_2319_, 6);
lean_inc_ref(v_config_2322_);
lean_dec(v___x_2319_);
v___x_2323_ = l_Lake_toolchainFileName;
v___x_2324_ = l_System_FilePath_join(v_dir_2321_, v___x_2323_);
v___x_2325_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2324_);
lean_dec_ref(v___x_2324_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2384_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2384_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2384_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_src_2331_; lean_object* v_tc_x3f_2332_; lean_object* v_clashes_2333_; uint8_t v_fixed_2334_; lean_object* v___y_2358_; uint8_t v_fixedToolchain_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_fixedToolchain_2372_ = lean_ctor_get_uint8(v_config_2322_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_2322_);
v___x_2373_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2374_ = lean_array_get_size(v_rootDeps_2120_);
v___x_2375_ = lean_nat_dec_lt(v___x_2283_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_inc(v_a_2326_);
v_src_2331_ = v_baseName_2320_;
v_tc_x3f_2332_ = v_a_2326_;
v_clashes_2333_ = v___x_2373_;
v_fixed_2334_ = v_fixedToolchain_2372_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2376_; uint8_t v___x_2377_; 
lean_inc(v_a_2326_);
lean_inc(v_baseName_2320_);
v___x_2376_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2376_, 0, v_baseName_2320_);
lean_ctor_set(v___x_2376_, 1, v_a_2326_);
lean_ctor_set(v___x_2376_, 2, v___x_2373_);
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*3, v_fixedToolchain_2372_);
v___x_2377_ = lean_nat_dec_le(v___x_2374_, v___x_2374_);
if (v___x_2377_ == 0)
{
if (v___x_2375_ == 0)
{
lean_dec_ref_known(v___x_2376_, 3);
lean_inc(v_a_2326_);
v_src_2331_ = v_baseName_2320_;
v_tc_x3f_2332_ = v_a_2326_;
v_clashes_2333_ = v___x_2373_;
v_fixed_2334_ = v_fixedToolchain_2372_;
goto v___jp_2330_;
}
else
{
size_t v___x_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
lean_dec(v_baseName_2320_);
v___x_2378_ = ((size_t)0ULL);
v___x_2379_ = lean_usize_of_nat(v___x_2374_);
lean_inc_ref(v_dir_2321_);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2321_, v_rootDeps_2120_, v___x_2378_, v___x_2379_, v___x_2376_, v_a_2121_);
v___y_2358_ = v___x_2380_;
goto v___jp_2357_;
}
}
else
{
size_t v___x_2381_; size_t v___x_2382_; lean_object* v___x_2383_; 
lean_dec(v_baseName_2320_);
v___x_2381_ = ((size_t)0ULL);
v___x_2382_ = lean_usize_of_nat(v___x_2374_);
lean_inc_ref(v_dir_2321_);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2321_, v_rootDeps_2120_, v___x_2381_, v___x_2382_, v___x_2376_, v_a_2121_);
v___y_2358_ = v___x_2383_;
goto v___jp_2357_;
}
}
v___jp_2330_:
{
lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = lean_array_get_size(v_clashes_2333_);
v___x_2336_ = lean_nat_dec_lt(v___x_2283_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_dec_ref(v_clashes_2333_);
lean_dec(v_src_2331_);
if (lean_obj_tag(v_tc_x3f_2332_) == 1)
{
lean_object* v_val_2337_; lean_object* v_rootToolchainFile_2338_; 
v_val_2337_ = lean_ctor_get(v_tc_x3f_2332_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v_tc_x3f_2332_, 1);
v_rootToolchainFile_2338_ = l_Lake_joinRelative(v_dir_2321_, v___x_2323_);
if (lean_obj_tag(v_a_2326_) == 0)
{
lean_del_object(v___x_2328_);
v___y_2278_ = v_val_2337_;
v___y_2279_ = v_rootToolchainFile_2338_;
v___y_2280_ = v___x_2336_;
goto v___jp_2277_;
}
else
{
lean_object* v_val_2339_; uint8_t v___x_2340_; 
v_val_2339_ = lean_ctor_get(v_a_2326_, 0);
lean_inc(v_val_2339_);
lean_dec_ref_known(v_a_2326_, 1);
lean_inc(v_val_2337_);
v___x_2340_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2339_, v_val_2337_);
if (v___x_2340_ == 0)
{
lean_del_object(v___x_2328_);
v___y_2278_ = v_val_2337_;
v___y_2279_ = v_rootToolchainFile_2338_;
v___y_2280_ = v___x_2340_;
goto v___jp_2277_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
lean_dec_ref(v_rootToolchainFile_2338_);
lean_dec(v_val_2337_);
lean_dec(v_lakeArgs_x3f_2130_);
lean_dec_ref(v_lakeEnv_2129_);
v___x_2341_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2121_);
v___x_2342_ = lean_apply_2(v_a_2121_, v___x_2341_, lean_box(0));
v___x_2343_ = lean_box(0);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2343_);
v___x_2345_ = v___x_2328_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec(v_tc_x3f_2332_);
lean_dec(v_a_2326_);
lean_dec_ref(v_dir_2321_);
lean_dec(v_lakeArgs_x3f_2130_);
lean_dec_ref(v_lakeEnv_2129_);
v___x_2347_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2121_);
v___x_2348_ = lean_apply_2(v_a_2121_, v___x_2347_, lean_box(0));
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2348_);
v___x_2350_ = v___x_2328_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_del_object(v___x_2328_);
lean_dec(v_a_2326_);
lean_dec_ref(v_dir_2321_);
lean_dec(v_lakeArgs_x3f_2130_);
lean_dec_ref(v_lakeEnv_2129_);
if (lean_obj_tag(v_tc_x3f_2332_) == 1)
{
if (v_fixed_2334_ == 0)
{
lean_object* v_val_2352_; lean_object* v___x_2353_; 
v_val_2352_ = lean_ctor_get(v_tc_x3f_2332_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v_tc_x3f_2332_, 1);
v___x_2353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2311_ = v_val_2352_;
v___y_2312_ = v___x_2336_;
v___y_2313_ = v_clashes_2333_;
v___y_2314_ = v___x_2335_;
v___y_2315_ = v_src_2331_;
v___y_2316_ = v___x_2353_;
goto v___jp_2310_;
}
else
{
lean_object* v_val_2354_; lean_object* v___x_2355_; 
v_val_2354_ = lean_ctor_get(v_tc_x3f_2332_, 0);
lean_inc(v_val_2354_);
lean_dec_ref_known(v_tc_x3f_2332_, 1);
v___x_2355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2311_ = v_val_2354_;
v___y_2312_ = v___x_2336_;
v___y_2313_ = v_clashes_2333_;
v___y_2314_ = v___x_2335_;
v___y_2315_ = v_src_2331_;
v___y_2316_ = v___x_2355_;
goto v___jp_2310_;
}
}
else
{
lean_object* v___x_2356_; 
lean_dec(v_tc_x3f_2332_);
lean_dec(v_src_2331_);
v___x_2356_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2285_ = v_clashes_2333_;
v___y_2286_ = v___x_2335_;
v___y_2287_ = v___x_2356_;
goto v___jp_2284_;
}
}
}
v___jp_2357_:
{
if (lean_obj_tag(v___y_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v_src_2360_; lean_object* v_tc_x3f_2361_; lean_object* v_clashes_2362_; uint8_t v_fixed_2363_; 
v_a_2359_ = lean_ctor_get(v___y_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___y_2358_, 1);
v_src_2360_ = lean_ctor_get(v_a_2359_, 0);
lean_inc(v_src_2360_);
v_tc_x3f_2361_ = lean_ctor_get(v_a_2359_, 1);
lean_inc(v_tc_x3f_2361_);
v_clashes_2362_ = lean_ctor_get(v_a_2359_, 2);
lean_inc_ref(v_clashes_2362_);
v_fixed_2363_ = lean_ctor_get_uint8(v_a_2359_, sizeof(void*)*3);
lean_dec(v_a_2359_);
v_src_2331_ = v_src_2360_;
v_tc_x3f_2332_ = v_tc_x3f_2361_;
v_clashes_2333_ = v_clashes_2362_;
v_fixed_2334_ = v_fixed_2363_;
goto v___jp_2330_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_del_object(v___x_2328_);
lean_dec(v_a_2326_);
lean_dec_ref(v_dir_2321_);
lean_dec(v_lakeArgs_x3f_2130_);
lean_dec_ref(v_lakeEnv_2129_);
v_a_2364_ = lean_ctor_get(v___y_2358_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___y_2358_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___y_2358_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___y_2358_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_config_2322_);
lean_dec_ref(v_dir_2321_);
lean_dec(v_baseName_2320_);
lean_dec(v_lakeArgs_x3f_2130_);
lean_dec_ref(v_lakeEnv_2129_);
v_a_2385_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2387_ = v___x_2325_;
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2325_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2397_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2389_ = lean_io_error_to_string(v_a_2385_);
v___x_2390_ = 3;
v___x_2391_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*1, v___x_2390_);
lean_inc_ref(v_a_2121_);
v___x_2392_ = lean_apply_2(v_a_2121_, v___x_2391_, lean_box(0));
v___x_2393_ = lean_box(0);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2393_);
v___x_2395_ = v___x_2387_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
v___jp_2123_:
{
uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2125_ = 2;
v___x_2126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2126_, 0, v___y_2124_);
lean_ctor_set_uint8(v___x_2126_, sizeof(void*)*1, v___x_2125_);
lean_inc_ref(v_a_2121_);
v___x_2127_ = lean_apply_2(v_a_2121_, v___x_2126_, lean_box(0));
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
v___jp_2132_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_inc_ref(v___y_2133_);
v___x_2137_ = lean_string_append(v___y_2133_, v___y_2136_);
v___x_2138_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2139_ = lean_string_append(v___x_2137_, v___x_2138_);
v___x_2140_ = 1;
v___x_2141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1, v___x_2140_);
lean_inc_ref(v_a_2121_);
v___x_2142_ = lean_apply_2(v_a_2121_, v___x_2141_, lean_box(0));
v___x_2143_ = l_IO_FS_writeFile(v___y_2135_, v___y_2136_);
lean_dec_ref(v___y_2135_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2130_) == 1)
{
lean_object* v_elan_x3f_2144_; 
v_elan_x3f_2144_ = lean_ctor_get(v_lakeEnv_2129_, 2);
if (lean_obj_tag(v_elan_x3f_2144_) == 1)
{
lean_object* v_val_2145_; lean_object* v_val_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_elan_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_val_2145_ = lean_ctor_get(v_lakeArgs_x3f_2130_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_lakeArgs_x3f_2130_, 1);
v_val_2146_ = lean_ctor_get(v_elan_x3f_2144_, 0);
v___x_2147_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2121_);
v___x_2148_ = lean_apply_2(v_a_2121_, v___x_2147_, lean_box(0));
v___x_2149_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2150_ = lean_ctor_get(v_val_2146_, 1);
lean_inc_ref(v_elan_2150_);
v___x_2151_ = 1;
v___x_2152_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2153_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2154_ = lean_array_push(v___x_2153_, v___y_2136_);
v___x_2155_ = lean_array_push(v___x_2154_, v___x_2152_);
v___x_2156_ = l_Array_append___redArg(v___x_2155_, v_val_2145_);
lean_dec(v_val_2145_);
v___x_2157_ = lean_box(0);
v___x_2158_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2129_);
v___x_2159_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2159_, 0, v___x_2149_);
lean_ctor_set(v___x_2159_, 1, v_elan_2150_);
lean_ctor_set(v___x_2159_, 2, v___x_2156_);
lean_ctor_set(v___x_2159_, 3, v___x_2157_);
lean_ctor_set(v___x_2159_, 4, v___x_2158_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*5, v___x_2151_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*5 + 1, v___y_2134_);
v___x_2160_ = lean_io_process_spawn(v___x_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = lean_io_process_child_wait(v___x_2149_, v_a_2161_);
lean_dec(v_a_2161_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; uint32_t v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = lean_unbox_uint32(v_a_2163_);
lean_dec(v_a_2163_);
v___x_2165_ = lean_uint32_to_uint8(v___x_2164_);
v___x_2166_ = lean_io_exit(v___x_2165_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2187_; 
v_a_2175_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2177_ = v___x_2166_;
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2166_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2179_ = lean_io_error_to_string(v_a_2175_);
v___x_2180_ = 3;
v___x_2181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set_uint8(v___x_2181_, sizeof(void*)*1, v___x_2180_);
lean_inc_ref(v_a_2121_);
v___x_2182_ = lean_apply_2(v_a_2121_, v___x_2181_, lean_box(0));
v___x_2183_ = lean_box(0);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2183_);
v___x_2185_ = v___x_2177_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2200_; 
v_a_2188_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2190_ = v___x_2162_;
v_isShared_2191_ = v_isSharedCheck_2200_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2162_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2200_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2192_ = lean_io_error_to_string(v_a_2188_);
v___x_2193_ = 3;
v___x_2194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*1, v___x_2193_);
lean_inc_ref(v_a_2121_);
v___x_2195_ = lean_apply_2(v_a_2121_, v___x_2194_, lean_box(0));
v___x_2196_ = lean_box(0);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2196_);
v___x_2198_ = v___x_2190_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2213_; 
v_a_2201_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2203_ = v___x_2160_;
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2160_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2205_ = lean_io_error_to_string(v_a_2201_);
v___x_2206_ = 3;
v___x_2207_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*1, v___x_2206_);
lean_inc_ref(v_a_2121_);
v___x_2208_ = lean_apply_2(v_a_2121_, v___x_2207_, lean_box(0));
v___x_2209_ = lean_box(0);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2209_);
v___x_2211_ = v___x_2203_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; 
lean_dec_ref_known(v_lakeArgs_x3f_2130_, 1);
lean_dec_ref(v___y_2136_);
lean_dec_ref(v_lakeEnv_2129_);
v___x_2214_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2121_);
v___x_2215_ = lean_apply_2(v_a_2121_, v___x_2214_, lean_box(0));
v___x_2216_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2217_ = lean_io_exit(v___x_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2238_; 
v_a_2226_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2228_ = v___x_2217_;
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2217_);
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
lean_inc_ref(v_a_2121_);
v___x_2233_ = lean_apply_2(v_a_2121_, v___x_2232_, lean_box(0));
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
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; 
lean_dec_ref(v___y_2136_);
lean_dec(v_lakeArgs_x3f_2130_);
lean_dec_ref(v_lakeEnv_2129_);
v___x_2239_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2121_);
v___x_2240_ = lean_apply_2(v_a_2121_, v___x_2239_, lean_box(0));
v___x_2241_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2242_ = lean_io_exit(v___x_2241_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2263_; 
v_a_2251_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2253_ = v___x_2242_;
v_isShared_2254_ = v_isSharedCheck_2263_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2242_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2263_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2255_ = lean_io_error_to_string(v_a_2251_);
v___x_2256_ = 3;
v___x_2257_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*1, v___x_2256_);
lean_inc_ref(v_a_2121_);
v___x_2258_ = lean_apply_2(v_a_2121_, v___x_2257_, lean_box(0));
v___x_2259_ = lean_box(0);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2259_);
v___x_2261_ = v___x_2253_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v___y_2136_);
lean_dec(v_lakeArgs_x3f_2130_);
lean_dec_ref(v_lakeEnv_2129_);
v_a_2264_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2266_ = v___x_2143_;
v_isShared_2267_ = v_isSharedCheck_2276_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2143_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2276_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2268_ = lean_io_error_to_string(v_a_2264_);
v___x_2269_ = 3;
v___x_2270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*1, v___x_2269_);
lean_inc_ref(v_a_2121_);
v___x_2271_ = lean_apply_2(v_a_2121_, v___x_2270_, lean_box(0));
v___x_2272_ = lean_box(0);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2272_);
v___x_2274_ = v___x_2266_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
v___jp_2277_:
{
lean_object* v___x_2281_; lean_object* v_toString_2282_; 
v___x_2281_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2282_ = lean_ctor_get(v___y_2278_, 0);
lean_inc_ref(v_toString_2282_);
lean_dec_ref(v___y_2278_);
v___y_2133_ = v___x_2281_;
v___y_2134_ = v___y_2280_;
v___y_2135_ = v___y_2279_;
v___y_2136_ = v_toString_2282_;
goto v___jp_2132_;
}
v___jp_2284_:
{
uint8_t v___x_2288_; 
v___x_2288_ = lean_nat_dec_lt(v___x_2283_, v___y_2286_);
if (v___x_2288_ == 0)
{
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
v___y_2124_ = v___y_2287_;
goto v___jp_2123_;
}
else
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_nat_dec_le(v___y_2286_, v___y_2286_);
if (v___x_2289_ == 0)
{
if (v___x_2288_ == 0)
{
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
v___y_2124_ = v___y_2287_;
goto v___jp_2123_;
}
else
{
size_t v___x_2290_; size_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = lean_usize_of_nat(v___y_2286_);
lean_dec(v___y_2286_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2285_, v___x_2290_, v___x_2291_, v___y_2287_);
lean_dec_ref(v___y_2285_);
v___y_2124_ = v___x_2292_;
goto v___jp_2123_;
}
}
else
{
size_t v___x_2293_; size_t v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = ((size_t)0ULL);
v___x_2294_ = lean_usize_of_nat(v___y_2286_);
lean_dec(v___y_2286_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2285_, v___x_2293_, v___x_2294_, v___y_2287_);
lean_dec_ref(v___y_2285_);
v___y_2124_ = v___x_2295_;
goto v___jp_2123_;
}
}
}
v___jp_2296_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
lean_inc_ref(v___y_2301_);
v___x_2304_ = lean_string_append(v___y_2301_, v___y_2303_);
lean_dec_ref(v___y_2303_);
v___x_2305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
v___x_2307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2302_, v___y_2297_);
v___x_2308_ = lean_string_append(v___x_2306_, v___x_2307_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = lean_string_append(v___x_2308_, v___y_2299_);
v___y_2285_ = v___y_2298_;
v___y_2286_ = v___y_2300_;
v___y_2287_ = v___x_2309_;
goto v___jp_2284_;
}
v___jp_2310_:
{
lean_object* v___x_2317_; lean_object* v_toString_2318_; 
v___x_2317_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2318_ = lean_ctor_get(v___y_2311_, 0);
lean_inc_ref(v_toString_2318_);
lean_dec_ref(v___y_2311_);
v___y_2297_ = v___y_2312_;
v___y_2298_ = v___y_2313_;
v___y_2299_ = v___y_2316_;
v___y_2300_ = v___y_2314_;
v___y_2301_ = v___x_2317_;
v___y_2302_ = v___y_2315_;
v___y_2303_ = v_toString_2318_;
goto v___jp_2296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2398_, lean_object* v_rootDeps_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2398_, v_rootDeps_2399_, v_a_2400_);
lean_dec_ref(v_a_2400_);
lean_dec_ref(v_rootDeps_2399_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2403_, lean_object* v_dep_2404_, lean_object* v_ws_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2405_, v_pkg_2403_, v_dep_2404_, v_a_2406_, v_a_2407_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v___x_2413_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v_fst_2411_ = lean_ctor_get(v_a_2410_, 0);
lean_inc_n(v_fst_2411_, 2);
v_snd_2412_ = lean_ctor_get(v_a_2410_, 1);
lean_inc(v_snd_2412_);
lean_dec(v_a_2410_);
v___x_2413_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2411_, v_snd_2412_, v_a_2407_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2430_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2430_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2430_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_snd_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2428_; 
v_snd_2418_ = lean_ctor_get(v_a_2414_, 1);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_a_2414_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; 
v_unused_2429_ = lean_ctor_get(v_a_2414_, 0);
lean_dec(v_unused_2429_);
v___x_2420_ = v_a_2414_;
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_snd_2418_);
lean_dec(v_a_2414_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v_fst_2411_);
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_fst_2411_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_snd_2418_);
v___x_2423_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2425_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2423_);
v___x_2425_ = v___x_2416_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_fst_2411_);
v_a_2431_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2413_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2413_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2439_, lean_object* v_dep_2440_, lean_object* v_ws_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2439_, v_dep_2440_, v_ws_2441_, v_a_2442_, v_a_2443_);
lean_dec_ref(v_a_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2446_, lean_object* v_ws_2447_, lean_object* v_pkg_2448_, lean_object* v_dep_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_name_2452_; lean_object* v___x_2453_; 
v_name_2452_ = lean_ctor_get(v_dep_2449_, 0);
v___x_2453_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2450_, v_name_2452_);
if (lean_obj_tag(v___x_2453_) == 1)
{
lean_object* v_val_2454_; lean_object* v_lakeEnv_2455_; lean_object* v_packages_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_config_2459_; lean_object* v_dir_2460_; lean_object* v_toWorkspaceConfig_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec_ref(v_dep_2449_);
lean_dec_ref(v_pkg_2448_);
v_val_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_val_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v_lakeEnv_2455_ = lean_ctor_get(v_ws_2447_, 0);
lean_inc_ref(v_lakeEnv_2455_);
v_packages_2456_ = lean_ctor_get(v_ws_2447_, 4);
lean_inc_ref(v_packages_2456_);
lean_dec_ref(v_ws_2447_);
v___x_2457_ = lean_unsigned_to_nat(0u);
v___x_2458_ = lean_array_fget(v_packages_2456_, v___x_2457_);
lean_dec_ref(v_packages_2456_);
v_config_2459_ = lean_ctor_get(v___x_2458_, 6);
lean_inc_ref(v_config_2459_);
v_dir_2460_ = lean_ctor_get(v___x_2458_, 4);
lean_inc_ref(v_dir_2460_);
lean_dec(v___x_2458_);
v_toWorkspaceConfig_2461_ = lean_ctor_get(v_config_2459_, 0);
lean_inc_ref(v_toWorkspaceConfig_2461_);
lean_dec_ref(v_config_2459_);
v___x_2462_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2461_);
v___x_2463_ = l_Lake_PackageEntry_materialize(v_val_2454_, v_lakeEnv_2455_, v_dir_2460_, v___x_2462_, v___y_2446_);
lean_dec_ref(v_lakeEnv_2455_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2472_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_a_2464_);
lean_ctor_set(v___x_2468_, 1, v_a_2450_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2468_);
v___x_2470_ = v___x_2466_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_a_2450_);
v_a_2473_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2463_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2463_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
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
lean_object* v_wsIdx_2481_; lean_object* v_relDir_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; uint8_t v___x_2485_; lean_object* v___y_2487_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
lean_dec(v___x_2453_);
v_wsIdx_2481_ = lean_ctor_get(v_pkg_2448_, 0);
lean_inc(v_wsIdx_2481_);
v_relDir_2482_ = lean_ctor_get(v_pkg_2448_, 5);
lean_inc_ref(v_relDir_2482_);
lean_dec_ref(v_pkg_2448_);
v___x_2483_ = lean_unsigned_to_nat(0u);
v___x_2484_ = lean_nat_dec_eq(v_wsIdx_2481_, v___x_2483_);
lean_dec(v_wsIdx_2481_);
v___x_2485_ = lean_bool_not(v___x_2484_);
v___x_2516_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2517_ = lean_string_dec_eq(v_relDir_2482_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lake_joinRelative(v_relDir_2482_, v___x_2516_);
v___y_2487_ = v___x_2518_;
goto v___jp_2486_;
}
else
{
v___y_2487_ = v_relDir_2482_;
goto v___jp_2486_;
}
v___jp_2486_:
{
lean_object* v_lakeEnv_2488_; lean_object* v_packages_2489_; lean_object* v___x_2490_; lean_object* v_config_2491_; lean_object* v_dir_2492_; lean_object* v_toWorkspaceConfig_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v_lakeEnv_2488_ = lean_ctor_get(v_ws_2447_, 0);
lean_inc_ref(v_lakeEnv_2488_);
v_packages_2489_ = lean_ctor_get(v_ws_2447_, 4);
lean_inc_ref(v_packages_2489_);
lean_dec_ref(v_ws_2447_);
v___x_2490_ = lean_array_fget(v_packages_2489_, v___x_2483_);
lean_dec_ref(v_packages_2489_);
v_config_2491_ = lean_ctor_get(v___x_2490_, 6);
lean_inc_ref(v_config_2491_);
v_dir_2492_ = lean_ctor_get(v___x_2490_, 4);
lean_inc_ref(v_dir_2492_);
lean_dec(v___x_2490_);
v_toWorkspaceConfig_2493_ = lean_ctor_get(v_config_2491_, 0);
lean_inc_ref(v_toWorkspaceConfig_2493_);
lean_dec_ref(v_config_2491_);
v___x_2494_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2493_);
v___x_2495_ = l_Lake_Dependency_materialize(v_dep_2449_, v___x_2485_, v_lakeEnv_2488_, v_dir_2492_, v___x_2494_, v___y_2487_, v___y_2446_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2507_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2507_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2507_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_manifestEntry_2500_; lean_object* v_name_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v_manifestEntry_2500_ = lean_ctor_get(v_a_2496_, 4);
v_name_2501_ = lean_ctor_get(v_manifestEntry_2500_, 0);
lean_inc_ref(v_manifestEntry_2500_);
lean_inc(v_name_2501_);
v___x_2502_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2501_, v_manifestEntry_2500_, v_a_2450_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2496_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2503_);
v___x_2505_ = v___x_2498_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_a_2450_);
v_a_2508_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2495_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2495_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2519_, lean_object* v_ws_2520_, lean_object* v_pkg_2521_, lean_object* v_dep_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2519_, v_ws_2520_, v_pkg_2521_, v_dep_2522_, v_a_2523_);
lean_dec_ref(v___y_2519_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2526_, lean_object* v_dep_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_manifestEntry_2530_; lean_object* v_pkgDir_2531_; lean_object* v_name_2532_; lean_object* v_manifestFile_x3f_2533_; lean_object* v___y_2535_; lean_object* v_fst_2536_; lean_object* v_snd_2537_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v_val_2597_; lean_object* v___y_2625_; 
v_manifestEntry_2530_ = lean_ctor_get(v_dep_2527_, 4);
v_pkgDir_2531_ = lean_ctor_get(v_dep_2527_, 0);
v_name_2532_ = lean_ctor_get(v_manifestEntry_2530_, 0);
v_manifestFile_x3f_2533_ = lean_ctor_get(v_manifestEntry_2530_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2533_) == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2531_);
v___x_2646_ = l_Lake_joinRelative(v_pkgDir_2531_, v___x_2645_);
v___y_2625_ = v___x_2646_;
goto v___jp_2624_;
}
else
{
lean_object* v_val_2647_; lean_object* v___x_2648_; 
v_val_2647_ = lean_ctor_get(v_manifestFile_x3f_2533_, 0);
lean_inc(v_val_2647_);
lean_inc_ref(v_pkgDir_2531_);
v___x_2648_ = l_Lake_joinRelative(v_pkgDir_2531_, v_val_2647_);
v___y_2625_ = v___x_2648_;
goto v___jp_2624_;
}
v___jp_2534_:
{
if (lean_obj_tag(v_fst_2536_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2567_; 
lean_inc(v_name_2532_);
lean_dec_ref(v_dep_2527_);
v_a_2538_ = lean_ctor_get(v_fst_2536_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_fst_2536_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2540_ = v_fst_2536_;
v_isShared_2541_ = v_isSharedCheck_2567_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v_fst_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2567_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
if (lean_obj_tag(v_a_2538_) == 11)
{
uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_dec_ref_known(v_a_2538_, 2);
v___x_2542_ = 0;
v___x_2543_ = l_Lean_Name_toString(v_name_2532_, v___x_2542_);
v___x_2544_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
v___x_2546_ = lean_string_append(v___x_2545_, v___y_2535_);
lean_dec_ref(v___y_2535_);
v___x_2547_ = 2;
v___x_2548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*1, v___x_2547_);
v___x_2549_ = lean_apply_2(v___y_2526_, v___x_2548_, lean_box(0));
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v_snd_2537_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2550_);
v___x_2552_ = v___x_2540_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
else
{
uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_dec_ref(v___y_2535_);
v___x_2554_ = 0;
v___x_2555_ = l_Lean_Name_toString(v_name_2532_, v___x_2554_);
v___x_2556_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2557_ = lean_string_append(v___x_2555_, v___x_2556_);
v___x_2558_ = lean_io_error_to_string(v_a_2538_);
v___x_2559_ = lean_string_append(v___x_2557_, v___x_2558_);
lean_dec_ref(v___x_2558_);
v___x_2560_ = 2;
v___x_2561_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set_uint8(v___x_2561_, sizeof(void*)*1, v___x_2560_);
v___x_2562_ = lean_apply_2(v___y_2526_, v___x_2561_, lean_box(0));
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v_snd_2537_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2563_);
v___x_2565_ = v___x_2540_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
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
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2526_);
v_a_2568_ = lean_ctor_get(v_fst_2536_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_fst_2536_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2570_ = v_fst_2536_;
v_isShared_2571_ = v_isSharedCheck_2592_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v_fst_2536_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2592_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_packages_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_packages_2572_ = lean_ctor_get(v_a_2568_, 3);
lean_inc_ref(v_packages_2572_);
lean_dec(v_a_2568_);
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = lean_array_get_size(v_packages_2572_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_nat_dec_lt(v___x_2573_, v___x_2574_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec_ref(v_packages_2572_);
lean_dec_ref(v_dep_2527_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v_snd_2537_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2577_);
v___x_2579_ = v___x_2570_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
else
{
uint8_t v___x_2581_; 
v___x_2581_ = lean_nat_dec_le(v___x_2574_, v___x_2574_);
if (v___x_2581_ == 0)
{
if (v___x_2576_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
lean_dec_ref(v_packages_2572_);
lean_dec_ref(v_dep_2527_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2575_);
lean_ctor_set(v___x_2582_, 1, v_snd_2537_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2582_);
v___x_2584_ = v___x_2570_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
else
{
size_t v___x_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
lean_del_object(v___x_2570_);
v___x_2586_ = ((size_t)0ULL);
v___x_2587_ = lean_usize_of_nat(v___x_2574_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2527_, v_packages_2572_, v___x_2586_, v___x_2587_, v___x_2575_, v_snd_2537_);
lean_dec_ref(v_packages_2572_);
return v___x_2588_;
}
}
else
{
size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
lean_del_object(v___x_2570_);
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = lean_usize_of_nat(v___x_2574_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2527_, v_packages_2572_, v___x_2589_, v___x_2590_, v___x_2575_, v_snd_2537_);
lean_dec_ref(v_packages_2572_);
return v___x_2591_;
}
}
}
}
}
v___jp_2593_:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_array_get_size(v___y_2596_);
v___x_2599_ = lean_nat_dec_lt(v___y_2595_, v___x_2598_);
if (v___x_2599_ == 0)
{
v___y_2535_ = v___y_2594_;
v_fst_2536_ = v_val_2597_;
v_snd_2537_ = v_a_2528_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_nat_dec_le(v___x_2598_, v___x_2598_);
if (v___x_2601_ == 0)
{
if (v___x_2599_ == 0)
{
v___y_2535_ = v___y_2594_;
v_fst_2536_ = v_val_2597_;
v_snd_2537_ = v_a_2528_;
goto v___jp_2534_;
}
else
{
size_t v___x_2602_; size_t v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = ((size_t)0ULL);
v___x_2603_ = lean_usize_of_nat(v___x_2598_);
v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2596_, v___x_2602_, v___x_2603_, v___x_2600_, v___y_2526_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_dec_ref_known(v___x_2604_, 1);
v___y_2535_ = v___y_2594_;
v_fst_2536_ = v_val_2597_;
v_snd_2537_ = v_a_2528_;
goto v___jp_2534_;
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_val_2597_);
lean_dec_ref(v___y_2594_);
lean_dec(v_a_2528_);
lean_dec_ref(v_dep_2527_);
lean_dec_ref(v___y_2526_);
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
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
else
{
size_t v___x_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = ((size_t)0ULL);
v___x_2614_ = lean_usize_of_nat(v___x_2598_);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2596_, v___x_2613_, v___x_2614_, v___x_2600_, v___y_2526_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_dec_ref_known(v___x_2615_, 1);
v___y_2535_ = v___y_2594_;
v_fst_2536_ = v_val_2597_;
v_snd_2537_ = v_a_2528_;
goto v___jp_2534_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_val_2597_);
lean_dec_ref(v___y_2594_);
lean_dec(v_a_2528_);
lean_dec_ref(v_dep_2527_);
lean_dec_ref(v___y_2526_);
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
}
v___jp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2625_);
v___x_2628_ = l_Lake_Manifest_load(v___y_2625_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set_tag(v___x_2631_, 1);
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
v___y_2594_ = v___y_2625_;
v___y_2595_ = v___x_2626_;
v___y_2596_ = v___x_2627_;
v_val_2597_ = v___x_2634_;
goto v___jp_2593_;
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_a_2637_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2628_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2628_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set_tag(v___x_2639_, 0);
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
v___y_2594_ = v___y_2625_;
v___y_2595_ = v___x_2626_;
v___y_2596_ = v___x_2627_;
v_val_2597_ = v___x_2642_;
goto v___jp_2593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2649_, lean_object* v_dep_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2649_, v_dep_2650_, v_a_2651_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2658_, v___y_2656_, v___y_2654_, v___y_2655_, v___y_2657_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v_fst_2662_; lean_object* v_snd_2663_; lean_object* v___x_2664_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
v_fst_2662_ = lean_ctor_get(v_a_2661_, 0);
lean_inc_n(v_fst_2662_, 2);
v_snd_2663_ = lean_ctor_get(v_a_2661_, 1);
lean_inc(v_snd_2663_);
lean_dec(v_a_2661_);
v___x_2664_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2658_, v_fst_2662_, v_snd_2663_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2681_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2681_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2681_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_snd_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2679_; 
v_snd_2669_ = lean_ctor_get(v_a_2665_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_a_2665_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v_a_2665_, 0);
lean_dec(v_unused_2680_);
v___x_2671_ = v_a_2665_;
v_isShared_2672_ = v_isSharedCheck_2679_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_snd_2669_);
lean_dec(v_a_2665_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2679_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v_fst_2662_);
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_fst_2662_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_snd_2669_);
v___x_2674_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2674_);
v___x_2676_ = v___x_2667_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_fst_2662_);
v_a_2682_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2664_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2664_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
else
{
lean_dec_ref(v___y_2658_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2697_, lean_object* v_ws_2698_, lean_object* v_toUpdate_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___y_2703_; lean_object* v_fst_2704_; lean_object* v_snd_2705_; lean_object* v_packages_2724_; lean_object* v___x_2725_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v_val_2730_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___x_2778_; lean_object* v_baseName_2779_; lean_object* v_dir_2780_; lean_object* v_config_2781_; lean_object* v_relManifestFile_2782_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; uint8_t v___y_2787_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; uint8_t v_fst_2811_; lean_object* v_snd_2812_; lean_object* v_packagesDir_x3f_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2861_; lean_object* v___y_2862_; uint8_t v___x_2865_; lean_object* v_rootName_2866_; lean_object* v_fst_2868_; lean_object* v_snd_2869_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_val_2920_; lean_object* v___x_2946_; 
v_packages_2724_ = lean_ctor_get(v_ws_2698_, 4);
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2778_ = lean_array_fget_borrowed(v_packages_2724_, v___x_2725_);
v_baseName_2779_ = lean_ctor_get(v___x_2778_, 1);
v_dir_2780_ = lean_ctor_get(v___x_2778_, 4);
v_config_2781_ = lean_ctor_get(v___x_2778_, 6);
v_relManifestFile_2782_ = lean_ctor_get(v___x_2778_, 9);
v___x_2865_ = 0;
lean_inc(v_baseName_2779_);
v_rootName_2866_ = l_Lean_Name_toString(v_baseName_2779_, v___x_2865_);
lean_inc_ref(v_relManifestFile_2782_);
lean_inc_ref(v_dir_2780_);
v___x_2917_ = l_Lake_joinRelative(v_dir_2780_, v_relManifestFile_2782_);
v___x_2918_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2946_ = l_Lake_Manifest_load(v___x_2917_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 1);
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
v_val_2920_ = v___x_2952_;
goto v___jp_2919_;
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
v_a_2955_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2946_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2946_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 0);
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
v_val_2920_ = v___x_2960_;
goto v___jp_2919_;
}
}
}
v___jp_2702_:
{
if (lean_obj_tag(v_fst_2704_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_snd_2705_);
v_a_2706_ = lean_ctor_get(v_fst_2704_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_fst_2704_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2708_ = v_fst_2704_;
v_isShared_2709_ = v_isSharedCheck_2720_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v_fst_2704_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2720_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2710_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2711_ = lean_io_error_to_string(v_a_2706_);
v___x_2712_ = lean_string_append(v___x_2710_, v___x_2711_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = 3;
v___x_2714_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set_uint8(v___x_2714_, sizeof(void*)*1, v___x_2713_);
lean_inc_ref(v___y_2703_);
v___x_2715_ = lean_apply_2(v___y_2703_, v___x_2714_, lean_box(0));
v___x_2716_ = lean_box(0);
if (v_isShared_2709_ == 0)
{
lean_ctor_set_tag(v___x_2708_, 1);
lean_ctor_set(v___x_2708_, 0, v___x_2716_);
v___x_2718_ = v___x_2708_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec_ref(v_fst_2704_);
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_snd_2705_);
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
return v___x_2723_;
}
}
v___jp_2726_:
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_array_get_size(v___y_2729_);
v___x_2732_ = lean_nat_dec_lt(v___x_2725_, v___x_2731_);
if (v___x_2732_ == 0)
{
v___y_2703_ = v___y_2727_;
v_fst_2704_ = v_val_2730_;
v_snd_2705_ = v___y_2728_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = lean_box(0);
v___x_2734_ = lean_nat_dec_le(v___x_2731_, v___x_2731_);
if (v___x_2734_ == 0)
{
if (v___x_2732_ == 0)
{
v___y_2703_ = v___y_2727_;
v_fst_2704_ = v_val_2730_;
v_snd_2705_ = v___y_2728_;
goto v___jp_2702_;
}
else
{
size_t v___x_2735_; size_t v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = ((size_t)0ULL);
v___x_2736_ = lean_usize_of_nat(v___x_2731_);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2729_, v___x_2735_, v___x_2736_, v___x_2733_, v___y_2727_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_dec_ref_known(v___x_2737_, 1);
v___y_2703_ = v___y_2727_;
v_fst_2704_ = v_val_2730_;
v_snd_2705_ = v___y_2728_;
goto v___jp_2702_;
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v_val_2730_);
lean_dec(v___y_2728_);
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
else
{
size_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = lean_usize_of_nat(v___x_2731_);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2729_, v___x_2746_, v___x_2747_, v___x_2733_, v___y_2727_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_dec_ref_known(v___x_2748_, 1);
v___y_2703_ = v___y_2727_;
v_fst_2704_ = v_val_2730_;
v_snd_2705_ = v___y_2728_;
goto v___jp_2702_;
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v_val_2730_);
lean_dec(v___y_2728_);
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
}
v___jp_2757_:
{
if (lean_obj_tag(v___y_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_a_2762_ = lean_ctor_get(v___y_2761_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___y_2761_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___y_2761_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___y_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 1);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
v___y_2727_ = v___y_2758_;
v___y_2728_ = v___y_2759_;
v___y_2729_ = v___y_2760_;
v_val_2730_ = v___x_2767_;
goto v___jp_2726_;
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v_a_2770_ = lean_ctor_get(v___y_2761_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___y_2761_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___y_2761_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___y_2761_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 0);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
v___y_2727_ = v___y_2758_;
v___y_2728_ = v___y_2759_;
v___y_2729_ = v___y_2760_;
v_val_2730_ = v___x_2775_;
goto v___jp_2726_;
}
}
}
}
v___jp_2783_:
{
if (v___y_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec_ref(v___y_2786_);
v___x_2788_ = lean_box(0);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___y_2785_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
else
{
lean_object* v_toWorkspaceConfig_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_toWorkspaceConfig_2791_ = lean_ctor_get(v_config_2781_, 0);
v___x_2792_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2793_ = lean_string_append(v___x_2792_, v___y_2786_);
v___x_2794_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2795_ = lean_string_append(v___x_2793_, v___x_2794_);
lean_inc_ref(v_toWorkspaceConfig_2791_);
v___x_2796_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2791_);
lean_inc_ref(v_dir_2780_);
v___x_2797_ = l_Lake_joinRelative(v_dir_2780_, v___x_2796_);
v___x_2798_ = lean_string_append(v___x_2795_, v___x_2797_);
v___x_2799_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2800_ = lean_string_append(v___x_2798_, v___x_2799_);
v___x_2801_ = 1;
v___x_2802_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*1, v___x_2801_);
lean_inc_ref(v___y_2784_);
v___x_2803_ = lean_apply_2(v___y_2784_, v___x_2802_, lean_box(0));
v___x_2804_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2797_);
v___x_2805_ = l_Lake_createParentDirs(v___x_2797_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v___x_2806_; 
lean_dec_ref_known(v___x_2805_, 1);
v___x_2806_ = lean_io_rename(v___y_2786_, v___x_2797_);
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___y_2786_);
v___y_2758_ = v___y_2784_;
v___y_2759_ = v___y_2785_;
v___y_2760_ = v___x_2804_;
v___y_2761_ = v___x_2806_;
goto v___jp_2757_;
}
else
{
lean_dec_ref(v___x_2797_);
lean_dec_ref(v___y_2786_);
v___y_2758_ = v___y_2784_;
v___y_2759_ = v___y_2785_;
v___y_2760_ = v___x_2804_;
v___y_2761_ = v___x_2805_;
goto v___jp_2757_;
}
}
}
v___jp_2807_:
{
lean_object* v_toWorkspaceConfig_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; uint8_t v___x_2818_; 
v_toWorkspaceConfig_2813_ = lean_ctor_get(v_config_2781_, 0);
v___x_2814_ = l_System_FilePath_normalize(v___y_2810_);
lean_inc_ref(v_toWorkspaceConfig_2813_);
v___x_2815_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2813_);
v___x_2816_ = l_System_FilePath_normalize(v___x_2815_);
v___x_2817_ = lean_string_dec_eq(v___x_2814_, v___x_2816_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v___x_2814_);
v___x_2818_ = lean_bool_not(v___x_2817_);
if (v___x_2818_ == 0)
{
v___y_2784_ = v___y_2808_;
v___y_2785_ = v_snd_2812_;
v___y_2786_ = v___y_2809_;
v___y_2787_ = v___x_2818_;
goto v___jp_2783_;
}
else
{
v___y_2784_ = v___y_2808_;
v___y_2785_ = v_snd_2812_;
v___y_2786_ = v___y_2809_;
v___y_2787_ = v_fst_2811_;
goto v___jp_2783_;
}
}
v___jp_2819_:
{
if (lean_obj_tag(v_packagesDir_x3f_2820_) == 1)
{
lean_object* v_val_2823_; lean_object* v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_val_2823_ = lean_ctor_get(v_packagesDir_x3f_2820_, 0);
lean_inc_n(v_val_2823_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2820_, 1);
lean_inc_ref(v_dir_2780_);
v___x_2824_ = l_Lake_joinRelative(v_dir_2780_, v_val_2823_);
v___x_2825_ = l_System_FilePath_pathExists(v___x_2824_);
v___x_2826_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2827_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2827_ == 0)
{
v___y_2808_ = v___y_2822_;
v___y_2809_ = v___x_2824_;
v___y_2810_ = v_val_2823_;
v_fst_2811_ = v___x_2825_;
v_snd_2812_ = v___y_2821_;
goto v___jp_2807_;
}
else
{
lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2829_ == 0)
{
if (v___x_2827_ == 0)
{
v___y_2808_ = v___y_2822_;
v___y_2809_ = v___x_2824_;
v___y_2810_ = v_val_2823_;
v_fst_2811_ = v___x_2825_;
v_snd_2812_ = v___y_2821_;
goto v___jp_2807_;
}
else
{
size_t v___x_2830_; size_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = ((size_t)0ULL);
v___x_2831_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2826_, v___x_2830_, v___x_2831_, v___x_2828_, v___y_2822_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_dec_ref_known(v___x_2832_, 1);
v___y_2808_ = v___y_2822_;
v___y_2809_ = v___x_2824_;
v___y_2810_ = v_val_2823_;
v_fst_2811_ = v___x_2825_;
v_snd_2812_ = v___y_2821_;
goto v___jp_2807_;
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec_ref(v___x_2824_);
lean_dec(v_val_2823_);
lean_dec(v___y_2821_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
else
{
size_t v___x_2841_; size_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2841_ = ((size_t)0ULL);
v___x_2842_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2826_, v___x_2841_, v___x_2842_, v___x_2828_, v___y_2822_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_dec_ref_known(v___x_2843_, 1);
v___y_2808_ = v___y_2822_;
v___y_2809_ = v___x_2824_;
v___y_2810_ = v_val_2823_;
v_fst_2811_ = v___x_2825_;
v_snd_2812_ = v___y_2821_;
goto v___jp_2807_;
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref(v___x_2824_);
lean_dec(v_val_2823_);
lean_dec(v___y_2821_);
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec(v_packagesDir_x3f_2820_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___y_2821_);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
return v___x_2854_;
}
}
v___jp_2855_:
{
lean_object* v_packagesDir_x3f_2859_; 
v_packagesDir_x3f_2859_ = lean_ctor_get(v___y_2856_, 2);
lean_inc(v_packagesDir_x3f_2859_);
lean_dec_ref(v___y_2856_);
v_packagesDir_x3f_2820_ = v_packagesDir_x3f_2859_;
v___y_2821_ = v___y_2857_;
v___y_2822_ = v___y_2858_;
goto v___jp_2819_;
}
v___jp_2860_:
{
if (lean_obj_tag(v___y_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v_snd_2864_; 
v_a_2863_ = lean_ctor_get(v___y_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___y_2862_, 1);
v_snd_2864_ = lean_ctor_get(v_a_2863_, 1);
lean_inc(v_snd_2864_);
lean_dec(v_a_2863_);
v___y_2856_ = v___y_2861_;
v___y_2857_ = v_snd_2864_;
v___y_2858_ = v_a_2697_;
goto v___jp_2855_;
}
else
{
lean_dec_ref(v___y_2861_);
return v___y_2862_;
}
}
v___jp_2867_:
{
if (lean_obj_tag(v_fst_2868_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2902_; 
v_a_2870_ = lean_ctor_get(v_fst_2868_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_fst_2868_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2872_ = v_fst_2868_;
v_isShared_2873_ = v_isSharedCheck_2902_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v_fst_2868_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2902_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
if (lean_obj_tag(v_a_2870_) == 11)
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_dec_ref_known(v_a_2870_, 2);
v___x_2874_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2875_ = lean_string_append(v_rootName_2866_, v___x_2874_);
v___x_2876_ = 1;
v___x_2877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set_uint8(v___x_2877_, sizeof(void*)*1, v___x_2876_);
lean_inc_ref(v_a_2697_);
v___x_2878_ = lean_apply_2(v_a_2697_, v___x_2877_, lean_box(0));
v___x_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v_snd_2869_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2879_);
v___x_2881_ = v___x_2872_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2699_) == 0)
{
lean_object* v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
lean_dec(v_snd_2869_);
lean_dec_ref(v_rootName_2866_);
v___x_2883_ = lean_io_error_to_string(v_a_2870_);
v___x_2884_ = 3;
v___x_2885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*1, v___x_2884_);
lean_inc_ref(v_a_2697_);
v___x_2886_ = lean_apply_2(v_a_2697_, v___x_2885_, lean_box(0));
v___x_2887_ = lean_box(0);
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 1);
lean_ctor_set(v___x_2872_, 0, v___x_2887_);
v___x_2889_ = v___x_2872_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2891_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_2892_ = lean_string_append(v_rootName_2866_, v___x_2891_);
v___x_2893_ = lean_io_error_to_string(v_a_2870_);
v___x_2894_ = lean_string_append(v___x_2892_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = 2;
v___x_2896_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*1, v___x_2895_);
lean_inc_ref(v_a_2697_);
v___x_2897_ = lean_apply_2(v_a_2697_, v___x_2896_, lean_box(0));
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v_snd_2869_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2898_);
v___x_2900_ = v___x_2872_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_2866_);
if (lean_obj_tag(v_toUpdate_2699_) == 0)
{
lean_object* v_a_2903_; lean_object* v_packagesDir_x3f_2904_; lean_object* v_packages_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_a_2903_ = lean_ctor_get(v_fst_2868_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v_fst_2868_, 1);
v_packagesDir_x3f_2904_ = lean_ctor_get(v_a_2903_, 2);
v_packages_2905_ = lean_ctor_get(v_a_2903_, 3);
v___x_2906_ = lean_array_get_size(v_packages_2905_);
v___x_2907_ = lean_nat_dec_lt(v___x_2725_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_inc(v_packagesDir_x3f_2904_);
lean_dec(v_a_2903_);
v_packagesDir_x3f_2820_ = v_packagesDir_x3f_2904_;
v___y_2821_ = v_snd_2869_;
v___y_2822_ = v_a_2697_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_nat_dec_le(v___x_2906_, v___x_2906_);
if (v___x_2909_ == 0)
{
if (v___x_2907_ == 0)
{
lean_inc(v_packagesDir_x3f_2904_);
lean_dec(v_a_2903_);
v_packagesDir_x3f_2820_ = v_packagesDir_x3f_2904_;
v___y_2821_ = v_snd_2869_;
v___y_2822_ = v_a_2697_;
goto v___jp_2819_;
}
else
{
size_t v___x_2910_; size_t v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = ((size_t)0ULL);
v___x_2911_ = lean_usize_of_nat(v___x_2906_);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2699_, v_packages_2905_, v___x_2910_, v___x_2911_, v___x_2908_, v_snd_2869_);
v___y_2861_ = v_a_2903_;
v___y_2862_ = v___x_2912_;
goto v___jp_2860_;
}
}
else
{
size_t v___x_2913_; size_t v___x_2914_; lean_object* v___x_2915_; 
v___x_2913_ = ((size_t)0ULL);
v___x_2914_ = lean_usize_of_nat(v___x_2906_);
v___x_2915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2699_, v_packages_2905_, v___x_2913_, v___x_2914_, v___x_2908_, v_snd_2869_);
v___y_2861_ = v_a_2903_;
v___y_2862_ = v___x_2915_;
goto v___jp_2860_;
}
}
}
else
{
lean_object* v_a_2916_; 
v_a_2916_ = lean_ctor_get(v_fst_2868_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v_fst_2868_, 1);
v___y_2856_ = v_a_2916_;
v___y_2857_ = v_snd_2869_;
v___y_2858_ = v_a_2697_;
goto v___jp_2855_;
}
}
}
v___jp_2919_:
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2921_ == 0)
{
v_fst_2868_ = v_val_2920_;
v_snd_2869_ = v_a_2700_;
goto v___jp_2867_;
}
else
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = lean_box(0);
v___x_2923_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2923_ == 0)
{
if (v___x_2921_ == 0)
{
v_fst_2868_ = v_val_2920_;
v_snd_2869_ = v_a_2700_;
goto v___jp_2867_;
}
else
{
size_t v___x_2924_; size_t v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2918_, v___x_2924_, v___x_2925_, v___x_2922_, v_a_2697_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_dec_ref_known(v___x_2926_, 1);
v_fst_2868_ = v_val_2920_;
v_snd_2869_ = v_a_2700_;
goto v___jp_2867_;
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v_val_2920_);
lean_dec_ref(v_rootName_2866_);
lean_dec(v_a_2700_);
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
else
{
size_t v___x_2935_; size_t v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = ((size_t)0ULL);
v___x_2936_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2918_, v___x_2935_, v___x_2936_, v___x_2922_, v_a_2697_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_dec_ref_known(v___x_2937_, 1);
v_fst_2868_ = v_val_2920_;
v_snd_2869_ = v_a_2700_;
goto v___jp_2867_;
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v_val_2920_);
lean_dec_ref(v_rootName_2866_);
lean_dec(v_a_2700_);
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2937_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_2963_, lean_object* v_ws_2964_, lean_object* v_toUpdate_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_2963_, v_ws_2964_, v_toUpdate_2965_, v_a_2966_);
lean_dec(v_toUpdate_2965_);
lean_dec_ref(v_ws_2964_);
lean_dec_ref(v_a_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_2969_, lean_object* v_ws_2970_, lean_object* v_rootDeps_2971_){
_start:
{
lean_object* v___y_2974_; lean_object* v_lakeEnv_2979_; lean_object* v_lakeArgs_x3f_2980_; lean_object* v_packages_2981_; uint8_t v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3132_; lean_object* v___x_3135_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; uint8_t v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; uint8_t v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___x_3171_; lean_object* v_baseName_3172_; lean_object* v_dir_3173_; lean_object* v_config_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_lakeEnv_2979_ = lean_ctor_get(v_ws_2970_, 0);
lean_inc_ref(v_lakeEnv_2979_);
v_lakeArgs_x3f_2980_ = lean_ctor_get(v_ws_2970_, 3);
lean_inc(v_lakeArgs_x3f_2980_);
v_packages_2981_ = lean_ctor_get(v_ws_2970_, 4);
lean_inc_ref(v_packages_2981_);
lean_dec_ref(v_ws_2970_);
v___x_3135_ = lean_unsigned_to_nat(0u);
v___x_3171_ = lean_array_fget(v_packages_2981_, v___x_3135_);
lean_dec_ref(v_packages_2981_);
v_baseName_3172_ = lean_ctor_get(v___x_3171_, 1);
lean_inc(v_baseName_3172_);
v_dir_3173_ = lean_ctor_get(v___x_3171_, 4);
lean_inc_ref_n(v_dir_3173_, 2);
v_config_3174_ = lean_ctor_get(v___x_3171_, 6);
lean_inc_ref(v_config_3174_);
lean_dec(v___x_3171_);
v___x_3175_ = l_Lake_toolchainFileName;
v___x_3176_ = l_System_FilePath_join(v_dir_3173_, v___x_3175_);
v___x_3177_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3176_);
lean_dec_ref(v___x_3176_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3236_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3236_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3236_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_src_3183_; lean_object* v_tc_x3f_3184_; lean_object* v_clashes_3185_; uint8_t v_fixed_3186_; lean_object* v___y_3210_; uint8_t v_fixedToolchain_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; 
v_fixedToolchain_3224_ = lean_ctor_get_uint8(v_config_3174_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_3174_);
v___x_3225_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3226_ = lean_array_get_size(v_rootDeps_2971_);
v___x_3227_ = lean_nat_dec_lt(v___x_3135_, v___x_3226_);
if (v___x_3227_ == 0)
{
lean_inc(v_a_3178_);
v_src_3183_ = v_baseName_3172_;
v_tc_x3f_3184_ = v_a_3178_;
v_clashes_3185_ = v___x_3225_;
v_fixed_3186_ = v_fixedToolchain_3224_;
goto v___jp_3182_;
}
else
{
lean_object* v___x_3228_; uint8_t v___x_3229_; 
lean_inc(v_a_3178_);
lean_inc(v_baseName_3172_);
v___x_3228_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3228_, 0, v_baseName_3172_);
lean_ctor_set(v___x_3228_, 1, v_a_3178_);
lean_ctor_set(v___x_3228_, 2, v___x_3225_);
lean_ctor_set_uint8(v___x_3228_, sizeof(void*)*3, v_fixedToolchain_3224_);
v___x_3229_ = lean_nat_dec_le(v___x_3226_, v___x_3226_);
if (v___x_3229_ == 0)
{
if (v___x_3227_ == 0)
{
lean_dec_ref_known(v___x_3228_, 3);
lean_inc(v_a_3178_);
v_src_3183_ = v_baseName_3172_;
v_tc_x3f_3184_ = v_a_3178_;
v_clashes_3185_ = v___x_3225_;
v_fixed_3186_ = v_fixedToolchain_3224_;
goto v___jp_3182_;
}
else
{
size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v_baseName_3172_);
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = lean_usize_of_nat(v___x_3226_);
lean_inc_ref(v_dir_3173_);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3173_, v_rootDeps_2971_, v___x_3230_, v___x_3231_, v___x_3228_, v_a_2969_);
v___y_3210_ = v___x_3232_;
goto v___jp_3209_;
}
}
else
{
size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
lean_dec(v_baseName_3172_);
v___x_3233_ = ((size_t)0ULL);
v___x_3234_ = lean_usize_of_nat(v___x_3226_);
lean_inc_ref(v_dir_3173_);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3173_, v_rootDeps_2971_, v___x_3233_, v___x_3234_, v___x_3228_, v_a_2969_);
v___y_3210_ = v___x_3235_;
goto v___jp_3209_;
}
}
v___jp_3182_:
{
lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = lean_array_get_size(v_clashes_3185_);
v___x_3188_ = lean_nat_dec_lt(v___x_3135_, v___x_3187_);
if (v___x_3188_ == 0)
{
lean_dec_ref(v_clashes_3185_);
lean_dec(v_src_3183_);
if (lean_obj_tag(v_tc_x3f_3184_) == 1)
{
lean_object* v_val_3189_; lean_object* v_rootToolchainFile_3190_; 
v_val_3189_ = lean_ctor_get(v_tc_x3f_3184_, 0);
lean_inc(v_val_3189_);
lean_dec_ref_known(v_tc_x3f_3184_, 1);
v_rootToolchainFile_3190_ = l_Lake_joinRelative(v_dir_3173_, v___x_3175_);
if (lean_obj_tag(v_a_3178_) == 0)
{
lean_del_object(v___x_3180_);
v___y_3130_ = v_val_3189_;
v___y_3131_ = v_rootToolchainFile_3190_;
v___y_3132_ = v___x_3188_;
goto v___jp_3129_;
}
else
{
lean_object* v_val_3191_; uint8_t v___x_3192_; 
v_val_3191_ = lean_ctor_get(v_a_3178_, 0);
lean_inc(v_val_3191_);
lean_dec_ref_known(v_a_3178_, 1);
lean_inc(v_val_3189_);
v___x_3192_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3191_, v_val_3189_);
if (v___x_3192_ == 0)
{
lean_del_object(v___x_3180_);
v___y_3130_ = v_val_3189_;
v___y_3131_ = v_rootToolchainFile_3190_;
v___y_3132_ = v___x_3192_;
goto v___jp_3129_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
lean_dec_ref(v_rootToolchainFile_3190_);
lean_dec(v_val_3189_);
lean_dec(v_lakeArgs_x3f_2980_);
lean_dec_ref(v_lakeEnv_2979_);
v___x_3193_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2969_);
v___x_3194_ = lean_apply_2(v_a_2969_, v___x_3193_, lean_box(0));
v___x_3195_ = lean_box(0);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3195_);
v___x_3197_ = v___x_3180_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
lean_dec(v_tc_x3f_3184_);
lean_dec(v_a_3178_);
lean_dec_ref(v_dir_3173_);
lean_dec(v_lakeArgs_x3f_2980_);
lean_dec_ref(v_lakeEnv_2979_);
v___x_3199_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2969_);
v___x_3200_ = lean_apply_2(v_a_2969_, v___x_3199_, lean_box(0));
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3200_);
v___x_3202_ = v___x_3180_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
else
{
lean_del_object(v___x_3180_);
lean_dec(v_a_3178_);
lean_dec_ref(v_dir_3173_);
lean_dec(v_lakeArgs_x3f_2980_);
lean_dec_ref(v_lakeEnv_2979_);
if (lean_obj_tag(v_tc_x3f_3184_) == 1)
{
if (v_fixed_3186_ == 0)
{
lean_object* v_val_3204_; lean_object* v___x_3205_; 
v_val_3204_ = lean_ctor_get(v_tc_x3f_3184_, 0);
lean_inc(v_val_3204_);
lean_dec_ref_known(v_tc_x3f_3184_, 1);
v___x_3205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3163_ = v_clashes_3185_;
v___y_3164_ = v_val_3204_;
v___y_3165_ = v_src_3183_;
v___y_3166_ = v___x_3188_;
v___y_3167_ = v___x_3187_;
v___y_3168_ = v___x_3205_;
goto v___jp_3162_;
}
else
{
lean_object* v_val_3206_; lean_object* v___x_3207_; 
v_val_3206_ = lean_ctor_get(v_tc_x3f_3184_, 0);
lean_inc(v_val_3206_);
lean_dec_ref_known(v_tc_x3f_3184_, 1);
v___x_3207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3163_ = v_clashes_3185_;
v___y_3164_ = v_val_3206_;
v___y_3165_ = v_src_3183_;
v___y_3166_ = v___x_3188_;
v___y_3167_ = v___x_3187_;
v___y_3168_ = v___x_3207_;
goto v___jp_3162_;
}
}
else
{
lean_object* v___x_3208_; 
lean_dec(v_tc_x3f_3184_);
lean_dec(v_src_3183_);
v___x_3208_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3137_ = v_clashes_3185_;
v___y_3138_ = v___x_3187_;
v___y_3139_ = v___x_3208_;
goto v___jp_3136_;
}
}
}
v___jp_3209_:
{
if (lean_obj_tag(v___y_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v_src_3212_; lean_object* v_tc_x3f_3213_; lean_object* v_clashes_3214_; uint8_t v_fixed_3215_; 
v_a_3211_ = lean_ctor_get(v___y_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___y_3210_, 1);
v_src_3212_ = lean_ctor_get(v_a_3211_, 0);
lean_inc(v_src_3212_);
v_tc_x3f_3213_ = lean_ctor_get(v_a_3211_, 1);
lean_inc(v_tc_x3f_3213_);
v_clashes_3214_ = lean_ctor_get(v_a_3211_, 2);
lean_inc_ref(v_clashes_3214_);
v_fixed_3215_ = lean_ctor_get_uint8(v_a_3211_, sizeof(void*)*3);
lean_dec(v_a_3211_);
v_src_3183_ = v_src_3212_;
v_tc_x3f_3184_ = v_tc_x3f_3213_;
v_clashes_3185_ = v_clashes_3214_;
v_fixed_3186_ = v_fixed_3215_;
goto v___jp_3182_;
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_del_object(v___x_3180_);
lean_dec(v_a_3178_);
lean_dec_ref(v_dir_3173_);
lean_dec(v_lakeArgs_x3f_2980_);
lean_dec_ref(v_lakeEnv_2979_);
v_a_3216_ = lean_ctor_get(v___y_3210_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___y_3210_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___y_3210_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___y_3210_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v_config_3174_);
lean_dec_ref(v_dir_3173_);
lean_dec(v_baseName_3172_);
lean_dec(v_lakeArgs_x3f_2980_);
lean_dec_ref(v_lakeEnv_2979_);
v_a_3237_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3239_ = v___x_3177_;
v_isShared_3240_ = v_isSharedCheck_3249_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3177_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3249_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; uint8_t v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3241_ = lean_io_error_to_string(v_a_3237_);
v___x_3242_ = 3;
v___x_3243_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*1, v___x_3242_);
lean_inc_ref(v_a_2969_);
v___x_3244_ = lean_apply_2(v_a_2969_, v___x_3243_, lean_box(0));
v___x_3245_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3245_);
v___x_3247_ = v___x_3239_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2973_:
{
uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2975_ = 2;
v___x_2976_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2976_, 0, v___y_2974_);
lean_ctor_set_uint8(v___x_2976_, sizeof(void*)*1, v___x_2975_);
lean_inc_ref(v_a_2969_);
v___x_2977_ = lean_apply_2(v_a_2969_, v___x_2976_, lean_box(0));
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
v___jp_2982_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_inc_ref(v___y_2984_);
v___x_2987_ = lean_string_append(v___y_2984_, v___y_2986_);
v___x_2988_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2989_ = lean_string_append(v___x_2987_, v___x_2988_);
v___x_2990_ = 1;
v___x_2991_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2991_, 0, v___x_2989_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*1, v___x_2990_);
lean_inc_ref(v_a_2969_);
v___x_2992_ = lean_apply_2(v_a_2969_, v___x_2991_, lean_box(0));
v___x_2993_ = l_IO_FS_writeFile(v___y_2985_, v___y_2986_);
lean_dec_ref(v___y_2985_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_dec_ref_known(v___x_2993_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2980_) == 1)
{
lean_object* v_elan_x3f_2994_; 
v_elan_x3f_2994_ = lean_ctor_get(v_lakeEnv_2979_, 2);
if (lean_obj_tag(v_elan_x3f_2994_) == 1)
{
lean_object* v_val_2995_; lean_object* v_val_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_elan_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_val_2995_ = lean_ctor_get(v_lakeArgs_x3f_2980_, 0);
lean_inc(v_val_2995_);
lean_dec_ref_known(v_lakeArgs_x3f_2980_, 1);
v_val_2996_ = lean_ctor_get(v_elan_x3f_2994_, 0);
v___x_2997_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2969_);
v___x_2998_ = lean_apply_2(v_a_2969_, v___x_2997_, lean_box(0));
v___x_2999_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_3000_ = lean_ctor_get(v_val_2996_, 1);
lean_inc_ref(v_elan_3000_);
v___x_3001_ = 1;
v___x_3002_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_3003_ = lean_unsigned_to_nat(4u);
v___x_3004_ = lean_mk_empty_array_with_capacity(v___x_3003_);
lean_dec_ref(v___x_3004_);
v___x_3005_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_3006_ = lean_array_push(v___x_3005_, v___y_2986_);
v___x_3007_ = lean_array_push(v___x_3006_, v___x_3002_);
v___x_3008_ = l_Array_append___redArg(v___x_3007_, v_val_2995_);
lean_dec(v_val_2995_);
v___x_3009_ = lean_box(0);
v___x_3010_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2979_);
v___x_3011_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3011_, 0, v___x_2999_);
lean_ctor_set(v___x_3011_, 1, v_elan_3000_);
lean_ctor_set(v___x_3011_, 2, v___x_3008_);
lean_ctor_set(v___x_3011_, 3, v___x_3009_);
lean_ctor_set(v___x_3011_, 4, v___x_3010_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*5, v___x_3001_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*5 + 1, v___y_2983_);
v___x_3012_ = lean_io_process_spawn(v___x_3011_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = lean_io_process_child_wait(v___x_2999_, v_a_3013_);
lean_dec(v_a_3013_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; uint32_t v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_unbox_uint32(v_a_3015_);
lean_dec(v_a_3015_);
v___x_3017_ = lean_uint32_to_uint8(v___x_3016_);
v___x_3018_ = lean_io_exit(v___x_3017_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3039_; 
v_a_3027_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3029_ = v___x_3018_;
v_isShared_3030_ = v_isSharedCheck_3039_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3018_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3039_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3031_ = lean_io_error_to_string(v_a_3027_);
v___x_3032_ = 3;
v___x_3033_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3033_, 0, v___x_3031_);
lean_ctor_set_uint8(v___x_3033_, sizeof(void*)*1, v___x_3032_);
lean_inc_ref(v_a_2969_);
v___x_3034_ = lean_apply_2(v_a_2969_, v___x_3033_, lean_box(0));
v___x_3035_ = lean_box(0);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3035_);
v___x_3037_ = v___x_3029_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3052_; 
v_a_3040_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3042_ = v___x_3014_;
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3014_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3044_ = lean_io_error_to_string(v_a_3040_);
v___x_3045_ = 3;
v___x_3046_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*1, v___x_3045_);
lean_inc_ref(v_a_2969_);
v___x_3047_ = lean_apply_2(v_a_2969_, v___x_3046_, lean_box(0));
v___x_3048_ = lean_box(0);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3048_);
v___x_3050_ = v___x_3042_;
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
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3065_; 
v_a_3053_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3055_ = v___x_3012_;
v_isShared_3056_ = v_isSharedCheck_3065_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3012_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3065_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3057_ = lean_io_error_to_string(v_a_3053_);
v___x_3058_ = 3;
v___x_3059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*1, v___x_3058_);
lean_inc_ref(v_a_2969_);
v___x_3060_ = lean_apply_2(v_a_2969_, v___x_3059_, lean_box(0));
v___x_3061_ = lean_box(0);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3061_);
v___x_3063_ = v___x_3055_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; lean_object* v___x_3069_; 
lean_dec_ref_known(v_lakeArgs_x3f_2980_, 1);
lean_dec_ref(v___y_2986_);
lean_dec_ref(v_lakeEnv_2979_);
v___x_3066_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2969_);
v___x_3067_ = lean_apply_2(v_a_2969_, v___x_3066_, lean_box(0));
v___x_3068_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3069_ = lean_io_exit(v___x_3068_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3090_; 
v_a_3078_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3080_ = v___x_3069_;
v_isShared_3081_ = v_isSharedCheck_3090_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3069_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3090_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3082_ = lean_io_error_to_string(v_a_3078_);
v___x_3083_ = 3;
v___x_3084_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set_uint8(v___x_3084_, sizeof(void*)*1, v___x_3083_);
lean_inc_ref(v_a_2969_);
v___x_3085_ = lean_apply_2(v_a_2969_, v___x_3084_, lean_box(0));
v___x_3086_ = lean_box(0);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3086_);
v___x_3088_ = v___x_3080_;
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
}
}
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref(v___y_2986_);
lean_dec(v_lakeArgs_x3f_2980_);
lean_dec_ref(v_lakeEnv_2979_);
v___x_3091_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2969_);
v___x_3092_ = lean_apply_2(v_a_2969_, v___x_3091_, lean_box(0));
v___x_3093_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3094_ = lean_io_exit(v___x_3093_);
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
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3115_; 
v_a_3103_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3105_ = v___x_3094_;
v_isShared_3106_ = v_isSharedCheck_3115_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3094_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3115_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; uint8_t v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3107_ = lean_io_error_to_string(v_a_3103_);
v___x_3108_ = 3;
v___x_3109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set_uint8(v___x_3109_, sizeof(void*)*1, v___x_3108_);
lean_inc_ref(v_a_2969_);
v___x_3110_ = lean_apply_2(v_a_2969_, v___x_3109_, lean_box(0));
v___x_3111_ = lean_box(0);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3111_);
v___x_3113_ = v___x_3105_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref(v___y_2986_);
lean_dec(v_lakeArgs_x3f_2980_);
lean_dec_ref(v_lakeEnv_2979_);
v_a_3116_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3118_ = v___x_2993_;
v_isShared_3119_ = v_isSharedCheck_3128_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_2993_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3128_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; uint8_t v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3120_ = lean_io_error_to_string(v_a_3116_);
v___x_3121_ = 3;
v___x_3122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3122_, 0, v___x_3120_);
lean_ctor_set_uint8(v___x_3122_, sizeof(void*)*1, v___x_3121_);
lean_inc_ref(v_a_2969_);
v___x_3123_ = lean_apply_2(v_a_2969_, v___x_3122_, lean_box(0));
v___x_3124_ = lean_box(0);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3124_);
v___x_3126_ = v___x_3118_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
v___jp_3129_:
{
lean_object* v___x_3133_; lean_object* v_toString_3134_; 
v___x_3133_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3134_ = lean_ctor_get(v___y_3130_, 0);
lean_inc_ref(v_toString_3134_);
lean_dec_ref(v___y_3130_);
v___y_2983_ = v___y_3132_;
v___y_2984_ = v___x_3133_;
v___y_2985_ = v___y_3131_;
v___y_2986_ = v_toString_3134_;
goto v___jp_2982_;
}
v___jp_3136_:
{
uint8_t v___x_3140_; 
v___x_3140_ = lean_nat_dec_lt(v___x_3135_, v___y_3138_);
if (v___x_3140_ == 0)
{
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
v___y_2974_ = v___y_3139_;
goto v___jp_2973_;
}
else
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_nat_dec_le(v___y_3138_, v___y_3138_);
if (v___x_3141_ == 0)
{
if (v___x_3140_ == 0)
{
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
v___y_2974_ = v___y_3139_;
goto v___jp_2973_;
}
else
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((size_t)0ULL);
v___x_3143_ = lean_usize_of_nat(v___y_3138_);
lean_dec(v___y_3138_);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3137_, v___x_3142_, v___x_3143_, v___y_3139_);
lean_dec_ref(v___y_3137_);
v___y_2974_ = v___x_3144_;
goto v___jp_2973_;
}
}
else
{
size_t v___x_3145_; size_t v___x_3146_; lean_object* v___x_3147_; 
v___x_3145_ = ((size_t)0ULL);
v___x_3146_ = lean_usize_of_nat(v___y_3138_);
lean_dec(v___y_3138_);
v___x_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3137_, v___x_3145_, v___x_3146_, v___y_3139_);
lean_dec_ref(v___y_3137_);
v___y_2974_ = v___x_3147_;
goto v___jp_2973_;
}
}
}
v___jp_3148_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_inc_ref(v___y_3152_);
v___x_3156_ = lean_string_append(v___y_3152_, v___y_3155_);
lean_dec_ref(v___y_3155_);
v___x_3157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3158_ = lean_string_append(v___x_3156_, v___x_3157_);
v___x_3159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3151_, v___y_3154_);
v___x_3160_ = lean_string_append(v___x_3158_, v___x_3159_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = lean_string_append(v___x_3160_, v___y_3150_);
v___y_3137_ = v___y_3149_;
v___y_3138_ = v___y_3153_;
v___y_3139_ = v___x_3161_;
goto v___jp_3136_;
}
v___jp_3162_:
{
lean_object* v___x_3169_; lean_object* v_toString_3170_; 
v___x_3169_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3170_ = lean_ctor_get(v___y_3164_, 0);
lean_inc_ref(v_toString_3170_);
lean_dec_ref(v___y_3164_);
v___y_3149_ = v___y_3163_;
v___y_3150_ = v___y_3168_;
v___y_3151_ = v___y_3165_;
v___y_3152_ = v___x_3169_;
v___y_3153_ = v___y_3167_;
v___y_3154_ = v___y_3166_;
v___y_3155_ = v_toString_3170_;
goto v___jp_3148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3250_, lean_object* v_ws_3251_, lean_object* v_rootDeps_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3250_, v_ws_3251_, v_rootDeps_3252_);
lean_dec_ref(v_rootDeps_3252_);
lean_dec_ref(v_a_3250_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3255_){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = lean_box(1);
v___x_3257_ = lean_panic_fn_borrowed(v___x_3256_, v_msg_3255_);
return v___x_3257_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3261_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3262_ = lean_unsigned_to_nat(35u);
v___x_3263_ = lean_unsigned_to_nat(182u);
v___x_3264_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3265_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3266_ = l_mkPanicMessageWithDecl(v___x_3265_, v___x_3264_, v___x_3263_, v___x_3262_, v___x_3261_);
return v___x_3266_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3267_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3268_ = lean_unsigned_to_nat(21u);
v___x_3269_ = lean_unsigned_to_nat(183u);
v___x_3270_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3271_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3272_ = l_mkPanicMessageWithDecl(v___x_3271_, v___x_3270_, v___x_3269_, v___x_3268_, v___x_3267_);
return v___x_3272_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3275_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3276_ = lean_unsigned_to_nat(35u);
v___x_3277_ = lean_unsigned_to_nat(276u);
v___x_3278_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3279_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3280_ = l_mkPanicMessageWithDecl(v___x_3279_, v___x_3278_, v___x_3277_, v___x_3276_, v___x_3275_);
return v___x_3280_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3281_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3282_ = lean_unsigned_to_nat(21u);
v___x_3283_ = lean_unsigned_to_nat(277u);
v___x_3284_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3285_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3286_ = l_mkPanicMessageWithDecl(v___x_3285_, v___x_3284_, v___x_3283_, v___x_3282_, v___x_3281_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3287_, lean_object* v_v_3288_, lean_object* v_t_3289_){
_start:
{
if (lean_obj_tag(v_t_3289_) == 0)
{
lean_object* v_size_3290_; lean_object* v_k_3291_; lean_object* v_v_3292_; lean_object* v_l_3293_; lean_object* v_r_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3650_; 
v_size_3290_ = lean_ctor_get(v_t_3289_, 0);
v_k_3291_ = lean_ctor_get(v_t_3289_, 1);
v_v_3292_ = lean_ctor_get(v_t_3289_, 2);
v_l_3293_ = lean_ctor_get(v_t_3289_, 3);
v_r_3294_ = lean_ctor_get(v_t_3289_, 4);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_t_3289_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3296_ = v_t_3289_;
v_isShared_3297_ = v_isSharedCheck_3650_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_r_3294_);
lean_inc(v_l_3293_);
lean_inc(v_v_3292_);
lean_inc(v_k_3291_);
lean_inc(v_size_3290_);
lean_dec(v_t_3289_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3650_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
uint8_t v___x_3298_; 
v___x_3298_ = lean_string_compare(v_k_3287_, v_k_3291_);
switch(v___x_3298_)
{
case 0:
{
lean_object* v___x_3299_; 
lean_dec(v_size_3290_);
v___x_3299_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3287_, v_v_3288_, v_l_3293_);
if (lean_obj_tag(v_r_3294_) == 0)
{
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_size_3300_; lean_object* v_size_3301_; lean_object* v_k_3302_; lean_object* v_v_3303_; lean_object* v_l_3304_; lean_object* v_r_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; 
v_size_3300_ = lean_ctor_get(v_r_3294_, 0);
v_size_3301_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_size_3301_);
v_k_3302_ = lean_ctor_get(v___x_3299_, 1);
lean_inc(v_k_3302_);
v_v_3303_ = lean_ctor_get(v___x_3299_, 2);
lean_inc(v_v_3303_);
v_l_3304_ = lean_ctor_get(v___x_3299_, 3);
lean_inc(v_l_3304_);
v_r_3305_ = lean_ctor_get(v___x_3299_, 4);
lean_inc(v_r_3305_);
v___x_3306_ = lean_unsigned_to_nat(3u);
v___x_3307_ = lean_nat_mul(v___x_3306_, v_size_3300_);
v___x_3308_ = lean_nat_dec_lt(v___x_3307_, v_size_3301_);
lean_dec(v___x_3307_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
lean_dec(v_r_3305_);
lean_dec(v_l_3304_);
lean_dec(v_v_3303_);
lean_dec(v_k_3302_);
v___x_3309_ = lean_unsigned_to_nat(1u);
v___x_3310_ = lean_nat_add(v___x_3309_, v_size_3301_);
lean_dec(v_size_3301_);
v___x_3311_ = lean_nat_add(v___x_3310_, v_size_3300_);
lean_dec(v___x_3310_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 3, v___x_3299_);
lean_ctor_set(v___x_3296_, 0, v___x_3311_);
v___x_3313_ = v___x_3296_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_r_3294_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
else
{
lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3386_; 
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; lean_object* v_unused_3388_; lean_object* v_unused_3389_; lean_object* v_unused_3390_; lean_object* v_unused_3391_; 
v_unused_3387_ = lean_ctor_get(v___x_3299_, 4);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v___x_3299_, 3);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v___x_3299_, 2);
lean_dec(v_unused_3389_);
v_unused_3390_ = lean_ctor_get(v___x_3299_, 1);
lean_dec(v_unused_3390_);
v_unused_3391_ = lean_ctor_get(v___x_3299_, 0);
lean_dec(v_unused_3391_);
v___x_3316_ = v___x_3299_;
v_isShared_3317_ = v_isSharedCheck_3386_;
goto v_resetjp_3315_;
}
else
{
lean_dec(v___x_3299_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3386_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
if (lean_obj_tag(v_l_3304_) == 0)
{
if (lean_obj_tag(v_r_3305_) == 0)
{
lean_object* v_size_3318_; lean_object* v_size_3319_; lean_object* v_k_3320_; lean_object* v_v_3321_; lean_object* v_l_3322_; lean_object* v_r_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v_size_3318_ = lean_ctor_get(v_l_3304_, 0);
v_size_3319_ = lean_ctor_get(v_r_3305_, 0);
v_k_3320_ = lean_ctor_get(v_r_3305_, 1);
v_v_3321_ = lean_ctor_get(v_r_3305_, 2);
v_l_3322_ = lean_ctor_get(v_r_3305_, 3);
v_r_3323_ = lean_ctor_get(v_r_3305_, 4);
v___x_3324_ = lean_unsigned_to_nat(2u);
v___x_3325_ = lean_nat_mul(v___x_3324_, v_size_3318_);
v___x_3326_ = lean_nat_dec_lt(v_size_3319_, v___x_3325_);
lean_dec(v___x_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3356_; 
lean_inc(v_r_3323_);
lean_inc(v_l_3322_);
lean_inc(v_v_3321_);
lean_inc(v_k_3320_);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_r_3305_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; lean_object* v_unused_3358_; lean_object* v_unused_3359_; lean_object* v_unused_3360_; lean_object* v_unused_3361_; 
v_unused_3357_ = lean_ctor_get(v_r_3305_, 4);
lean_dec(v_unused_3357_);
v_unused_3358_ = lean_ctor_get(v_r_3305_, 3);
lean_dec(v_unused_3358_);
v_unused_3359_ = lean_ctor_get(v_r_3305_, 2);
lean_dec(v_unused_3359_);
v_unused_3360_ = lean_ctor_get(v_r_3305_, 1);
lean_dec(v_unused_3360_);
v_unused_3361_ = lean_ctor_get(v_r_3305_, 0);
lean_dec(v_unused_3361_);
v___x_3328_ = v_r_3305_;
v_isShared_3329_ = v_isSharedCheck_3356_;
goto v_resetjp_3327_;
}
else
{
lean_dec(v_r_3305_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3356_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___x_3344_; lean_object* v___y_3346_; 
v___x_3330_ = lean_unsigned_to_nat(1u);
v___x_3331_ = lean_nat_add(v___x_3330_, v_size_3301_);
lean_dec(v_size_3301_);
v___x_3332_ = lean_nat_add(v___x_3331_, v_size_3300_);
lean_dec(v___x_3331_);
v___x_3344_ = lean_nat_add(v___x_3330_, v_size_3318_);
if (lean_obj_tag(v_l_3322_) == 0)
{
lean_object* v_size_3354_; 
v_size_3354_ = lean_ctor_get(v_l_3322_, 0);
lean_inc(v_size_3354_);
v___y_3346_ = v_size_3354_;
goto v___jp_3345_;
}
else
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_unsigned_to_nat(0u);
v___y_3346_ = v___x_3355_;
goto v___jp_3345_;
}
v___jp_3333_:
{
lean_object* v___x_3337_; lean_object* v___x_3339_; 
v___x_3337_ = lean_nat_add(v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec(v___y_3335_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 4, v_r_3294_);
lean_ctor_set(v___x_3328_, 3, v_r_3323_);
lean_ctor_set(v___x_3328_, 2, v_v_3292_);
lean_ctor_set(v___x_3328_, 1, v_k_3291_);
lean_ctor_set(v___x_3328_, 0, v___x_3337_);
v___x_3339_ = v___x_3328_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3343_, 3, v_r_3323_);
lean_ctor_set(v_reuseFailAlloc_3343_, 4, v_r_3294_);
v___x_3339_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
lean_object* v___x_3341_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 4, v___x_3339_);
lean_ctor_set(v___x_3316_, 3, v___y_3334_);
lean_ctor_set(v___x_3316_, 2, v_v_3321_);
lean_ctor_set(v___x_3316_, 1, v_k_3320_);
lean_ctor_set(v___x_3316_, 0, v___x_3332_);
v___x_3341_ = v___x_3316_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_k_3320_);
lean_ctor_set(v_reuseFailAlloc_3342_, 2, v_v_3321_);
lean_ctor_set(v_reuseFailAlloc_3342_, 3, v___y_3334_);
lean_ctor_set(v_reuseFailAlloc_3342_, 4, v___x_3339_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
v___jp_3345_:
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_nat_add(v___x_3344_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec(v___x_3344_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_l_3322_);
lean_ctor_set(v___x_3296_, 3, v_l_3304_);
lean_ctor_set(v___x_3296_, 2, v_v_3303_);
lean_ctor_set(v___x_3296_, 1, v_k_3302_);
lean_ctor_set(v___x_3296_, 0, v___x_3347_);
v___x_3349_ = v___x_3296_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_k_3302_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_v_3303_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v_l_3304_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v_l_3322_);
v___x_3349_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_nat_add(v___x_3330_, v_size_3300_);
if (lean_obj_tag(v_r_3323_) == 0)
{
lean_object* v_size_3351_; 
v_size_3351_ = lean_ctor_get(v_r_3323_, 0);
lean_inc(v_size_3351_);
v___y_3334_ = v___x_3349_;
v___y_3335_ = v___x_3350_;
v___y_3336_ = v_size_3351_;
goto v___jp_3333_;
}
else
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_unsigned_to_nat(0u);
v___y_3334_ = v___x_3349_;
v___y_3335_ = v___x_3350_;
v___y_3336_ = v___x_3352_;
goto v___jp_3333_;
}
}
}
}
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3368_; 
lean_del_object(v___x_3296_);
v___x_3362_ = lean_unsigned_to_nat(1u);
v___x_3363_ = lean_nat_add(v___x_3362_, v_size_3301_);
lean_dec(v_size_3301_);
v___x_3364_ = lean_nat_add(v___x_3363_, v_size_3300_);
lean_dec(v___x_3363_);
v___x_3365_ = lean_nat_add(v___x_3362_, v_size_3300_);
v___x_3366_ = lean_nat_add(v___x_3365_, v_size_3319_);
lean_dec(v___x_3365_);
lean_inc_ref(v_r_3294_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 4, v_r_3294_);
lean_ctor_set(v___x_3316_, 3, v_r_3305_);
lean_ctor_set(v___x_3316_, 2, v_v_3292_);
lean_ctor_set(v___x_3316_, 1, v_k_3291_);
lean_ctor_set(v___x_3316_, 0, v___x_3366_);
v___x_3368_ = v___x_3316_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3381_, 3, v_r_3305_);
lean_ctor_set(v_reuseFailAlloc_3381_, 4, v_r_3294_);
v___x_3368_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
v_isSharedCheck_3375_ = !lean_is_exclusive(v_r_3294_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; lean_object* v_unused_3379_; lean_object* v_unused_3380_; 
v_unused_3376_ = lean_ctor_get(v_r_3294_, 4);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_r_3294_, 3);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_r_3294_, 2);
lean_dec(v_unused_3378_);
v_unused_3379_ = lean_ctor_get(v_r_3294_, 1);
lean_dec(v_unused_3379_);
v_unused_3380_ = lean_ctor_get(v_r_3294_, 0);
lean_dec(v_unused_3380_);
v___x_3370_ = v_r_3294_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_dec(v_r_3294_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 4, v___x_3368_);
lean_ctor_set(v___x_3370_, 3, v_l_3304_);
lean_ctor_set(v___x_3370_, 2, v_v_3303_);
lean_ctor_set(v___x_3370_, 1, v_k_3302_);
lean_ctor_set(v___x_3370_, 0, v___x_3364_);
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_k_3302_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_v_3303_);
lean_ctor_set(v_reuseFailAlloc_3374_, 3, v_l_3304_);
lean_ctor_set(v_reuseFailAlloc_3374_, 4, v___x_3368_);
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
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
lean_dec_ref_known(v_l_3304_, 5);
lean_del_object(v___x_3316_);
lean_dec(v_v_3303_);
lean_dec(v_k_3302_);
lean_dec(v_size_3301_);
lean_dec_ref_known(v_r_3294_, 5);
lean_del_object(v___x_3296_);
lean_dec(v_v_3292_);
lean_dec(v_k_3291_);
v___x_3382_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3383_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3382_);
return v___x_3383_;
}
}
else
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_del_object(v___x_3316_);
lean_dec(v_r_3305_);
lean_dec(v_v_3303_);
lean_dec(v_k_3302_);
lean_dec(v_size_3301_);
lean_dec_ref_known(v_r_3294_, 5);
lean_del_object(v___x_3296_);
lean_dec(v_v_3292_);
lean_dec(v_k_3291_);
v___x_3384_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3385_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3384_);
return v___x_3385_;
}
}
}
}
else
{
lean_object* v_size_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v_size_3392_ = lean_ctor_get(v_r_3294_, 0);
v___x_3393_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_nat_add(v___x_3393_, v_size_3392_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 3, v___x_3299_);
lean_ctor_set(v___x_3296_, 0, v___x_3394_);
v___x_3396_ = v___x_3296_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3397_, 3, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3397_, 4, v_r_3294_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
else
{
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_l_3398_; 
v_l_3398_ = lean_ctor_get(v___x_3299_, 3);
lean_inc(v_l_3398_);
if (lean_obj_tag(v_l_3398_) == 0)
{
lean_object* v_r_3399_; 
v_r_3399_ = lean_ctor_get(v___x_3299_, 4);
lean_inc(v_r_3399_);
if (lean_obj_tag(v_r_3399_) == 0)
{
lean_object* v_size_3400_; lean_object* v_k_3401_; lean_object* v_v_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3416_; 
v_size_3400_ = lean_ctor_get(v___x_3299_, 0);
v_k_3401_ = lean_ctor_get(v___x_3299_, 1);
v_v_3402_ = lean_ctor_get(v___x_3299_, 2);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; lean_object* v_unused_3418_; 
v_unused_3417_ = lean_ctor_get(v___x_3299_, 4);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v___x_3299_, 3);
lean_dec(v_unused_3418_);
v___x_3404_ = v___x_3299_;
v_isShared_3405_ = v_isSharedCheck_3416_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_v_3402_);
lean_inc(v_k_3401_);
lean_inc(v_size_3400_);
lean_dec(v___x_3299_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3416_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_size_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
v_size_3406_ = lean_ctor_get(v_r_3399_, 0);
v___x_3407_ = lean_unsigned_to_nat(1u);
v___x_3408_ = lean_nat_add(v___x_3407_, v_size_3400_);
lean_dec(v_size_3400_);
v___x_3409_ = lean_nat_add(v___x_3407_, v_size_3406_);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 4, v_r_3294_);
lean_ctor_set(v___x_3404_, 3, v_r_3399_);
lean_ctor_set(v___x_3404_, 2, v_v_3292_);
lean_ctor_set(v___x_3404_, 1, v_k_3291_);
lean_ctor_set(v___x_3404_, 0, v___x_3409_);
v___x_3411_ = v___x_3404_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3415_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3415_, 3, v_r_3399_);
lean_ctor_set(v_reuseFailAlloc_3415_, 4, v_r_3294_);
v___x_3411_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3411_);
lean_ctor_set(v___x_3296_, 3, v_l_3398_);
lean_ctor_set(v___x_3296_, 2, v_v_3402_);
lean_ctor_set(v___x_3296_, 1, v_k_3401_);
lean_ctor_set(v___x_3296_, 0, v___x_3408_);
v___x_3413_ = v___x_3296_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_k_3401_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_v_3402_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_l_3398_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_k_3419_; lean_object* v_v_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3432_; 
v_k_3419_ = lean_ctor_get(v___x_3299_, 1);
v_v_3420_ = lean_ctor_get(v___x_3299_, 2);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; lean_object* v_unused_3434_; lean_object* v_unused_3435_; 
v_unused_3433_ = lean_ctor_get(v___x_3299_, 4);
lean_dec(v_unused_3433_);
v_unused_3434_ = lean_ctor_get(v___x_3299_, 3);
lean_dec(v_unused_3434_);
v_unused_3435_ = lean_ctor_get(v___x_3299_, 0);
lean_dec(v_unused_3435_);
v___x_3422_ = v___x_3299_;
v_isShared_3423_ = v_isSharedCheck_3432_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_v_3420_);
lean_inc(v_k_3419_);
lean_dec(v___x_3299_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3432_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3427_; 
v___x_3424_ = lean_unsigned_to_nat(3u);
v___x_3425_ = lean_unsigned_to_nat(1u);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 3, v_r_3399_);
lean_ctor_set(v___x_3422_, 2, v_v_3292_);
lean_ctor_set(v___x_3422_, 1, v_k_3291_);
lean_ctor_set(v___x_3422_, 0, v___x_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_r_3399_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_r_3399_);
v___x_3427_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3429_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3427_);
lean_ctor_set(v___x_3296_, 3, v_l_3398_);
lean_ctor_set(v___x_3296_, 2, v_v_3420_);
lean_ctor_set(v___x_3296_, 1, v_k_3419_);
lean_ctor_set(v___x_3296_, 0, v___x_3424_);
v___x_3429_ = v___x_3296_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_k_3419_);
lean_ctor_set(v_reuseFailAlloc_3430_, 2, v_v_3420_);
lean_ctor_set(v_reuseFailAlloc_3430_, 3, v_l_3398_);
lean_ctor_set(v_reuseFailAlloc_3430_, 4, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
lean_object* v_r_3436_; 
v_r_3436_ = lean_ctor_get(v___x_3299_, 4);
lean_inc(v_r_3436_);
if (lean_obj_tag(v_r_3436_) == 0)
{
lean_object* v_k_3437_; lean_object* v_v_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3462_; 
v_k_3437_ = lean_ctor_get(v___x_3299_, 1);
v_v_3438_ = lean_ctor_get(v___x_3299_, 2);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3462_ == 0)
{
lean_object* v_unused_3463_; lean_object* v_unused_3464_; lean_object* v_unused_3465_; 
v_unused_3463_ = lean_ctor_get(v___x_3299_, 4);
lean_dec(v_unused_3463_);
v_unused_3464_ = lean_ctor_get(v___x_3299_, 3);
lean_dec(v_unused_3464_);
v_unused_3465_ = lean_ctor_get(v___x_3299_, 0);
lean_dec(v_unused_3465_);
v___x_3440_ = v___x_3299_;
v_isShared_3441_ = v_isSharedCheck_3462_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_v_3438_);
lean_inc(v_k_3437_);
lean_dec(v___x_3299_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3462_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v_k_3442_; lean_object* v_v_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3458_; 
v_k_3442_ = lean_ctor_get(v_r_3436_, 1);
v_v_3443_ = lean_ctor_get(v_r_3436_, 2);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_r_3436_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; lean_object* v_unused_3460_; lean_object* v_unused_3461_; 
v_unused_3459_ = lean_ctor_get(v_r_3436_, 4);
lean_dec(v_unused_3459_);
v_unused_3460_ = lean_ctor_get(v_r_3436_, 3);
lean_dec(v_unused_3460_);
v_unused_3461_ = lean_ctor_get(v_r_3436_, 0);
lean_dec(v_unused_3461_);
v___x_3445_ = v_r_3436_;
v_isShared_3446_ = v_isSharedCheck_3458_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_v_3443_);
lean_inc(v_k_3442_);
lean_dec(v_r_3436_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3458_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3447_ = lean_unsigned_to_nat(3u);
v___x_3448_ = lean_unsigned_to_nat(1u);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 4, v_l_3398_);
lean_ctor_set(v___x_3445_, 3, v_l_3398_);
lean_ctor_set(v___x_3445_, 2, v_v_3438_);
lean_ctor_set(v___x_3445_, 1, v_k_3437_);
lean_ctor_set(v___x_3445_, 0, v___x_3448_);
v___x_3450_ = v___x_3445_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_k_3437_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_v_3438_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v_l_3398_);
lean_ctor_set(v_reuseFailAlloc_3457_, 4, v_l_3398_);
v___x_3450_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 4, v_l_3398_);
lean_ctor_set(v___x_3440_, 2, v_v_3292_);
lean_ctor_set(v___x_3440_, 1, v_k_3291_);
lean_ctor_set(v___x_3440_, 0, v___x_3448_);
v___x_3452_ = v___x_3440_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3456_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3456_, 3, v_l_3398_);
lean_ctor_set(v_reuseFailAlloc_3456_, 4, v_l_3398_);
v___x_3452_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3454_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3452_);
lean_ctor_set(v___x_3296_, 3, v___x_3450_);
lean_ctor_set(v___x_3296_, 2, v_v_3443_);
lean_ctor_set(v___x_3296_, 1, v_k_3442_);
lean_ctor_set(v___x_3296_, 0, v___x_3447_);
v___x_3454_ = v___x_3296_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_k_3442_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v_v_3443_);
lean_ctor_set(v_reuseFailAlloc_3455_, 3, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3455_, 4, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3466_ = lean_unsigned_to_nat(2u);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_r_3436_);
lean_ctor_set(v___x_3296_, 3, v___x_3299_);
lean_ctor_set(v___x_3296_, 0, v___x_3466_);
v___x_3468_ = v___x_3296_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_r_3436_);
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
else
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3470_ = lean_unsigned_to_nat(1u);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3299_);
lean_ctor_set(v___x_3296_, 3, v___x_3299_);
lean_ctor_set(v___x_3296_, 0, v___x_3470_);
v___x_3472_ = v___x_3296_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v___x_3299_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
case 1:
{
lean_object* v___x_3475_; 
lean_dec(v_v_3292_);
lean_dec(v_k_3291_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 2, v_v_3288_);
lean_ctor_set(v___x_3296_, 1, v_k_3287_);
v___x_3475_ = v___x_3296_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_size_3290_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_k_3287_);
lean_ctor_set(v_reuseFailAlloc_3476_, 2, v_v_3288_);
lean_ctor_set(v_reuseFailAlloc_3476_, 3, v_l_3293_);
lean_ctor_set(v_reuseFailAlloc_3476_, 4, v_r_3294_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
default: 
{
lean_object* v___x_3477_; 
lean_dec(v_size_3290_);
v___x_3477_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3287_, v_v_3288_, v_r_3294_);
if (lean_obj_tag(v_l_3293_) == 0)
{
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_size_3478_; lean_object* v_size_3479_; lean_object* v_k_3480_; lean_object* v_v_3481_; lean_object* v_l_3482_; lean_object* v_r_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v_size_3478_ = lean_ctor_get(v_l_3293_, 0);
v_size_3479_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_size_3479_);
v_k_3480_ = lean_ctor_get(v___x_3477_, 1);
lean_inc(v_k_3480_);
v_v_3481_ = lean_ctor_get(v___x_3477_, 2);
lean_inc(v_v_3481_);
v_l_3482_ = lean_ctor_get(v___x_3477_, 3);
lean_inc(v_l_3482_);
v_r_3483_ = lean_ctor_get(v___x_3477_, 4);
lean_inc(v_r_3483_);
v___x_3484_ = lean_unsigned_to_nat(3u);
v___x_3485_ = lean_nat_mul(v___x_3484_, v_size_3478_);
v___x_3486_ = lean_nat_dec_lt(v___x_3485_, v_size_3479_);
lean_dec(v___x_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
lean_dec(v_r_3483_);
lean_dec(v_l_3482_);
lean_dec(v_v_3481_);
lean_dec(v_k_3480_);
v___x_3487_ = lean_unsigned_to_nat(1u);
v___x_3488_ = lean_nat_add(v___x_3487_, v_size_3478_);
v___x_3489_ = lean_nat_add(v___x_3488_, v_size_3479_);
lean_dec(v_size_3479_);
lean_dec(v___x_3488_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3477_);
lean_ctor_set(v___x_3296_, 0, v___x_3489_);
v___x_3491_ = v___x_3296_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3492_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3492_, 3, v_l_3293_);
lean_ctor_set(v_reuseFailAlloc_3492_, 4, v___x_3477_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
else
{
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3562_; 
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; lean_object* v_unused_3564_; lean_object* v_unused_3565_; lean_object* v_unused_3566_; lean_object* v_unused_3567_; 
v_unused_3563_ = lean_ctor_get(v___x_3477_, 4);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v___x_3477_, 3);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v___x_3477_, 2);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v___x_3477_, 1);
lean_dec(v_unused_3566_);
v_unused_3567_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3567_);
v___x_3494_ = v___x_3477_;
v_isShared_3495_ = v_isSharedCheck_3562_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v___x_3477_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3562_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
if (lean_obj_tag(v_l_3482_) == 0)
{
if (lean_obj_tag(v_r_3483_) == 0)
{
lean_object* v_size_3496_; lean_object* v_k_3497_; lean_object* v_v_3498_; lean_object* v_l_3499_; lean_object* v_r_3500_; lean_object* v_size_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_size_3496_ = lean_ctor_get(v_l_3482_, 0);
v_k_3497_ = lean_ctor_get(v_l_3482_, 1);
v_v_3498_ = lean_ctor_get(v_l_3482_, 2);
v_l_3499_ = lean_ctor_get(v_l_3482_, 3);
v_r_3500_ = lean_ctor_get(v_l_3482_, 4);
v_size_3501_ = lean_ctor_get(v_r_3483_, 0);
v___x_3502_ = lean_unsigned_to_nat(2u);
v___x_3503_ = lean_nat_mul(v___x_3502_, v_size_3501_);
v___x_3504_ = lean_nat_dec_lt(v_size_3496_, v___x_3503_);
lean_dec(v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3533_; 
lean_inc(v_r_3500_);
lean_inc(v_l_3499_);
lean_inc(v_v_3498_);
lean_inc(v_k_3497_);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_l_3482_);
if (v_isSharedCheck_3533_ == 0)
{
lean_object* v_unused_3534_; lean_object* v_unused_3535_; lean_object* v_unused_3536_; lean_object* v_unused_3537_; lean_object* v_unused_3538_; 
v_unused_3534_ = lean_ctor_get(v_l_3482_, 4);
lean_dec(v_unused_3534_);
v_unused_3535_ = lean_ctor_get(v_l_3482_, 3);
lean_dec(v_unused_3535_);
v_unused_3536_ = lean_ctor_get(v_l_3482_, 2);
lean_dec(v_unused_3536_);
v_unused_3537_ = lean_ctor_get(v_l_3482_, 1);
lean_dec(v_unused_3537_);
v_unused_3538_ = lean_ctor_get(v_l_3482_, 0);
lean_dec(v_unused_3538_);
v___x_3506_ = v_l_3482_;
v_isShared_3507_ = v_isSharedCheck_3533_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v_l_3482_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3533_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3523_; 
v___x_3508_ = lean_unsigned_to_nat(1u);
v___x_3509_ = lean_nat_add(v___x_3508_, v_size_3478_);
v___x_3510_ = lean_nat_add(v___x_3509_, v_size_3479_);
lean_dec(v_size_3479_);
if (lean_obj_tag(v_l_3499_) == 0)
{
lean_object* v_size_3531_; 
v_size_3531_ = lean_ctor_get(v_l_3499_, 0);
lean_inc(v_size_3531_);
v___y_3523_ = v_size_3531_;
goto v___jp_3522_;
}
else
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_unsigned_to_nat(0u);
v___y_3523_ = v___x_3532_;
goto v___jp_3522_;
}
v___jp_3511_:
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3515_ = lean_nat_add(v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 4, v_r_3483_);
lean_ctor_set(v___x_3506_, 3, v_r_3500_);
lean_ctor_set(v___x_3506_, 2, v_v_3481_);
lean_ctor_set(v___x_3506_, 1, v_k_3480_);
lean_ctor_set(v___x_3506_, 0, v___x_3515_);
v___x_3517_ = v___x_3506_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3480_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3481_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_r_3500_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_r_3483_);
v___x_3517_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3519_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v___x_3517_);
lean_ctor_set(v___x_3494_, 3, v___y_3512_);
lean_ctor_set(v___x_3494_, 2, v_v_3498_);
lean_ctor_set(v___x_3494_, 1, v_k_3497_);
lean_ctor_set(v___x_3494_, 0, v___x_3510_);
v___x_3519_ = v___x_3494_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_k_3497_);
lean_ctor_set(v_reuseFailAlloc_3520_, 2, v_v_3498_);
lean_ctor_set(v_reuseFailAlloc_3520_, 3, v___y_3512_);
lean_ctor_set(v_reuseFailAlloc_3520_, 4, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
v___jp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = lean_nat_add(v___x_3509_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec(v___x_3509_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_l_3499_);
lean_ctor_set(v___x_3296_, 0, v___x_3524_);
v___x_3526_ = v___x_3296_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3530_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3530_, 3, v_l_3293_);
lean_ctor_set(v_reuseFailAlloc_3530_, 4, v_l_3499_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_nat_add(v___x_3508_, v_size_3501_);
if (lean_obj_tag(v_r_3500_) == 0)
{
lean_object* v_size_3528_; 
v_size_3528_ = lean_ctor_get(v_r_3500_, 0);
lean_inc(v_size_3528_);
v___y_3512_ = v___x_3526_;
v___y_3513_ = v___x_3527_;
v___y_3514_ = v_size_3528_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_unsigned_to_nat(0u);
v___y_3512_ = v___x_3526_;
v___y_3513_ = v___x_3527_;
v___y_3514_ = v___x_3529_;
goto v___jp_3511_;
}
}
}
}
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
lean_del_object(v___x_3296_);
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = lean_nat_add(v___x_3539_, v_size_3478_);
v___x_3541_ = lean_nat_add(v___x_3540_, v_size_3479_);
lean_dec(v_size_3479_);
v___x_3542_ = lean_nat_add(v___x_3540_, v_size_3496_);
lean_dec(v___x_3540_);
lean_inc_ref(v_l_3293_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v_l_3482_);
lean_ctor_set(v___x_3494_, 3, v_l_3293_);
lean_ctor_set(v___x_3494_, 2, v_v_3292_);
lean_ctor_set(v___x_3494_, 1, v_k_3291_);
lean_ctor_set(v___x_3494_, 0, v___x_3542_);
v___x_3544_ = v___x_3494_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3542_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_l_3293_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v_l_3482_);
v___x_3544_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
v_isSharedCheck_3551_ = !lean_is_exclusive(v_l_3293_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; lean_object* v_unused_3553_; lean_object* v_unused_3554_; lean_object* v_unused_3555_; lean_object* v_unused_3556_; 
v_unused_3552_ = lean_ctor_get(v_l_3293_, 4);
lean_dec(v_unused_3552_);
v_unused_3553_ = lean_ctor_get(v_l_3293_, 3);
lean_dec(v_unused_3553_);
v_unused_3554_ = lean_ctor_get(v_l_3293_, 2);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_l_3293_, 1);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_l_3293_, 0);
lean_dec(v_unused_3556_);
v___x_3546_ = v_l_3293_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_dec(v_l_3293_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 4, v_r_3483_);
lean_ctor_set(v___x_3546_, 3, v___x_3544_);
lean_ctor_set(v___x_3546_, 2, v_v_3481_);
lean_ctor_set(v___x_3546_, 1, v_k_3480_);
lean_ctor_set(v___x_3546_, 0, v___x_3541_);
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_k_3480_);
lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_v_3481_);
lean_ctor_set(v_reuseFailAlloc_3550_, 3, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3550_, 4, v_r_3483_);
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
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
lean_dec_ref_known(v_l_3482_, 5);
lean_del_object(v___x_3494_);
lean_dec(v_v_3481_);
lean_dec(v_k_3480_);
lean_dec(v_size_3479_);
lean_dec_ref_known(v_l_3293_, 5);
lean_del_object(v___x_3296_);
lean_dec(v_v_3292_);
lean_dec(v_k_3291_);
v___x_3558_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3559_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3558_);
return v___x_3559_;
}
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_del_object(v___x_3494_);
lean_dec(v_r_3483_);
lean_dec(v_v_3481_);
lean_dec(v_k_3480_);
lean_dec(v_size_3479_);
lean_dec_ref_known(v_l_3293_, 5);
lean_del_object(v___x_3296_);
lean_dec(v_v_3292_);
lean_dec(v_k_3291_);
v___x_3560_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3561_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3560_);
return v___x_3561_;
}
}
}
}
else
{
lean_object* v_size_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v_size_3568_ = lean_ctor_get(v_l_3293_, 0);
v___x_3569_ = lean_unsigned_to_nat(1u);
v___x_3570_ = lean_nat_add(v___x_3569_, v_size_3568_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3477_);
lean_ctor_set(v___x_3296_, 0, v___x_3570_);
v___x_3572_ = v___x_3296_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3573_, 3, v_l_3293_);
lean_ctor_set(v_reuseFailAlloc_3573_, 4, v___x_3477_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_l_3574_; 
v_l_3574_ = lean_ctor_get(v___x_3477_, 3);
lean_inc(v_l_3574_);
if (lean_obj_tag(v_l_3574_) == 0)
{
lean_object* v_r_3575_; 
v_r_3575_ = lean_ctor_get(v___x_3477_, 4);
lean_inc(v_r_3575_);
if (lean_obj_tag(v_r_3575_) == 0)
{
lean_object* v_size_3576_; lean_object* v_k_3577_; lean_object* v_v_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3592_; 
v_size_3576_ = lean_ctor_get(v___x_3477_, 0);
v_k_3577_ = lean_ctor_get(v___x_3477_, 1);
v_v_3578_ = lean_ctor_get(v___x_3477_, 2);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; lean_object* v_unused_3594_; 
v_unused_3593_ = lean_ctor_get(v___x_3477_, 4);
lean_dec(v_unused_3593_);
v_unused_3594_ = lean_ctor_get(v___x_3477_, 3);
lean_dec(v_unused_3594_);
v___x_3580_ = v___x_3477_;
v_isShared_3581_ = v_isSharedCheck_3592_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_v_3578_);
lean_inc(v_k_3577_);
lean_inc(v_size_3576_);
lean_dec(v___x_3477_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3592_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_size_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3587_; 
v_size_3582_ = lean_ctor_get(v_l_3574_, 0);
v___x_3583_ = lean_unsigned_to_nat(1u);
v___x_3584_ = lean_nat_add(v___x_3583_, v_size_3576_);
lean_dec(v_size_3576_);
v___x_3585_ = lean_nat_add(v___x_3583_, v_size_3582_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 4, v_l_3574_);
lean_ctor_set(v___x_3580_, 3, v_l_3293_);
lean_ctor_set(v___x_3580_, 2, v_v_3292_);
lean_ctor_set(v___x_3580_, 1, v_k_3291_);
lean_ctor_set(v___x_3580_, 0, v___x_3585_);
v___x_3587_ = v___x_3580_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3591_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3591_, 3, v_l_3293_);
lean_ctor_set(v_reuseFailAlloc_3591_, 4, v_l_3574_);
v___x_3587_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_r_3575_);
lean_ctor_set(v___x_3296_, 3, v___x_3587_);
lean_ctor_set(v___x_3296_, 2, v_v_3578_);
lean_ctor_set(v___x_3296_, 1, v_k_3577_);
lean_ctor_set(v___x_3296_, 0, v___x_3584_);
v___x_3589_ = v___x_3296_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_k_3577_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_v_3578_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_r_3575_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_k_3595_; lean_object* v_v_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3620_; 
v_k_3595_ = lean_ctor_get(v___x_3477_, 1);
v_v_3596_ = lean_ctor_get(v___x_3477_, 2);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; 
v_unused_3621_ = lean_ctor_get(v___x_3477_, 4);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v___x_3477_, 3);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3623_);
v___x_3598_ = v___x_3477_;
v_isShared_3599_ = v_isSharedCheck_3620_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_v_3596_);
lean_inc(v_k_3595_);
lean_dec(v___x_3477_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3620_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v_k_3600_; lean_object* v_v_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3616_; 
v_k_3600_ = lean_ctor_get(v_l_3574_, 1);
v_v_3601_ = lean_ctor_get(v_l_3574_, 2);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_l_3574_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; lean_object* v_unused_3618_; lean_object* v_unused_3619_; 
v_unused_3617_ = lean_ctor_get(v_l_3574_, 4);
lean_dec(v_unused_3617_);
v_unused_3618_ = lean_ctor_get(v_l_3574_, 3);
lean_dec(v_unused_3618_);
v_unused_3619_ = lean_ctor_get(v_l_3574_, 0);
lean_dec(v_unused_3619_);
v___x_3603_ = v_l_3574_;
v_isShared_3604_ = v_isSharedCheck_3616_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_v_3601_);
lean_inc(v_k_3600_);
lean_dec(v_l_3574_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3616_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_unsigned_to_nat(3u);
v___x_3606_ = lean_unsigned_to_nat(1u);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_r_3575_);
lean_ctor_set(v___x_3603_, 3, v_r_3575_);
lean_ctor_set(v___x_3603_, 2, v_v_3292_);
lean_ctor_set(v___x_3603_, 1, v_k_3291_);
lean_ctor_set(v___x_3603_, 0, v___x_3606_);
v___x_3608_ = v___x_3603_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3615_, 3, v_r_3575_);
lean_ctor_set(v_reuseFailAlloc_3615_, 4, v_r_3575_);
v___x_3608_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3610_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 3, v_r_3575_);
lean_ctor_set(v___x_3598_, 0, v___x_3606_);
v___x_3610_ = v___x_3598_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_k_3595_);
lean_ctor_set(v_reuseFailAlloc_3614_, 2, v_v_3596_);
lean_ctor_set(v_reuseFailAlloc_3614_, 3, v_r_3575_);
lean_ctor_set(v_reuseFailAlloc_3614_, 4, v_r_3575_);
v___x_3610_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3610_);
lean_ctor_set(v___x_3296_, 3, v___x_3608_);
lean_ctor_set(v___x_3296_, 2, v_v_3601_);
lean_ctor_set(v___x_3296_, 1, v_k_3600_);
lean_ctor_set(v___x_3296_, 0, v___x_3605_);
v___x_3612_ = v___x_3296_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_k_3600_);
lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_v_3601_);
lean_ctor_set(v_reuseFailAlloc_3613_, 3, v___x_3608_);
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
}
}
}
else
{
lean_object* v_r_3624_; 
v_r_3624_ = lean_ctor_get(v___x_3477_, 4);
lean_inc(v_r_3624_);
if (lean_obj_tag(v_r_3624_) == 0)
{
lean_object* v_k_3625_; lean_object* v_v_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3638_; 
v_k_3625_ = lean_ctor_get(v___x_3477_, 1);
v_v_3626_ = lean_ctor_get(v___x_3477_, 2);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; lean_object* v_unused_3640_; lean_object* v_unused_3641_; 
v_unused_3639_ = lean_ctor_get(v___x_3477_, 4);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v___x_3477_, 3);
lean_dec(v_unused_3640_);
v_unused_3641_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3641_);
v___x_3628_ = v___x_3477_;
v_isShared_3629_ = v_isSharedCheck_3638_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_v_3626_);
lean_inc(v_k_3625_);
lean_dec(v___x_3477_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3638_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3630_ = lean_unsigned_to_nat(3u);
v___x_3631_ = lean_unsigned_to_nat(1u);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 4, v_l_3574_);
lean_ctor_set(v___x_3628_, 2, v_v_3292_);
lean_ctor_set(v___x_3628_, 1, v_k_3291_);
lean_ctor_set(v___x_3628_, 0, v___x_3631_);
v___x_3633_ = v___x_3628_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3631_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_l_3574_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_l_3574_);
v___x_3633_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3635_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_r_3624_);
lean_ctor_set(v___x_3296_, 3, v___x_3633_);
lean_ctor_set(v___x_3296_, 2, v_v_3626_);
lean_ctor_set(v___x_3296_, 1, v_k_3625_);
lean_ctor_set(v___x_3296_, 0, v___x_3630_);
v___x_3635_ = v___x_3296_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v_r_3624_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3642_ = lean_unsigned_to_nat(2u);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3477_);
lean_ctor_set(v___x_3296_, 3, v_r_3624_);
lean_ctor_set(v___x_3296_, 0, v___x_3642_);
v___x_3644_ = v___x_3296_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_r_3624_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v___x_3477_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3646_ = lean_unsigned_to_nat(1u);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3477_);
lean_ctor_set(v___x_3296_, 3, v___x_3477_);
lean_ctor_set(v___x_3296_, 0, v___x_3646_);
v___x_3648_ = v___x_3296_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_k_3291_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_v_3292_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v___x_3477_);
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
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = lean_unsigned_to_nat(1u);
v___x_3652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set(v___x_3652_, 1, v_k_3287_);
lean_ctor_set(v___x_3652_, 2, v_v_3288_);
lean_ctor_set(v___x_3652_, 3, v_t_3289_);
lean_ctor_set(v___x_3652_, 4, v_t_3289_);
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3653_, lean_object* v_x_3654_){
_start:
{
if (lean_obj_tag(v_x_3654_) == 0)
{
lean_object* v_k_3655_; lean_object* v_v_3656_; lean_object* v_l_3657_; lean_object* v_r_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_k_3655_ = lean_ctor_get(v_x_3654_, 1);
lean_inc(v_k_3655_);
v_v_3656_ = lean_ctor_get(v_x_3654_, 2);
lean_inc(v_v_3656_);
v_l_3657_ = lean_ctor_get(v_x_3654_, 3);
lean_inc(v_l_3657_);
v_r_3658_ = lean_ctor_get(v_x_3654_, 4);
lean_inc(v_r_3658_);
lean_dec_ref_known(v_x_3654_, 5);
v___x_3659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3653_, v_l_3657_);
v___x_3660_ = 1;
v___x_3661_ = l_Lean_Name_toString(v_k_3655_, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_v_3656_);
v___x_3663_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3661_, v___x_3662_, v___x_3659_);
v_init_3653_ = v___x_3663_;
v_x_3654_ = v_r_3658_;
goto _start;
}
else
{
return v_init_3653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3665_){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = lean_box(1);
v___x_3667_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3666_, v_m_3665_);
v___x_3668_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3671_, uint8_t v_updateToolchain_3672_, lean_object* v_ws_3673_, lean_object* v_dep_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v_baseName_3678_; lean_object* v_name_3679_; lean_object* v_opts_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_baseName_3678_ = lean_ctor_get(v___x_3671_, 1);
v_name_3679_ = lean_ctor_get(v_dep_3674_, 0);
v_opts_3680_ = lean_ctor_get(v_dep_3674_, 4);
v___x_3681_ = 0;
lean_inc(v_baseName_3678_);
v___x_3682_ = l_Lean_Name_toString(v_baseName_3678_, v___x_3681_);
v___x_3683_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3684_ = lean_string_append(v___x_3682_, v___x_3683_);
lean_inc(v_name_3679_);
v___x_3685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3679_, v_updateToolchain_3672_);
v___x_3686_ = lean_string_append(v___x_3684_, v___x_3685_);
lean_dec_ref(v___x_3685_);
v___x_3687_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3688_ = lean_string_append(v___x_3686_, v___x_3687_);
lean_inc(v_opts_3680_);
v___x_3689_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3680_);
v___x_3690_ = lean_unsigned_to_nat(80u);
v___x_3691_ = l_Lean_Json_pretty(v___x_3689_, v___x_3690_);
v___x_3692_ = lean_string_append(v___x_3688_, v___x_3691_);
lean_dec_ref(v___x_3691_);
v___x_3693_ = 0;
v___x_3694_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set_uint8(v___x_3694_, sizeof(void*)*1, v___x_3693_);
lean_inc_ref(v___y_3676_);
v___x_3695_ = lean_apply_2(v___y_3676_, v___x_3694_, lean_box(0));
v___x_3696_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3673_, v___x_3671_, v_dep_3674_, v___y_3675_, v___y_3676_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3697_, lean_object* v_updateToolchain_3698_, lean_object* v_ws_3699_, lean_object* v_dep_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
uint8_t v_updateToolchain_boxed_3704_; lean_object* v_res_3705_; 
v_updateToolchain_boxed_3704_ = lean_unbox(v_updateToolchain_3698_);
v_res_3705_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3697_, v_updateToolchain_boxed_3704_, v_ws_3699_, v_dep_3700_, v___y_3701_, v___y_3702_);
lean_dec_ref(v___y_3702_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3706_, lean_object* v_b_3707_){
_start:
{
lean_object* v_next_3708_; 
v_next_3708_ = lean_ctor_get(v_a_3706_, 0);
lean_inc(v_next_3708_);
if (lean_obj_tag(v_next_3708_) == 0)
{
lean_dec_ref(v_a_3706_);
return v_b_3707_;
}
else
{
lean_object* v_upperBound_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3729_; 
v_upperBound_3709_ = lean_ctor_get(v_a_3706_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_a_3706_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_a_3706_, 0);
lean_dec(v_unused_3730_);
v___x_3711_ = v_a_3706_;
v_isShared_3712_ = v_isSharedCheck_3729_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_upperBound_3709_);
lean_dec(v_a_3706_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3729_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v_val_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3728_; 
v_val_3713_ = lean_ctor_get(v_next_3708_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_next_3708_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3715_ = v_next_3708_;
v_isShared_3716_ = v_isSharedCheck_3728_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_val_3713_);
lean_dec(v_next_3708_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3728_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
uint8_t v___x_3717_; 
v___x_3717_ = lean_nat_dec_lt(v_val_3713_, v_upperBound_3709_);
if (v___x_3717_ == 0)
{
lean_del_object(v___x_3715_);
lean_dec(v_val_3713_);
lean_del_object(v___x_3711_);
lean_dec(v_upperBound_3709_);
return v_b_3707_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3718_ = lean_unsigned_to_nat(1u);
v___x_3719_ = lean_nat_add(v_val_3713_, v___x_3718_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3719_);
v___x_3721_ = v___x_3715_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3723_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3721_);
v___x_3723_ = v___x_3711_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_upperBound_3709_);
v___x_3723_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_array_push(v_b_3707_, v_val_3713_);
v_a_3706_ = v___x_3723_;
v_b_3707_ = v___x_3724_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3731_, lean_object* v_f_3732_, lean_object* v_xs_3733_, lean_object* v_k_3734_, lean_object* v_acc_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v___x_3739_; 
v___x_3739_ = lean_nat_dec_lt(v_k_3734_, v_n_3731_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec(v_k_3734_);
lean_dec_ref(v_f_3732_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v_acc_3735_);
lean_ctor_set(v___x_3740_, 1, v___y_3736_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
return v___x_3741_;
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_array_fget_borrowed(v_xs_3733_, v_k_3734_);
lean_inc_ref(v_f_3732_);
lean_inc_ref(v___y_3737_);
lean_inc(v___x_3742_);
v___x_3743_ = lean_apply_4(v_f_3732_, v___x_3742_, v___y_3736_, v___y_3737_, lean_box(0));
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v_fst_3745_; lean_object* v_snd_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v_fst_3745_ = lean_ctor_get(v_a_3744_, 0);
lean_inc(v_fst_3745_);
v_snd_3746_ = lean_ctor_get(v_a_3744_, 1);
lean_inc(v_snd_3746_);
lean_dec(v_a_3744_);
v___x_3747_ = lean_unsigned_to_nat(1u);
v___x_3748_ = lean_nat_add(v_k_3734_, v___x_3747_);
lean_dec(v_k_3734_);
v___x_3749_ = lean_array_push(v_acc_3735_, v_fst_3745_);
v_k_3734_ = v___x_3748_;
v_acc_3735_ = v___x_3749_;
v___y_3736_ = v_snd_3746_;
goto _start;
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec_ref(v_acc_3735_);
lean_dec(v_k_3734_);
lean_dec_ref(v_f_3732_);
v_a_3751_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3743_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3743_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3759_, lean_object* v_f_3760_, lean_object* v_xs_3761_, lean_object* v_k_3762_, lean_object* v_acc_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3759_, v_f_3760_, v_xs_3761_, v_k_3762_, v_acc_3763_, v___y_3764_, v___y_3765_);
lean_dec_ref(v___y_3765_);
lean_dec_ref(v_xs_3761_);
lean_dec(v_n_3759_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3768_, lean_object* v_fst_3769_, lean_object* v___x_3770_, lean_object* v_leanOpts_3771_, lean_object* v_a_3772_, lean_object* v_b_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
uint8_t v___x_3780_; 
v___x_3780_ = lean_nat_dec_lt(v_a_3772_, v_upperBound_3768_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
lean_dec(v_a_3772_);
lean_dec_ref(v_leanOpts_3771_);
v___x_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3781_, 0, v_b_3773_);
lean_ctor_set(v___x_3781_, 1, v___y_3774_);
v___x_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
return v___x_3782_;
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = lean_array_fget_borrowed(v_fst_3769_, v_a_3772_);
lean_inc(v___x_3783_);
v___x_3784_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3783_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3859_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3859_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3859_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v_snd_3789_; lean_object* v___x_3790_; lean_object* v_opts_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v_snd_3789_ = lean_ctor_get(v_a_3785_, 1);
lean_inc(v_snd_3789_);
lean_dec(v_a_3785_);
v___x_3790_ = lean_array_fget_borrowed(v___x_3770_, v_a_3772_);
v_opts_3791_ = lean_ctor_get(v___x_3790_, 4);
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3771_);
lean_inc(v_opts_3791_);
lean_inc(v___x_3783_);
v___x_3794_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3773_, v___x_3783_, v_opts_3791_, v_leanOpts_3771_, v___x_3780_, v___x_3793_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v_a_3796_; lean_object* v_snd_3798_; lean_object* v___x_3802_; uint8_t v___x_3803_; 
lean_del_object(v___x_3787_);
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
v_a_3796_ = lean_ctor_get(v___x_3794_, 1);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3794_, 2);
v___x_3802_ = lean_array_get_size(v_a_3796_);
v___x_3803_ = lean_nat_dec_lt(v___x_3792_, v___x_3802_);
if (v___x_3803_ == 0)
{
lean_dec(v_a_3796_);
v_snd_3798_ = v_snd_3789_;
goto v___jp_3797_;
}
else
{
lean_object* v___x_3804_; uint8_t v___x_3805_; 
v___x_3804_ = lean_box(0);
v___x_3805_ = lean_nat_dec_le(v___x_3802_, v___x_3802_);
if (v___x_3805_ == 0)
{
if (v___x_3803_ == 0)
{
lean_dec(v_a_3796_);
v_snd_3798_ = v_snd_3789_;
goto v___jp_3797_;
}
else
{
size_t v___x_3806_; size_t v___x_3807_; lean_object* v___x_3808_; 
v___x_3806_ = ((size_t)0ULL);
v___x_3807_ = lean_usize_of_nat(v___x_3802_);
v___x_3808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3796_, v___x_3806_, v___x_3807_, v___x_3804_, v___y_3775_);
lean_dec(v_a_3796_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_dec_ref_known(v___x_3808_, 1);
v_snd_3798_ = v_snd_3789_;
goto v___jp_3797_;
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_a_3795_);
lean_dec(v_snd_3789_);
lean_dec(v_a_3772_);
lean_dec_ref(v_leanOpts_3771_);
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3808_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3808_);
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
else
{
size_t v___x_3817_; size_t v___x_3818_; lean_object* v___x_3819_; 
v___x_3817_ = ((size_t)0ULL);
v___x_3818_ = lean_usize_of_nat(v___x_3802_);
v___x_3819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3796_, v___x_3817_, v___x_3818_, v___x_3804_, v___y_3775_);
lean_dec(v_a_3796_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_dec_ref_known(v___x_3819_, 1);
v_snd_3798_ = v_snd_3789_;
goto v___jp_3797_;
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v_a_3795_);
lean_dec(v_snd_3789_);
lean_dec(v_a_3772_);
lean_dec_ref(v_leanOpts_3771_);
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3819_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
v___jp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = lean_unsigned_to_nat(1u);
v___x_3800_ = lean_nat_add(v_a_3772_, v___x_3799_);
lean_dec(v_a_3772_);
v_a_3772_ = v___x_3800_;
v_b_3773_ = v_a_3795_;
v___y_3774_ = v_snd_3798_;
goto _start;
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
lean_dec(v_snd_3789_);
lean_dec(v_a_3772_);
lean_dec_ref(v_leanOpts_3771_);
v_a_3828_ = lean_ctor_get(v___x_3794_, 1);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3794_, 2);
v___x_3829_ = lean_array_get_size(v_a_3828_);
v___x_3830_ = lean_nat_dec_lt(v___x_3792_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
lean_dec(v_a_3828_);
v___x_3831_ = lean_box(0);
if (v_isShared_3788_ == 0)
{
lean_ctor_set_tag(v___x_3787_, 1);
lean_ctor_set(v___x_3787_, 0, v___x_3831_);
v___x_3833_ = v___x_3787_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
else
{
lean_object* v___x_3835_; uint8_t v___x_3836_; 
lean_del_object(v___x_3787_);
v___x_3835_ = lean_box(0);
v___x_3836_ = lean_nat_dec_le(v___x_3829_, v___x_3829_);
if (v___x_3836_ == 0)
{
if (v___x_3830_ == 0)
{
lean_dec(v_a_3828_);
goto v___jp_3777_;
}
else
{
size_t v___x_3837_; size_t v___x_3838_; lean_object* v___x_3839_; 
v___x_3837_ = ((size_t)0ULL);
v___x_3838_ = lean_usize_of_nat(v___x_3829_);
v___x_3839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3828_, v___x_3837_, v___x_3838_, v___x_3835_, v___y_3775_);
lean_dec(v_a_3828_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_dec_ref_known(v___x_3839_, 1);
goto v___jp_3777_;
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
else
{
size_t v___x_3848_; size_t v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = ((size_t)0ULL);
v___x_3849_ = lean_usize_of_nat(v___x_3829_);
v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3828_, v___x_3848_, v___x_3849_, v___x_3835_, v___y_3775_);
lean_dec(v_a_3828_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_dec_ref_known(v___x_3850_, 1);
goto v___jp_3777_;
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3850_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3850_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
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
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_b_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_leanOpts_3771_);
v_a_3860_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3784_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3784_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
v___jp_3777_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_3868_, lean_object* v_fst_3869_, lean_object* v___x_3870_, lean_object* v_leanOpts_3871_, lean_object* v_a_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_3868_, v_fst_3869_, v___x_3870_, v_leanOpts_3871_, v_a_3872_, v_b_3873_, v___y_3874_, v___y_3875_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___x_3870_);
lean_dec_ref(v_fst_3869_);
lean_dec(v_upperBound_3868_);
return v_res_3877_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_3878_, lean_object* v_x_3879_){
_start:
{
lean_object* v_baseName_3880_; lean_object* v_name_3881_; uint8_t v___x_3882_; 
v_baseName_3880_ = lean_ctor_get(v_x_3879_, 1);
v_name_3881_ = lean_ctor_get(v___x_3878_, 0);
v___x_3882_ = lean_name_eq(v_baseName_3880_, v_name_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_3883_, lean_object* v_x_3884_){
_start:
{
uint8_t v_res_3885_; lean_object* v_r_3886_; 
v_res_3885_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_3883_, v_x_3884_);
lean_dec_ref(v_x_3884_);
lean_dec_ref(v___x_3883_);
v_r_3886_ = lean_box(v_res_3885_);
return v_r_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_3887_, lean_object* v_leanOpts_3888_, uint8_t v_reconfigure_3889_, lean_object* v_as_3890_, size_t v_i_3891_, size_t v_stop_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_usize_dec_eq(v_i_3891_, v_stop_3892_);
if (v___x_3900_ == 0)
{
lean_object* v_ws_3901_; lean_object* v_depIdxs_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_4017_; 
v_ws_3901_ = lean_ctor_get(v_b_3893_, 0);
v_depIdxs_3902_ = lean_ctor_get(v_b_3893_, 1);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_b_3893_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_3904_ = v_b_3893_;
v_isShared_3905_ = v_isSharedCheck_4017_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_depIdxs_3902_);
lean_inc(v_ws_3901_);
lean_dec(v_b_3893_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_4017_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v_packages_3906_; size_t v___x_3907_; size_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___f_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_packages_3906_ = lean_ctor_get(v_ws_3901_, 4);
v___x_3907_ = ((size_t)1ULL);
v___x_3908_ = lean_usize_sub(v_i_3891_, v___x_3907_);
v___x_3909_ = lean_array_uget_borrowed(v_as_3890_, v___x_3908_);
lean_inc(v___x_3909_);
v___f_3910_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3910_, 0, v___x_3909_);
v___x_3911_ = lean_unsigned_to_nat(0u);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3910_, v_packages_3906_, v___x_3911_);
if (lean_obj_tag(v___x_3912_) == 1)
{
lean_object* v_val_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
v_val_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_val_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = lean_array_push(v_depIdxs_3902_, v_val_3913_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 1, v___x_3914_);
v___x_3916_ = v___x_3904_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_ws_3901_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
v_i_3891_ = v___x_3908_;
v_b_3893_ = v___x_3916_;
goto _start;
}
}
else
{
lean_object* v_baseName_3919_; lean_object* v_name_3920_; lean_object* v_opts_3921_; uint8_t v___x_3922_; 
lean_inc_ref(v_packages_3906_);
lean_dec(v___x_3912_);
v_baseName_3919_ = lean_ctor_get(v_pkg_3887_, 1);
v_name_3920_ = lean_ctor_get(v___x_3909_, 0);
v_opts_3921_ = lean_ctor_get(v___x_3909_, 4);
v___x_3922_ = lean_name_eq(v_baseName_3919_, v_name_3920_);
if (v___x_3922_ == 0)
{
lean_object* v___x_3923_; 
lean_inc_ref(v___y_3895_);
lean_inc_ref(v_ws_3901_);
lean_inc(v___x_3909_);
lean_inc_ref(v_pkg_3887_);
v___x_3923_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_3887_, v___x_3909_, v_ws_3901_, v___y_3894_, v___y_3895_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_4000_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_4000_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_4000_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v_fst_3928_; lean_object* v_snd_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_fst_3928_ = lean_ctor_get(v_a_3924_, 0);
lean_inc(v_fst_3928_);
v_snd_3929_ = lean_ctor_get(v_a_3924_, 1);
lean_inc(v_snd_3929_);
lean_dec(v_a_3924_);
v___x_3930_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3888_);
lean_inc(v_opts_3921_);
v___x_3931_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_3901_, v_fst_3928_, v_opts_3921_, v_leanOpts_3888_, v_reconfigure_3889_, v___x_3930_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v_a_3933_; lean_object* v_wsIdx_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
lean_del_object(v___x_3926_);
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
v_a_3933_ = lean_ctor_get(v___x_3931_, 1);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3931_, 2);
v_wsIdx_3934_ = lean_array_get_size(v_packages_3906_);
lean_dec_ref(v_packages_3906_);
v___x_3935_ = lean_array_push(v_depIdxs_3902_, v_wsIdx_3934_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 1, v___x_3935_);
lean_ctor_set(v___x_3904_, 0, v_a_3932_);
v___x_3937_ = v___x_3904_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3932_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3938_ = lean_array_get_size(v_a_3933_);
v___x_3939_ = lean_nat_dec_lt(v___x_3911_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_dec(v_a_3933_);
v_i_3891_ = v___x_3908_;
v_b_3893_ = v___x_3937_;
v___y_3894_ = v_snd_3929_;
goto _start;
}
else
{
lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3941_ = lean_box(0);
v___x_3942_ = lean_nat_dec_le(v___x_3938_, v___x_3938_);
if (v___x_3942_ == 0)
{
if (v___x_3939_ == 0)
{
lean_dec(v_a_3933_);
v_i_3891_ = v___x_3908_;
v_b_3893_ = v___x_3937_;
v___y_3894_ = v_snd_3929_;
goto _start;
}
else
{
size_t v___x_3944_; size_t v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = ((size_t)0ULL);
v___x_3945_ = lean_usize_of_nat(v___x_3938_);
v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3933_, v___x_3944_, v___x_3945_, v___x_3941_, v___y_3895_);
lean_dec(v_a_3933_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_dec_ref_known(v___x_3946_, 1);
v_i_3891_ = v___x_3908_;
v_b_3893_ = v___x_3937_;
v___y_3894_ = v_snd_3929_;
goto _start;
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec_ref(v___x_3937_);
lean_dec(v_snd_3929_);
lean_dec_ref(v_leanOpts_3888_);
lean_dec_ref(v_pkg_3887_);
v_a_3948_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3946_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3946_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
else
{
size_t v___x_3956_; size_t v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = ((size_t)0ULL);
v___x_3957_ = lean_usize_of_nat(v___x_3938_);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3933_, v___x_3956_, v___x_3957_, v___x_3941_, v___y_3895_);
lean_dec(v_a_3933_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_dec_ref_known(v___x_3958_, 1);
v_i_3891_ = v___x_3908_;
v_b_3893_ = v___x_3937_;
v___y_3894_ = v_snd_3929_;
goto _start;
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec_ref(v___x_3937_);
lean_dec(v_snd_3929_);
lean_dec_ref(v_leanOpts_3888_);
lean_dec_ref(v_pkg_3887_);
v_a_3960_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3958_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3958_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
lean_dec(v_snd_3929_);
lean_dec_ref(v_packages_3906_);
lean_del_object(v___x_3904_);
lean_dec_ref(v_depIdxs_3902_);
lean_dec_ref(v_leanOpts_3888_);
lean_dec_ref(v_pkg_3887_);
v_a_3969_ = lean_ctor_get(v___x_3931_, 1);
lean_inc(v_a_3969_);
lean_dec_ref_known(v___x_3931_, 2);
v___x_3970_ = lean_array_get_size(v_a_3969_);
v___x_3971_ = lean_nat_dec_lt(v___x_3911_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
lean_dec(v_a_3969_);
v___x_3972_ = lean_box(0);
if (v_isShared_3927_ == 0)
{
lean_ctor_set_tag(v___x_3926_, 1);
lean_ctor_set(v___x_3926_, 0, v___x_3972_);
v___x_3974_ = v___x_3926_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
else
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
lean_del_object(v___x_3926_);
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_nat_dec_le(v___x_3970_, v___x_3970_);
if (v___x_3977_ == 0)
{
if (v___x_3971_ == 0)
{
lean_dec(v_a_3969_);
goto v___jp_3897_;
}
else
{
size_t v___x_3978_; size_t v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = lean_usize_of_nat(v___x_3970_);
v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3969_, v___x_3978_, v___x_3979_, v___x_3976_, v___y_3895_);
lean_dec(v_a_3969_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_dec_ref_known(v___x_3980_, 1);
goto v___jp_3897_;
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
else
{
size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = lean_usize_of_nat(v___x_3970_);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3969_, v___x_3989_, v___x_3990_, v___x_3976_, v___y_3895_);
lean_dec(v_a_3969_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_dec_ref_known(v___x_3991_, 1);
goto v___jp_3897_;
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3991_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3991_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
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
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v_packages_3906_);
lean_del_object(v___x_3904_);
lean_dec_ref(v_depIdxs_3902_);
lean_dec_ref(v_ws_3901_);
lean_dec_ref(v_leanOpts_3888_);
lean_dec_ref(v_pkg_3887_);
v_a_4001_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3923_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3923_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; uint8_t v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_inc(v_baseName_3919_);
lean_dec_ref(v_packages_3906_);
lean_del_object(v___x_3904_);
lean_dec_ref(v_depIdxs_3902_);
lean_dec_ref(v_ws_3901_);
lean_dec(v___y_3894_);
lean_dec_ref(v_leanOpts_3888_);
lean_dec_ref(v_pkg_3887_);
v___x_4009_ = l_Lean_Name_toString(v_baseName_3919_, v___x_3900_);
v___x_4010_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4011_ = lean_string_append(v___x_4009_, v___x_4010_);
v___x_4012_ = 3;
v___x_4013_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set_uint8(v___x_4013_, sizeof(void*)*1, v___x_4012_);
lean_inc_ref(v___y_3895_);
v___x_4014_ = lean_apply_2(v___y_3895_, v___x_4013_, lean_box(0));
v___x_4015_ = lean_box(0);
v___x_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
}
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec_ref(v_leanOpts_3888_);
lean_dec_ref(v_pkg_3887_);
v___x_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4018_, 0, v_b_3893_);
lean_ctor_set(v___x_4018_, 1, v___y_3894_);
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4018_);
return v___x_4019_;
}
v___jp_3897_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4020_, lean_object* v_leanOpts_4021_, lean_object* v_reconfigure_4022_, lean_object* v_as_4023_, lean_object* v_i_4024_, lean_object* v_stop_4025_, lean_object* v_b_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
uint8_t v_reconfigure_boxed_4030_; size_t v_i_boxed_4031_; size_t v_stop_boxed_4032_; lean_object* v_res_4033_; 
v_reconfigure_boxed_4030_ = lean_unbox(v_reconfigure_4022_);
v_i_boxed_4031_ = lean_unbox_usize(v_i_4024_);
lean_dec(v_i_4024_);
v_stop_boxed_4032_ = lean_unbox_usize(v_stop_4025_);
lean_dec(v_stop_4025_);
v_res_4033_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4020_, v_leanOpts_4021_, v_reconfigure_boxed_4030_, v_as_4023_, v_i_boxed_4031_, v_stop_boxed_4032_, v_b_4026_, v___y_4027_, v___y_4028_);
lean_dec_ref(v___y_4028_);
lean_dec_ref(v_as_4023_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4034_, uint8_t v_reconfigure_4035_, lean_object* v_ws_4036_, lean_object* v_i_4037_, lean_object* v_next_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_packages_4042_; lean_object* v_pkg_4043_; lean_object* v_ws_4045_; lean_object* v_depIdxs_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v_____x_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v_depConfigs_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v_s_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; 
v_packages_4042_ = lean_ctor_get(v_ws_4036_, 4);
v_pkg_4043_ = lean_array_fget(v_packages_4042_, v_i_4037_);
lean_dec(v_i_4037_);
v_depConfigs_4064_ = lean_ctor_get(v_pkg_4043_, 12);
v___x_4065_ = lean_array_get_size(v_depConfigs_4064_);
v___x_4066_ = lean_mk_empty_array_with_capacity(v___x_4065_);
lean_inc_ref(v___x_4066_);
lean_inc_ref(v_ws_4036_);
v_s_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4067_, 0, v_ws_4036_);
lean_ctor_set(v_s_4067_, 1, v___x_4066_);
v___x_4068_ = lean_unsigned_to_nat(0u);
v___x_4069_ = lean_nat_dec_le(v___x_4065_, v___x_4065_);
if (v___x_4069_ == 0)
{
uint8_t v___x_4070_; 
v___x_4070_ = lean_nat_dec_lt(v___x_4068_, v___x_4065_);
if (v___x_4070_ == 0)
{
lean_object* v_ws_4071_; lean_object* v_packages_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
lean_dec_ref_known(v_s_4067_, 2);
v_ws_4071_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4036_, v_pkg_4043_, v___x_4066_);
v_packages_4072_ = lean_ctor_get(v_ws_4071_, 4);
lean_inc_ref(v_packages_4072_);
v___x_4073_ = lean_array_get_size(v_packages_4072_);
lean_dec_ref(v_packages_4072_);
v___x_4074_ = lean_nat_dec_lt(v_next_4038_, v___x_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec(v_next_4038_);
lean_dec_ref(v_leanOpts_4034_);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v_ws_4071_);
lean_ctor_set(v___x_4075_, 1, v___y_4039_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_unsigned_to_nat(1u);
v___x_4078_ = lean_nat_add(v_next_4038_, v___x_4077_);
v_ws_4036_ = v_ws_4071_;
v_i_4037_ = v_next_4038_;
v_next_4038_ = v___x_4078_;
goto _start;
}
}
else
{
size_t v___x_4080_; size_t v___x_4081_; lean_object* v___x_4082_; 
lean_dec_ref(v___x_4066_);
lean_dec_ref(v_ws_4036_);
v___x_4080_ = lean_usize_of_nat(v___x_4065_);
v___x_4081_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4034_);
lean_inc(v_pkg_4043_);
v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4043_, v_leanOpts_4034_, v_reconfigure_4035_, v_depConfigs_4064_, v___x_4080_, v___x_4081_, v_s_4067_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v_fst_4084_; lean_object* v_snd_4085_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v_fst_4084_ = lean_ctor_get(v_a_4083_, 0);
lean_inc(v_fst_4084_);
v_snd_4085_ = lean_ctor_get(v_a_4083_, 1);
lean_inc(v_snd_4085_);
lean_dec(v_a_4083_);
v_____x_4059_ = v_fst_4084_;
v___y_4060_ = v_snd_4085_;
v___y_4061_ = v___y_4040_;
goto v___jp_4058_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_pkg_4043_);
lean_dec(v_next_4038_);
lean_dec_ref(v_leanOpts_4034_);
v_a_4086_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4082_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4082_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
else
{
uint8_t v___x_4094_; 
v___x_4094_ = lean_nat_dec_lt(v___x_4068_, v___x_4065_);
if (v___x_4094_ == 0)
{
lean_dec_ref_known(v_s_4067_, 2);
v_ws_4045_ = v_ws_4036_;
v_depIdxs_4046_ = v___x_4066_;
v___y_4047_ = v___y_4039_;
v___y_4048_ = v___y_4040_;
goto v___jp_4044_;
}
else
{
size_t v___x_4095_; size_t v___x_4096_; lean_object* v___x_4097_; 
lean_dec_ref(v___x_4066_);
lean_dec_ref(v_ws_4036_);
v___x_4095_ = lean_usize_of_nat(v___x_4065_);
v___x_4096_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4034_);
lean_inc(v_pkg_4043_);
v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4043_, v_leanOpts_4034_, v_reconfigure_4035_, v_depConfigs_4064_, v___x_4095_, v___x_4096_, v_s_4067_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v_fst_4099_; lean_object* v_snd_4100_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4097_, 1);
v_fst_4099_ = lean_ctor_get(v_a_4098_, 0);
lean_inc(v_fst_4099_);
v_snd_4100_ = lean_ctor_get(v_a_4098_, 1);
lean_inc(v_snd_4100_);
lean_dec(v_a_4098_);
v_____x_4059_ = v_fst_4099_;
v___y_4060_ = v_snd_4100_;
v___y_4061_ = v___y_4040_;
goto v___jp_4058_;
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v_pkg_4043_);
lean_dec(v_next_4038_);
lean_dec_ref(v_leanOpts_4034_);
v_a_4101_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4097_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4097_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
v___jp_4044_:
{
lean_object* v_ws_4049_; lean_object* v_packages_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v_ws_4049_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4045_, v_pkg_4043_, v_depIdxs_4046_);
v_packages_4050_ = lean_ctor_get(v_ws_4049_, 4);
lean_inc_ref(v_packages_4050_);
v___x_4051_ = lean_array_get_size(v_packages_4050_);
lean_dec_ref(v_packages_4050_);
v___x_4052_ = lean_nat_dec_lt(v_next_4038_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_dec(v_next_4038_);
lean_dec_ref(v_leanOpts_4034_);
v___x_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4053_, 0, v_ws_4049_);
lean_ctor_set(v___x_4053_, 1, v___y_4047_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
return v___x_4054_;
}
else
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = lean_unsigned_to_nat(1u);
v___x_4056_ = lean_nat_add(v_next_4038_, v___x_4055_);
v_ws_4036_ = v_ws_4049_;
v_i_4037_ = v_next_4038_;
v_next_4038_ = v___x_4056_;
v___y_4039_ = v___y_4047_;
v___y_4040_ = v___y_4048_;
goto _start;
}
}
v___jp_4058_:
{
lean_object* v_ws_4062_; lean_object* v_depIdxs_4063_; 
v_ws_4062_ = lean_ctor_get(v_____x_4059_, 0);
lean_inc_ref(v_ws_4062_);
v_depIdxs_4063_ = lean_ctor_get(v_____x_4059_, 1);
lean_inc_ref(v_depIdxs_4063_);
lean_dec_ref(v_____x_4059_);
v_ws_4045_ = v_ws_4062_;
v_depIdxs_4046_ = v_depIdxs_4063_;
v___y_4047_ = v___y_4060_;
v___y_4048_ = v___y_4061_;
goto v___jp_4044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4109_, lean_object* v_reconfigure_4110_, lean_object* v_ws_4111_, lean_object* v_i_4112_, lean_object* v_next_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v_reconfigure_boxed_4117_; lean_object* v_res_4118_; 
v_reconfigure_boxed_4117_ = lean_unbox(v_reconfigure_4110_);
v_res_4118_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4109_, v_reconfigure_boxed_4117_, v_ws_4111_, v_i_4112_, v_next_4113_, v___y_4114_, v___y_4115_);
lean_dec_ref(v___y_4115_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4121_, lean_object* v_toUpdate_4122_, lean_object* v_leanOpts_4123_, uint8_t v_updateToolchain_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = lean_box(1);
v___x_4128_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4125_, v_ws_4121_, v_toUpdate_4122_, v___x_4127_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v_snd_4130_; uint8_t v___x_4131_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v_snd_4130_ = lean_ctor_get(v_a_4129_, 1);
lean_inc(v_snd_4130_);
lean_dec(v_a_4129_);
v___x_4131_ = 1;
if (v_updateToolchain_4124_ == 0)
{
lean_object* v_packages_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v_wsIdx_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v_packages_4132_ = lean_ctor_get(v_ws_4121_, 4);
v___x_4133_ = lean_unsigned_to_nat(0u);
v___x_4134_ = lean_array_fget_borrowed(v_packages_4132_, v___x_4133_);
v_wsIdx_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_wsIdx_4135_);
v___x_4136_ = lean_array_get_size(v_packages_4132_);
v___x_4137_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4123_, v___x_4131_, v_ws_4121_, v_wsIdx_4135_, v___x_4136_, v_snd_4130_, v_a_4125_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4155_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4155_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4155_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v_fst_4142_; lean_object* v_snd_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4154_; 
v_fst_4142_ = lean_ctor_get(v_a_4138_, 0);
v_snd_4143_ = lean_ctor_get(v_a_4138_, 1);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_a_4138_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4145_ = v_a_4138_;
v_isShared_4146_ = v_isSharedCheck_4154_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_snd_4143_);
lean_inc(v_fst_4142_);
lean_dec(v_a_4138_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4154_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4147_; lean_object* v___x_4149_; 
v___x_4147_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4142_);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v___x_4147_);
v___x_4149_ = v___x_4145_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4147_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_snd_4143_);
v___x_4149_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4151_; 
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v___x_4149_);
v___x_4151_ = v___x_4140_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
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
}
else
{
return v___x_4137_;
}
}
else
{
lean_object* v_packages_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v_depConfigs_4159_; lean_object* v___x_4160_; lean_object* v___f_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_packages_4156_ = lean_ctor_get(v_ws_4121_, 4);
lean_inc_ref(v_packages_4156_);
v___x_4157_ = lean_unsigned_to_nat(0u);
v___x_4158_ = lean_array_fget_borrowed(v_packages_4156_, v___x_4157_);
v_depConfigs_4159_ = lean_ctor_get(v___x_4158_, 12);
v___x_4160_ = lean_box(v_updateToolchain_4124_);
lean_inc_ref(v_ws_4121_);
lean_inc(v___x_4158_);
v___f_4161_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4161_, 0, v___x_4158_);
lean_closure_set(v___f_4161_, 1, v___x_4160_);
lean_closure_set(v___f_4161_, 2, v_ws_4121_);
v___x_4162_ = lean_array_get_size(v_depConfigs_4159_);
lean_inc_ref(v_depConfigs_4159_);
v___x_4163_ = l_Array_reverse___redArg(v_depConfigs_4159_);
v___x_4164_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4165_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4162_, v___f_4161_, v___x_4163_, v___x_4157_, v___x_4164_, v_snd_4130_, v_a_4125_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v_fst_4167_; lean_object* v_snd_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4240_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v_fst_4167_ = lean_ctor_get(v_a_4166_, 0);
v_snd_4168_ = lean_ctor_get(v_a_4166_, 1);
v_isSharedCheck_4240_ = !lean_is_exclusive(v_a_4166_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4170_ = v_a_4166_;
v_isShared_4171_ = v_isSharedCheck_4240_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_snd_4168_);
lean_inc(v_fst_4167_);
lean_dec(v_a_4166_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4240_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4172_; 
lean_inc_ref(v_ws_4121_);
v___x_4172_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4125_, v_ws_4121_, v_fst_4167_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v___x_4173_; 
lean_dec_ref_known(v___x_4172_, 1);
lean_inc_ref(v_leanOpts_4123_);
v___x_4173_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4162_, v_fst_4167_, v___x_4163_, v_leanOpts_4123_, v___x_4157_, v_ws_4121_, v_snd_4168_, v_a_4125_);
lean_dec_ref(v___x_4163_);
lean_dec(v_fst_4167_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4223_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4223_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4223_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v_fst_4178_; lean_object* v_snd_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4222_; 
v_fst_4178_ = lean_ctor_get(v_a_4174_, 0);
v_snd_4179_ = lean_ctor_get(v_a_4174_, 1);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_a_4174_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4181_ = v_a_4174_;
v_isShared_4182_ = v_isSharedCheck_4222_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_snd_4179_);
lean_inc(v_fst_4178_);
lean_dec(v_a_4174_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4222_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v_packages_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4189_; 
v_packages_4183_ = lean_ctor_get(v_fst_4178_, 4);
v___x_4184_ = lean_array_get_size(v_packages_4156_);
lean_dec_ref(v_packages_4156_);
v___x_4185_ = lean_array_get_size(v_packages_4183_);
v___x_4186_ = lean_array_fget(v_packages_4183_, v___x_4157_);
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4184_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 1, v___x_4185_);
lean_ctor_set(v___x_4170_, 0, v___x_4187_);
v___x_4189_ = v___x_4170_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4187_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v___x_4185_);
v___x_4189_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v___x_4190_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4189_, v___x_4164_);
v___x_4191_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4178_, v___x_4186_, v___x_4190_);
v___x_4192_ = lean_nat_dec_eq(v___x_4184_, v___x_4185_);
if (v___x_4192_ == 0)
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_del_object(v___x_4181_);
lean_del_object(v___x_4176_);
v___x_4193_ = lean_unsigned_to_nat(1u);
v___x_4194_ = lean_nat_add(v___x_4184_, v___x_4193_);
v___x_4195_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4123_, v___x_4131_, v___x_4191_, v___x_4184_, v___x_4194_, v_snd_4179_, v_a_4125_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4213_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4213_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4213_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v_fst_4200_; lean_object* v_snd_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4212_; 
v_fst_4200_ = lean_ctor_get(v_a_4196_, 0);
v_snd_4201_ = lean_ctor_get(v_a_4196_, 1);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_a_4196_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4203_ = v_a_4196_;
v_isShared_4204_ = v_isSharedCheck_4212_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_snd_4201_);
lean_inc(v_fst_4200_);
lean_dec(v_a_4196_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4212_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4205_; lean_object* v___x_4207_; 
v___x_4205_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4200_);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4205_);
v___x_4207_ = v___x_4203_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4205_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v_snd_4201_);
v___x_4207_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_object* v___x_4209_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4207_);
v___x_4209_ = v___x_4198_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4207_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
}
else
{
return v___x_4195_;
}
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
lean_dec_ref(v_leanOpts_4123_);
v___x_4214_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4191_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___x_4214_);
v___x_4216_ = v___x_4181_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_snd_4179_);
v___x_4216_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4218_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4216_);
v___x_4218_ = v___x_4176_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_del_object(v___x_4170_);
lean_dec_ref(v_packages_4156_);
lean_dec_ref(v_leanOpts_4123_);
v_a_4224_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4173_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4173_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_del_object(v___x_4170_);
lean_dec(v_snd_4168_);
lean_dec(v_fst_4167_);
lean_dec_ref(v___x_4163_);
lean_dec_ref(v_packages_4156_);
lean_dec_ref(v_leanOpts_4123_);
lean_dec_ref(v_ws_4121_);
v_a_4232_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4172_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4172_);
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
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v___x_4163_);
lean_dec_ref(v_packages_4156_);
lean_dec_ref(v_leanOpts_4123_);
lean_dec_ref(v_ws_4121_);
v_a_4241_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4165_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4165_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref(v_leanOpts_4123_);
lean_dec_ref(v_ws_4121_);
v_a_4249_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4128_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4128_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4257_, lean_object* v_toUpdate_4258_, lean_object* v_leanOpts_4259_, lean_object* v_updateToolchain_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
uint8_t v_updateToolchain_boxed_4263_; lean_object* v_res_4264_; 
v_updateToolchain_boxed_4263_ = lean_unbox(v_updateToolchain_4260_);
v_res_4264_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4257_, v_toUpdate_4258_, v_leanOpts_4259_, v_updateToolchain_boxed_4263_, v_a_4261_);
lean_dec_ref(v_a_4261_);
lean_dec(v_toUpdate_4258_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4265_, uint8_t v_reconfigure_4266_, lean_object* v_ws_4267_, lean_object* v_i_4268_, lean_object* v_i__lt_4269_, lean_object* v_next_4270_, lean_object* v_lt__next_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4265_, v_reconfigure_4266_, v_ws_4267_, v_i_4268_, v_next_4270_, v___y_4272_, v___y_4273_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4276_, lean_object* v_reconfigure_4277_, lean_object* v_ws_4278_, lean_object* v_i_4279_, lean_object* v_i__lt_4280_, lean_object* v_next_4281_, lean_object* v_lt__next_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v_reconfigure_boxed_4286_; lean_object* v_res_4287_; 
v_reconfigure_boxed_4286_ = lean_unbox(v_reconfigure_4277_);
v_res_4287_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4276_, v_reconfigure_boxed_4286_, v_ws_4278_, v_i_4279_, v_i__lt_4280_, v_next_4281_, v_lt__next_4282_, v___y_4283_, v___y_4284_);
lean_dec_ref(v___y_4284_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4288_, lean_object* v_00_u03b2_4289_, lean_object* v_n_4290_, lean_object* v_f_4291_, lean_object* v_xs_4292_, lean_object* v_k_4293_, lean_object* v_h_4294_, lean_object* v_acc_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4290_, v_f_4291_, v_xs_4292_, v_k_4293_, v_acc_4295_, v___y_4296_, v___y_4297_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4300_, lean_object* v_00_u03b2_4301_, lean_object* v_n_4302_, lean_object* v_f_4303_, lean_object* v_xs_4304_, lean_object* v_k_4305_, lean_object* v_h_4306_, lean_object* v_acc_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4300_, v_00_u03b2_4301_, v_n_4302_, v_f_4303_, v_xs_4304_, v_k_4305_, v_h_4306_, v_acc_4307_, v___y_4308_, v___y_4309_);
lean_dec_ref(v___y_4309_);
lean_dec_ref(v_xs_4304_);
lean_dec(v_n_4302_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4312_, lean_object* v_R_4313_, lean_object* v_a_4314_, lean_object* v_b_4315_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4314_, v_b_4315_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4317_, lean_object* v_fst_4318_, lean_object* v___x_4319_, lean_object* v_leanOpts_4320_, lean_object* v_inst_4321_, lean_object* v_R_4322_, lean_object* v_a_4323_, lean_object* v_b_4324_, lean_object* v_c_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4317_, v_fst_4318_, v___x_4319_, v_leanOpts_4320_, v_a_4323_, v_b_4324_, v___y_4326_, v___y_4327_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4330_, lean_object* v_fst_4331_, lean_object* v___x_4332_, lean_object* v_leanOpts_4333_, lean_object* v_inst_4334_, lean_object* v_R_4335_, lean_object* v_a_4336_, lean_object* v_b_4337_, lean_object* v_c_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4330_, v_fst_4331_, v___x_4332_, v_leanOpts_4333_, v_inst_4334_, v_R_4335_, v_a_4336_, v_b_4337_, v_c_4338_, v___y_4339_, v___y_4340_);
lean_dec_ref(v___y_4340_);
lean_dec_ref(v___x_4332_);
lean_dec_ref(v_fst_4331_);
lean_dec(v_upperBound_4330_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4343_, lean_object* v_pkg_4344_, lean_object* v_leanOpts_4345_, uint8_t v_reconfigure_4346_, lean_object* v_as_4347_, size_t v_i_4348_, size_t v_stop_4349_, lean_object* v_b_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___x_4354_; 
v___x_4354_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4344_, v_leanOpts_4345_, v_reconfigure_4346_, v_as_4347_, v_i_4348_, v_stop_4349_, v_b_4350_, v___y_4351_, v___y_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4355_, lean_object* v_pkg_4356_, lean_object* v_leanOpts_4357_, lean_object* v_reconfigure_4358_, lean_object* v_as_4359_, lean_object* v_i_4360_, lean_object* v_stop_4361_, lean_object* v_b_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
uint8_t v_reconfigure_boxed_4366_; size_t v_i_boxed_4367_; size_t v_stop_boxed_4368_; lean_object* v_res_4369_; 
v_reconfigure_boxed_4366_ = lean_unbox(v_reconfigure_4358_);
v_i_boxed_4367_ = lean_unbox_usize(v_i_4360_);
lean_dec(v_i_4360_);
v_stop_boxed_4368_ = lean_unbox_usize(v_stop_4361_);
lean_dec(v_stop_4361_);
v_res_4369_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4355_, v_pkg_4356_, v_leanOpts_4357_, v_reconfigure_boxed_4366_, v_as_4359_, v_i_boxed_4367_, v_stop_boxed_4368_, v_b_4362_, v___y_4363_, v___y_4364_);
lean_dec_ref(v___y_4364_);
lean_dec_ref(v_as_4359_);
lean_dec(v_start_4355_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4370_, lean_object* v_msg_4371_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4373_, lean_object* v_k_4374_, lean_object* v_v_4375_, lean_object* v_t_4376_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4374_, v_v_4375_, v_t_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4378_, lean_object* v_t_4379_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4378_, v_t_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4381_, lean_object* v_as_4382_, size_t v_i_4383_, size_t v_stop_4384_, lean_object* v_b_4385_){
_start:
{
lean_object* v___y_4387_; uint8_t v___x_4391_; 
v___x_4391_ = lean_usize_dec_eq(v_i_4383_, v_stop_4384_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; lean_object* v_baseName_4393_; lean_object* v_relConfigFile_4394_; lean_object* v_relManifestFile_4395_; lean_object* v___x_4396_; 
v___x_4392_ = lean_array_uget_borrowed(v_as_4382_, v_i_4383_);
v_baseName_4393_ = lean_ctor_get(v___x_4392_, 1);
v_relConfigFile_4394_ = lean_ctor_get(v___x_4392_, 8);
v_relManifestFile_4395_ = lean_ctor_get(v___x_4392_, 9);
v___x_4396_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4381_, v_baseName_4393_);
if (lean_obj_tag(v___x_4396_) == 0)
{
v___y_4387_ = v_b_4385_;
goto v___jp_4386_;
}
else
{
lean_object* v_val_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4418_; 
v_val_4397_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4399_ = v___x_4396_;
v_isShared_4400_ = v_isSharedCheck_4418_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_val_4397_);
lean_dec(v___x_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4418_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v_name_4401_; lean_object* v_scope_4402_; uint8_t v_inherited_4403_; lean_object* v_src_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4415_; 
v_name_4401_ = lean_ctor_get(v_val_4397_, 0);
v_scope_4402_ = lean_ctor_get(v_val_4397_, 1);
v_inherited_4403_ = lean_ctor_get_uint8(v_val_4397_, sizeof(void*)*5);
v_src_4404_ = lean_ctor_get(v_val_4397_, 4);
v_isSharedCheck_4415_ = !lean_is_exclusive(v_val_4397_);
if (v_isSharedCheck_4415_ == 0)
{
lean_object* v_unused_4416_; lean_object* v_unused_4417_; 
v_unused_4416_ = lean_ctor_get(v_val_4397_, 3);
lean_dec(v_unused_4416_);
v_unused_4417_ = lean_ctor_get(v_val_4397_, 2);
lean_dec(v_unused_4417_);
v___x_4406_ = v_val_4397_;
v_isShared_4407_ = v_isSharedCheck_4415_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_src_4404_);
lean_inc(v_scope_4402_);
lean_inc(v_name_4401_);
lean_dec(v_val_4397_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4415_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
lean_inc_ref(v_relManifestFile_4395_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v_relManifestFile_4395_);
v___x_4409_ = v___x_4399_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_relManifestFile_4395_);
v___x_4409_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
lean_object* v___x_4411_; 
lean_inc_ref(v_relConfigFile_4394_);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 3, v___x_4409_);
lean_ctor_set(v___x_4406_, 2, v_relConfigFile_4394_);
v___x_4411_ = v___x_4406_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_name_4401_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_scope_4402_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v_relConfigFile_4394_);
lean_ctor_set(v_reuseFailAlloc_4413_, 3, v___x_4409_);
lean_ctor_set(v_reuseFailAlloc_4413_, 4, v_src_4404_);
lean_ctor_set_uint8(v_reuseFailAlloc_4413_, sizeof(void*)*5, v_inherited_4403_);
v___x_4411_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4412_; 
v___x_4412_ = lean_array_push(v_b_4385_, v___x_4411_);
v___y_4387_ = v___x_4412_;
goto v___jp_4386_;
}
}
}
}
}
}
else
{
return v_b_4385_;
}
v___jp_4386_:
{
size_t v___x_4388_; size_t v___x_4389_; 
v___x_4388_ = ((size_t)1ULL);
v___x_4389_ = lean_usize_add(v_i_4383_, v___x_4388_);
v_i_4383_ = v___x_4389_;
v_b_4385_ = v___y_4387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4419_, lean_object* v_as_4420_, lean_object* v_i_4421_, lean_object* v_stop_4422_, lean_object* v_b_4423_){
_start:
{
size_t v_i_boxed_4424_; size_t v_stop_boxed_4425_; lean_object* v_res_4426_; 
v_i_boxed_4424_ = lean_unbox_usize(v_i_4421_);
lean_dec(v_i_4421_);
v_stop_boxed_4425_ = lean_unbox_usize(v_stop_4422_);
lean_dec(v_stop_4422_);
v_res_4426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4419_, v_as_4420_, v_i_boxed_4424_, v_stop_boxed_4425_, v_b_4423_);
lean_dec_ref(v_as_4420_);
lean_dec(v_entries_4419_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4427_, lean_object* v_entries_4428_){
_start:
{
lean_object* v_packages_4430_; lean_object* v___y_4432_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v_packages_4430_ = lean_ctor_get(v_ws_4427_, 4);
v___x_4447_ = lean_unsigned_to_nat(0u);
v___x_4448_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4449_ = lean_array_get_size(v_packages_4430_);
v___x_4450_ = lean_nat_dec_lt(v___x_4447_, v___x_4449_);
if (v___x_4450_ == 0)
{
v___y_4432_ = v___x_4448_;
goto v___jp_4431_;
}
else
{
uint8_t v___x_4451_; 
v___x_4451_ = lean_nat_dec_le(v___x_4449_, v___x_4449_);
if (v___x_4451_ == 0)
{
if (v___x_4450_ == 0)
{
v___y_4432_ = v___x_4448_;
goto v___jp_4431_;
}
else
{
size_t v___x_4452_; size_t v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = ((size_t)0ULL);
v___x_4453_ = lean_usize_of_nat(v___x_4449_);
v___x_4454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4428_, v_packages_4430_, v___x_4452_, v___x_4453_, v___x_4448_);
v___y_4432_ = v___x_4454_;
goto v___jp_4431_;
}
}
else
{
size_t v___x_4455_; size_t v___x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = ((size_t)0ULL);
v___x_4456_ = lean_usize_of_nat(v___x_4449_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4428_, v_packages_4430_, v___x_4455_, v___x_4456_, v___x_4448_);
v___y_4432_ = v___x_4457_;
goto v___jp_4431_;
}
}
v___jp_4431_:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v_config_4435_; lean_object* v_baseName_4436_; lean_object* v_dir_4437_; lean_object* v_relManifestFile_4438_; lean_object* v_toWorkspaceConfig_4439_; uint8_t v_fixedToolchain_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v_manifest_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4433_ = lean_unsigned_to_nat(0u);
v___x_4434_ = lean_array_fget_borrowed(v_packages_4430_, v___x_4433_);
v_config_4435_ = lean_ctor_get(v___x_4434_, 6);
v_baseName_4436_ = lean_ctor_get(v___x_4434_, 1);
v_dir_4437_ = lean_ctor_get(v___x_4434_, 4);
v_relManifestFile_4438_ = lean_ctor_get(v___x_4434_, 9);
v_toWorkspaceConfig_4439_ = lean_ctor_get(v_config_4435_, 0);
v_fixedToolchain_4440_ = lean_ctor_get_uint8(v_config_4435_, sizeof(void*)*27 + 6);
v___x_4441_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4439_);
v___x_4442_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4439_);
v___x_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
lean_inc(v_baseName_4436_);
v_manifest_4444_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4444_, 0, v_baseName_4436_);
lean_ctor_set(v_manifest_4444_, 1, v___x_4441_);
lean_ctor_set(v_manifest_4444_, 2, v___x_4443_);
lean_ctor_set(v_manifest_4444_, 3, v___y_4432_);
lean_ctor_set_uint8(v_manifest_4444_, sizeof(void*)*4, v_fixedToolchain_4440_);
lean_inc_ref(v_relManifestFile_4438_);
lean_inc_ref(v_dir_4437_);
v___x_4445_ = l_Lake_joinRelative(v_dir_4437_, v_relManifestFile_4438_);
v___x_4446_ = l_Lake_Manifest_save(v_manifest_4444_, v___x_4445_);
lean_dec_ref(v___x_4445_);
return v___x_4446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4458_, lean_object* v_entries_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4458_, v_entries_4459_);
lean_dec(v_entries_4459_);
lean_dec_ref(v_ws_4458_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4462_, lean_object* v_as_4463_, size_t v_i_4464_, size_t v_stop_4465_, lean_object* v_b_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v_a_4471_; lean_object* v___y_4476_; uint8_t v___x_4481_; 
v___x_4481_ = lean_usize_dec_eq(v_i_4464_, v_stop_4465_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_9317__overap_4484_; lean_object* v___x_4485_; 
v___x_4482_ = lean_unsigned_to_nat(0u);
v___x_4483_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_9317__overap_4484_ = lean_array_uget_borrowed(v_as_4463_, v_i_4464_);
lean_inc(v___x_9317__overap_4484_);
lean_inc(v___y_4467_);
lean_inc_ref(v_pkg_4462_);
v___x_4485_ = lean_apply_4(v___x_9317__overap_4484_, v_pkg_4462_, v___y_4467_, v___x_4483_, lean_box(0));
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v_a_4487_; lean_object* v___x_4488_; uint8_t v___x_4489_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
v_a_4487_ = lean_ctor_get(v___x_4485_, 1);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4485_, 2);
v___x_4488_ = lean_array_get_size(v_a_4487_);
v___x_4489_ = lean_nat_dec_lt(v___x_4482_, v___x_4488_);
if (v___x_4489_ == 0)
{
lean_dec(v_a_4487_);
v_a_4471_ = v_a_4486_;
goto v___jp_4470_;
}
else
{
lean_object* v___x_4490_; uint8_t v___x_4491_; 
v___x_4490_ = lean_box(0);
v___x_4491_ = lean_nat_dec_le(v___x_4488_, v___x_4488_);
if (v___x_4491_ == 0)
{
if (v___x_4489_ == 0)
{
lean_dec(v_a_4487_);
v_a_4471_ = v_a_4486_;
goto v___jp_4470_;
}
else
{
size_t v___x_4492_; size_t v___x_4493_; lean_object* v___x_4494_; 
v___x_4492_ = ((size_t)0ULL);
v___x_4493_ = lean_usize_of_nat(v___x_4488_);
v___x_4494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4487_, v___x_4492_, v___x_4493_, v___x_4490_, v___y_4468_);
lean_dec(v_a_4487_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_dec_ref_known(v___x_4494_, 1);
v_a_4471_ = v_a_4486_;
goto v___jp_4470_;
}
else
{
lean_dec(v_a_4486_);
v___y_4476_ = v___x_4494_;
goto v___jp_4475_;
}
}
}
else
{
size_t v___x_4495_; size_t v___x_4496_; lean_object* v___x_4497_; 
v___x_4495_ = ((size_t)0ULL);
v___x_4496_ = lean_usize_of_nat(v___x_4488_);
v___x_4497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4487_, v___x_4495_, v___x_4496_, v___x_4490_, v___y_4468_);
lean_dec(v_a_4487_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_dec_ref_known(v___x_4497_, 1);
v_a_4471_ = v_a_4486_;
goto v___jp_4470_;
}
else
{
lean_dec(v_a_4486_);
v___y_4476_ = v___x_4497_;
goto v___jp_4475_;
}
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4499_; uint8_t v___x_4500_; 
v_a_4498_ = lean_ctor_get(v___x_4485_, 1);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4485_, 2);
v___x_4499_ = lean_array_get_size(v_a_4498_);
v___x_4500_ = lean_nat_dec_lt(v___x_4482_, v___x_4499_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4501_; lean_object* v___x_4502_; 
lean_dec(v_a_4498_);
lean_dec_ref(v_pkg_4462_);
v___x_4501_ = lean_box(0);
v___x_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
return v___x_4502_;
}
else
{
lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4503_ = lean_box(0);
v___x_4504_ = lean_nat_dec_le(v___x_4499_, v___x_4499_);
if (v___x_4504_ == 0)
{
if (v___x_4500_ == 0)
{
lean_dec(v_a_4498_);
lean_dec_ref(v_pkg_4462_);
goto v___jp_4478_;
}
else
{
size_t v___x_4505_; size_t v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = ((size_t)0ULL);
v___x_4506_ = lean_usize_of_nat(v___x_4499_);
v___x_4507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4498_, v___x_4505_, v___x_4506_, v___x_4503_, v___y_4468_);
lean_dec(v_a_4498_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_dec_ref_known(v___x_4507_, 1);
lean_dec_ref(v_pkg_4462_);
goto v___jp_4478_;
}
else
{
v___y_4476_ = v___x_4507_;
goto v___jp_4475_;
}
}
}
else
{
size_t v___x_4508_; size_t v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = ((size_t)0ULL);
v___x_4509_ = lean_usize_of_nat(v___x_4499_);
v___x_4510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4498_, v___x_4508_, v___x_4509_, v___x_4503_, v___y_4468_);
lean_dec(v_a_4498_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_dec_ref_known(v___x_4510_, 1);
lean_dec_ref(v_pkg_4462_);
goto v___jp_4478_;
}
else
{
v___y_4476_ = v___x_4510_;
goto v___jp_4475_;
}
}
}
}
}
else
{
lean_object* v___x_4511_; 
lean_dec_ref(v_pkg_4462_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v_b_4466_);
return v___x_4511_;
}
v___jp_4470_:
{
size_t v___x_4472_; size_t v___x_4473_; 
v___x_4472_ = ((size_t)1ULL);
v___x_4473_ = lean_usize_add(v_i_4464_, v___x_4472_);
v_i_4464_ = v___x_4473_;
v_b_4466_ = v_a_4471_;
goto _start;
}
v___jp_4475_:
{
if (lean_obj_tag(v___y_4476_) == 0)
{
lean_object* v_a_4477_; 
v_a_4477_ = lean_ctor_get(v___y_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___y_4476_, 1);
v_a_4471_ = v_a_4477_;
goto v___jp_4470_;
}
else
{
lean_dec_ref(v_pkg_4462_);
return v___y_4476_;
}
}
v___jp_4478_:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = lean_box(0);
v___x_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4512_, lean_object* v_as_4513_, lean_object* v_i_4514_, lean_object* v_stop_4515_, lean_object* v_b_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
size_t v_i_boxed_4520_; size_t v_stop_boxed_4521_; lean_object* v_res_4522_; 
v_i_boxed_4520_ = lean_unbox_usize(v_i_4514_);
lean_dec(v_i_4514_);
v_stop_boxed_4521_ = lean_unbox_usize(v_stop_4515_);
lean_dec(v_stop_4515_);
v_res_4522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4512_, v_as_4513_, v_i_boxed_4520_, v_stop_boxed_4521_, v_b_4516_, v___y_4517_, v___y_4518_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v_as_4513_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v_baseName_4528_; lean_object* v_postUpdateHooks_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; 
v_baseName_4528_ = lean_ctor_get(v_pkg_4524_, 1);
v_postUpdateHooks_4529_ = lean_ctor_get(v_pkg_4524_, 20);
lean_inc_ref(v_postUpdateHooks_4529_);
v___x_4530_ = lean_array_get_size(v_postUpdateHooks_4529_);
v___x_4531_ = lean_unsigned_to_nat(0u);
v___x_4532_ = lean_nat_dec_eq(v___x_4530_, v___x_4531_);
if (v___x_4532_ == 0)
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
lean_inc(v_baseName_4528_);
v___x_4533_ = l_Lean_Name_toString(v_baseName_4528_, v___x_4532_);
v___x_4534_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4535_ = lean_string_append(v___x_4533_, v___x_4534_);
v___x_4536_ = 1;
v___x_4537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4537_, 0, v___x_4535_);
lean_ctor_set_uint8(v___x_4537_, sizeof(void*)*1, v___x_4536_);
lean_inc_ref(v_a_4526_);
v___x_4538_ = lean_apply_2(v_a_4526_, v___x_4537_, lean_box(0));
v___x_4539_ = lean_box(0);
v___x_4540_ = lean_nat_dec_lt(v___x_4531_, v___x_4530_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
lean_dec_ref(v_postUpdateHooks_4529_);
lean_dec_ref(v_pkg_4524_);
v___x_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4539_);
return v___x_4541_;
}
else
{
uint8_t v___x_4542_; 
v___x_4542_ = lean_nat_dec_le(v___x_4530_, v___x_4530_);
if (v___x_4542_ == 0)
{
if (v___x_4540_ == 0)
{
lean_object* v___x_4543_; 
lean_dec_ref(v_postUpdateHooks_4529_);
lean_dec_ref(v_pkg_4524_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4539_);
return v___x_4543_;
}
else
{
size_t v___x_4544_; size_t v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = ((size_t)0ULL);
v___x_4545_ = lean_usize_of_nat(v___x_4530_);
v___x_4546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4524_, v_postUpdateHooks_4529_, v___x_4544_, v___x_4545_, v___x_4539_, v_a_4525_, v_a_4526_);
lean_dec_ref(v_postUpdateHooks_4529_);
return v___x_4546_;
}
}
else
{
size_t v___x_4547_; size_t v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = ((size_t)0ULL);
v___x_4548_ = lean_usize_of_nat(v___x_4530_);
v___x_4549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4524_, v_postUpdateHooks_4529_, v___x_4547_, v___x_4548_, v___x_4539_, v_a_4525_, v_a_4526_);
lean_dec_ref(v_postUpdateHooks_4529_);
return v___x_4549_;
}
}
}
else
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
lean_dec_ref(v_postUpdateHooks_4529_);
lean_dec_ref(v_pkg_4524_);
v___x_4550_ = lean_box(0);
v___x_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
return v___x_4551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v_res_4556_; 
v_res_4556_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4552_, v_a_4553_, v_a_4554_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4557_, lean_object* v_ws_4558_, lean_object* v_toUpdate_4559_, lean_object* v_leanOpts_4560_, uint8_t v_updateToolchain_4561_){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = lean_box(1);
v___x_4564_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4557_, v_ws_4558_, v_toUpdate_4559_, v___x_4563_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v_a_4565_; lean_object* v_snd_4566_; uint8_t v___x_4567_; 
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
lean_inc(v_a_4565_);
lean_dec_ref_known(v___x_4564_, 1);
v_snd_4566_ = lean_ctor_get(v_a_4565_, 1);
lean_inc(v_snd_4566_);
lean_dec(v_a_4565_);
v___x_4567_ = 1;
if (v_updateToolchain_4561_ == 0)
{
lean_object* v_packages_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v_wsIdx_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v_packages_4568_ = lean_ctor_get(v_ws_4558_, 4);
v___x_4569_ = lean_unsigned_to_nat(0u);
v___x_4570_ = lean_array_fget_borrowed(v_packages_4568_, v___x_4569_);
v_wsIdx_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_wsIdx_4571_);
v___x_4572_ = lean_array_get_size(v_packages_4568_);
v___x_4573_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4560_, v___x_4567_, v_ws_4558_, v_wsIdx_4571_, v___x_4572_, v_snd_4566_, v_a_4557_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4591_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4576_ = v___x_4573_;
v_isShared_4577_ = v_isSharedCheck_4591_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4573_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4591_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_fst_4578_; lean_object* v_snd_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4590_; 
v_fst_4578_ = lean_ctor_get(v_a_4574_, 0);
v_snd_4579_ = lean_ctor_get(v_a_4574_, 1);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_a_4574_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4581_ = v_a_4574_;
v_isShared_4582_ = v_isSharedCheck_4590_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_snd_4579_);
lean_inc(v_fst_4578_);
lean_dec(v_a_4574_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4590_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; lean_object* v___x_4585_; 
v___x_4583_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4578_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 0, v___x_4583_);
v___x_4585_ = v___x_4581_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_snd_4579_);
v___x_4585_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4587_; 
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v___x_4585_);
v___x_4587_ = v___x_4576_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
else
{
return v___x_4573_;
}
}
else
{
lean_object* v_packages_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v_depConfigs_4595_; lean_object* v___x_4596_; lean_object* v___f_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v_packages_4592_ = lean_ctor_get(v_ws_4558_, 4);
lean_inc_ref(v_packages_4592_);
v___x_4593_ = lean_unsigned_to_nat(0u);
v___x_4594_ = lean_array_fget_borrowed(v_packages_4592_, v___x_4593_);
v_depConfigs_4595_ = lean_ctor_get(v___x_4594_, 12);
v___x_4596_ = lean_box(v_updateToolchain_4561_);
lean_inc_ref(v_ws_4558_);
lean_inc(v___x_4594_);
v___f_4597_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4597_, 0, v___x_4594_);
lean_closure_set(v___f_4597_, 1, v___x_4596_);
lean_closure_set(v___f_4597_, 2, v_ws_4558_);
v___x_4598_ = lean_array_get_size(v_depConfigs_4595_);
lean_inc_ref(v_depConfigs_4595_);
v___x_4599_ = l_Array_reverse___redArg(v_depConfigs_4595_);
v___x_4600_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4601_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4598_, v___f_4597_, v___x_4599_, v___x_4593_, v___x_4600_, v_snd_4566_, v_a_4557_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v_fst_4603_; lean_object* v_snd_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4676_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
lean_dec_ref_known(v___x_4601_, 1);
v_fst_4603_ = lean_ctor_get(v_a_4602_, 0);
v_snd_4604_ = lean_ctor_get(v_a_4602_, 1);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_a_4602_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4606_ = v_a_4602_;
v_isShared_4607_ = v_isSharedCheck_4676_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_snd_4604_);
lean_inc(v_fst_4603_);
lean_dec(v_a_4602_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4676_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4608_; 
lean_inc_ref(v_ws_4558_);
v___x_4608_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4557_, v_ws_4558_, v_fst_4603_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v___x_4609_; 
lean_dec_ref_known(v___x_4608_, 1);
lean_inc_ref(v_leanOpts_4560_);
v___x_4609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4598_, v_fst_4603_, v___x_4599_, v_leanOpts_4560_, v___x_4593_, v_ws_4558_, v_snd_4604_, v_a_4557_);
lean_dec_ref(v___x_4599_);
lean_dec(v_fst_4603_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4659_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4659_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4659_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v_fst_4614_; lean_object* v_snd_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4658_; 
v_fst_4614_ = lean_ctor_get(v_a_4610_, 0);
v_snd_4615_ = lean_ctor_get(v_a_4610_, 1);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_a_4610_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4617_ = v_a_4610_;
v_isShared_4618_ = v_isSharedCheck_4658_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_snd_4615_);
lean_inc(v_fst_4614_);
lean_dec(v_a_4610_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4658_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v_packages_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4625_; 
v_packages_4619_ = lean_ctor_get(v_fst_4614_, 4);
v___x_4620_ = lean_array_get_size(v_packages_4592_);
lean_dec_ref(v_packages_4592_);
v___x_4621_ = lean_array_get_size(v_packages_4619_);
v___x_4622_ = lean_array_fget(v_packages_4619_, v___x_4593_);
v___x_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4620_);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 1, v___x_4621_);
lean_ctor_set(v___x_4606_, 0, v___x_4623_);
v___x_4625_ = v___x_4606_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4623_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v___x_4621_);
v___x_4625_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; uint8_t v___x_4628_; 
v___x_4626_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4625_, v___x_4600_);
v___x_4627_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4614_, v___x_4622_, v___x_4626_);
v___x_4628_ = lean_nat_dec_eq(v___x_4620_, v___x_4621_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
lean_del_object(v___x_4617_);
lean_del_object(v___x_4612_);
v___x_4629_ = lean_unsigned_to_nat(1u);
v___x_4630_ = lean_nat_add(v___x_4620_, v___x_4629_);
v___x_4631_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4560_, v___x_4567_, v___x_4627_, v___x_4620_, v___x_4630_, v_snd_4615_, v_a_4557_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4649_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4634_ = v___x_4631_;
v_isShared_4635_ = v_isSharedCheck_4649_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4631_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4649_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v_fst_4636_; lean_object* v_snd_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4648_; 
v_fst_4636_ = lean_ctor_get(v_a_4632_, 0);
v_snd_4637_ = lean_ctor_get(v_a_4632_, 1);
v_isSharedCheck_4648_ = !lean_is_exclusive(v_a_4632_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4639_ = v_a_4632_;
v_isShared_4640_ = v_isSharedCheck_4648_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_snd_4637_);
lean_inc(v_fst_4636_);
lean_dec(v_a_4632_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4648_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4641_; lean_object* v___x_4643_; 
v___x_4641_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4636_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v___x_4641_);
v___x_4643_ = v___x_4639_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4647_, 1, v_snd_4637_);
v___x_4643_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
lean_object* v___x_4645_; 
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 0, v___x_4643_);
v___x_4645_ = v___x_4634_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
return v___x_4645_;
}
}
}
}
}
else
{
return v___x_4631_;
}
}
else
{
lean_object* v___x_4650_; lean_object* v___x_4652_; 
lean_dec_ref(v_leanOpts_4560_);
v___x_4650_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4627_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4650_);
v___x_4652_ = v___x_4617_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4650_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_snd_4615_);
v___x_4652_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4654_; 
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v___x_4652_);
v___x_4654_ = v___x_4612_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4655_; 
v_reuseFailAlloc_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
v___x_4654_ = v_reuseFailAlloc_4655_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
return v___x_4654_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_del_object(v___x_4606_);
lean_dec_ref(v_packages_4592_);
lean_dec_ref(v_leanOpts_4560_);
v_a_4660_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4609_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4609_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
lean_del_object(v___x_4606_);
lean_dec(v_snd_4604_);
lean_dec(v_fst_4603_);
lean_dec_ref(v___x_4599_);
lean_dec_ref(v_packages_4592_);
lean_dec_ref(v_leanOpts_4560_);
lean_dec_ref(v_ws_4558_);
v_a_4668_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4608_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4608_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec_ref(v___x_4599_);
lean_dec_ref(v_packages_4592_);
lean_dec_ref(v_leanOpts_4560_);
lean_dec_ref(v_ws_4558_);
v_a_4677_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4601_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4601_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
else
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4692_; 
lean_dec_ref(v_leanOpts_4560_);
lean_dec_ref(v_ws_4558_);
v_a_4685_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4687_ = v___x_4564_;
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4564_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4692_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v___x_4690_; 
if (v_isShared_4688_ == 0)
{
v___x_4690_ = v___x_4687_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v_a_4685_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4693_, lean_object* v_ws_4694_, lean_object* v_toUpdate_4695_, lean_object* v_leanOpts_4696_, lean_object* v_updateToolchain_4697_, lean_object* v_a_4698_){
_start:
{
uint8_t v_updateToolchain_boxed_4699_; lean_object* v_res_4700_; 
v_updateToolchain_boxed_4699_ = lean_unbox(v_updateToolchain_4697_);
v_res_4700_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4693_, v_ws_4694_, v_toUpdate_4695_, v_leanOpts_4696_, v_updateToolchain_boxed_4699_);
lean_dec(v_toUpdate_4695_);
lean_dec_ref(v_a_4693_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4701_, size_t v_i_4702_, size_t v_stop_4703_, lean_object* v_b_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
uint8_t v___x_4708_; 
v___x_4708_ = lean_usize_dec_eq(v_i_4702_, v_stop_4703_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_array_uget_borrowed(v_as_4701_, v_i_4702_);
lean_inc(v___x_4709_);
v___x_4710_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4709_, v___y_4705_, v___y_4706_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; size_t v___x_4712_; size_t v___x_4713_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___x_4710_, 1);
v___x_4712_ = ((size_t)1ULL);
v___x_4713_ = lean_usize_add(v_i_4702_, v___x_4712_);
v_i_4702_ = v___x_4713_;
v_b_4704_ = v_a_4711_;
goto _start;
}
else
{
return v___x_4710_;
}
}
else
{
lean_object* v___x_4715_; 
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v_b_4704_);
return v___x_4715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4716_, lean_object* v_i_4717_, lean_object* v_stop_4718_, lean_object* v_b_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
size_t v_i_boxed_4723_; size_t v_stop_boxed_4724_; lean_object* v_res_4725_; 
v_i_boxed_4723_ = lean_unbox_usize(v_i_4717_);
lean_dec(v_i_4717_);
v_stop_boxed_4724_ = lean_unbox_usize(v_stop_4718_);
lean_dec(v_stop_4718_);
v_res_4725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4716_, v_i_boxed_4723_, v_stop_boxed_4724_, v_b_4719_, v___y_4720_, v___y_4721_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v_as_4716_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4726_, lean_object* v_toUpdate_4727_, lean_object* v_leanOpts_4728_, uint8_t v_updateToolchain_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v___x_4732_; 
v___x_4732_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4730_, v_ws_4726_, v_toUpdate_4727_, v_leanOpts_4728_, v_updateToolchain_4729_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_object* v_a_4733_; lean_object* v_fst_4734_; lean_object* v_snd_4735_; lean_object* v___y_4737_; lean_object* v___x_4754_; 
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v___x_4732_, 1);
v_fst_4734_ = lean_ctor_get(v_a_4733_, 0);
lean_inc(v_fst_4734_);
v_snd_4735_ = lean_ctor_get(v_a_4733_, 1);
lean_inc(v_snd_4735_);
lean_dec(v_a_4733_);
v___x_4754_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4734_, v_snd_4735_);
lean_dec(v_snd_4735_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4776_; 
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4776_ == 0)
{
lean_object* v_unused_4777_; 
v_unused_4777_ = lean_ctor_get(v___x_4754_, 0);
lean_dec(v_unused_4777_);
v___x_4756_ = v___x_4754_;
v_isShared_4757_ = v_isSharedCheck_4776_;
goto v_resetjp_4755_;
}
else
{
lean_dec(v___x_4754_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4776_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v_packages_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; 
v_packages_4758_ = lean_ctor_get(v_fst_4734_, 4);
v___x_4759_ = lean_unsigned_to_nat(0u);
v___x_4760_ = lean_array_get_size(v_packages_4758_);
v___x_4761_ = lean_nat_dec_lt(v___x_4759_, v___x_4760_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4763_; 
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v_fst_4734_);
v___x_4763_ = v___x_4756_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_fst_4734_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
else
{
lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4765_ = lean_box(0);
v___x_4766_ = lean_nat_dec_le(v___x_4760_, v___x_4760_);
if (v___x_4766_ == 0)
{
if (v___x_4761_ == 0)
{
lean_object* v___x_4768_; 
if (v_isShared_4757_ == 0)
{
lean_ctor_set(v___x_4756_, 0, v_fst_4734_);
v___x_4768_ = v___x_4756_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_fst_4734_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
else
{
size_t v___x_4770_; size_t v___x_4771_; lean_object* v___x_4772_; 
lean_del_object(v___x_4756_);
v___x_4770_ = ((size_t)0ULL);
v___x_4771_ = lean_usize_of_nat(v___x_4760_);
v___x_4772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4758_, v___x_4770_, v___x_4771_, v___x_4765_, v_fst_4734_, v_a_4730_);
v___y_4737_ = v___x_4772_;
goto v___jp_4736_;
}
}
else
{
size_t v___x_4773_; size_t v___x_4774_; lean_object* v___x_4775_; 
lean_del_object(v___x_4756_);
v___x_4773_ = ((size_t)0ULL);
v___x_4774_ = lean_usize_of_nat(v___x_4760_);
v___x_4775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4758_, v___x_4773_, v___x_4774_, v___x_4765_, v_fst_4734_, v_a_4730_);
v___y_4737_ = v___x_4775_;
goto v___jp_4736_;
}
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4790_; 
lean_dec(v_fst_4734_);
v_a_4778_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4780_ = v___x_4754_;
v_isShared_4781_ = v_isSharedCheck_4790_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4754_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4790_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4782_; uint8_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4782_ = lean_io_error_to_string(v_a_4778_);
v___x_4783_ = 3;
v___x_4784_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4784_, 0, v___x_4782_);
lean_ctor_set_uint8(v___x_4784_, sizeof(void*)*1, v___x_4783_);
lean_inc_ref(v_a_4730_);
v___x_4785_ = lean_apply_2(v_a_4730_, v___x_4784_, lean_box(0));
v___x_4786_ = lean_box(0);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 0, v___x_4786_);
v___x_4788_ = v___x_4780_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
v___jp_4736_:
{
if (lean_obj_tag(v___y_4737_) == 0)
{
lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
v_isSharedCheck_4744_ = !lean_is_exclusive(v___y_4737_);
if (v_isSharedCheck_4744_ == 0)
{
lean_object* v_unused_4745_; 
v_unused_4745_ = lean_ctor_get(v___y_4737_, 0);
lean_dec(v_unused_4745_);
v___x_4739_ = v___y_4737_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_dec(v___y_4737_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v_fst_4734_);
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_fst_4734_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_dec(v_fst_4734_);
v_a_4746_ = lean_ctor_get(v___y_4737_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___y_4737_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___y_4737_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___y_4737_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
v_a_4791_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4732_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4732_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4799_, lean_object* v_toUpdate_4800_, lean_object* v_leanOpts_4801_, lean_object* v_updateToolchain_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
uint8_t v_updateToolchain_boxed_4805_; lean_object* v_res_4806_; 
v_updateToolchain_boxed_4805_ = lean_unbox(v_updateToolchain_4802_);
v_res_4806_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4799_, v_toUpdate_4800_, v_leanOpts_4801_, v_updateToolchain_boxed_4805_, v_a_4803_);
lean_dec_ref(v_a_4803_);
lean_dec(v_toUpdate_4800_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4811_, lean_object* v_what_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v_name_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v_name_4815_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_name_4815_);
lean_dec_ref(v___x_4811_);
v___x_4816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4817_ = lean_string_append(v___x_4816_, v_what_4812_);
v___x_4818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4819_ = lean_string_append(v___x_4817_, v___x_4818_);
v___x_4820_ = 1;
v___x_4821_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4815_, v___x_4820_);
v___x_4822_ = lean_string_append(v___x_4819_, v___x_4821_);
v___x_4823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4824_ = lean_string_append(v___x_4822_, v___x_4823_);
v___x_4825_ = lean_string_append(v___x_4824_, v___x_4821_);
lean_dec_ref(v___x_4821_);
v___x_4826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4827_ = lean_string_append(v___x_4825_, v___x_4826_);
v___x_4828_ = 2;
v___x_4829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4829_, 0, v___x_4827_);
lean_ctor_set_uint8(v___x_4829_, sizeof(void*)*1, v___x_4828_);
lean_inc_ref(v___y_4813_);
v___x_4830_ = lean_apply_2(v___y_4813_, v___x_4829_, lean_box(0));
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4832_, lean_object* v_what_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4832_, v_what_4833_, v___y_4834_);
lean_dec_ref(v___y_4834_);
lean_dec_ref(v_what_4833_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4840_, lean_object* v_as_4841_, size_t v_i_4842_, size_t v_stop_4843_, lean_object* v_b_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v_a_4848_; lean_object* v___y_4853_; uint8_t v___x_4855_; 
v___x_4855_ = lean_usize_dec_eq(v_i_4842_, v_stop_4843_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; lean_object* v_src_x3f_4857_; 
v___x_4856_ = lean_array_uget_borrowed(v_as_4841_, v_i_4842_);
v_src_x3f_4857_ = lean_ctor_get(v___x_4856_, 3);
if (lean_obj_tag(v_src_x3f_4857_) == 1)
{
lean_object* v_name_4858_; lean_object* v_val_4859_; lean_object* v___x_4860_; 
v_name_4858_ = lean_ctor_get(v___x_4856_, 0);
v_val_4859_ = lean_ctor_get(v_src_x3f_4857_, 0);
v___x_4860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4840_, v_name_4858_);
if (lean_obj_tag(v___x_4860_) == 1)
{
lean_object* v_val_4861_; lean_object* v___y_4863_; lean_object* v___y_4867_; 
v_val_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_val_4861_);
lean_dec_ref_known(v___x_4860_, 1);
if (lean_obj_tag(v_val_4859_) == 0)
{
lean_object* v_src_4870_; 
v_src_4870_ = lean_ctor_get(v_val_4861_, 4);
lean_inc_ref(v_src_4870_);
lean_dec(v_val_4861_);
if (lean_obj_tag(v_src_4870_) == 0)
{
lean_object* v___x_4871_; 
lean_dec_ref_known(v_src_4870_, 1);
v___x_4871_ = lean_box(0);
v_a_4848_ = v___x_4871_;
goto v___jp_4847_;
}
else
{
lean_dec_ref(v_src_4870_);
v___y_4867_ = v___y_4845_;
goto v___jp_4866_;
}
}
else
{
lean_object* v_src_4872_; 
v_src_4872_ = lean_ctor_get(v_val_4861_, 4);
lean_inc_ref(v_src_4872_);
lean_dec(v_val_4861_);
if (lean_obj_tag(v_src_4872_) == 1)
{
lean_object* v_url_4873_; lean_object* v_rev_4874_; lean_object* v_url_4875_; lean_object* v_inputRev_x3f_4876_; lean_object* v___y_4878_; uint8_t v___x_4885_; 
v_url_4873_ = lean_ctor_get(v_val_4859_, 0);
v_rev_4874_ = lean_ctor_get(v_val_4859_, 1);
v_url_4875_ = lean_ctor_get(v_src_4872_, 0);
lean_inc_ref(v_url_4875_);
v_inputRev_x3f_4876_ = lean_ctor_get(v_src_4872_, 2);
lean_inc(v_inputRev_x3f_4876_);
lean_dec_ref_known(v_src_4872_, 4);
v___x_4885_ = lean_string_dec_eq(v_url_4873_, v_url_4875_);
lean_dec_ref(v_url_4875_);
if (v___x_4885_ == 0)
{
goto v___jp_4882_;
}
else
{
if (v___x_4855_ == 0)
{
v___y_4878_ = v___y_4845_;
goto v___jp_4877_;
}
else
{
goto v___jp_4882_;
}
}
v___jp_4877_:
{
lean_object* v___x_4879_; uint8_t v___x_4880_; 
v___x_4879_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4874_);
v___x_4880_ = l_Option_instDecidableEq___redArg(v___x_4879_, v_rev_4874_, v_inputRev_x3f_4876_);
if (v___x_4880_ == 0)
{
v___y_4863_ = v___y_4878_;
goto v___jp_4862_;
}
else
{
if (v___x_4855_ == 0)
{
lean_object* v___x_4881_; 
v___x_4881_ = lean_box(0);
v_a_4848_ = v___x_4881_;
goto v___jp_4847_;
}
else
{
v___y_4863_ = v___y_4878_;
goto v___jp_4862_;
}
}
}
v___jp_4882_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_4856_);
v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4856_, v___x_4883_, v___y_4845_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_dec_ref_known(v___x_4884_, 1);
v___y_4878_ = v___y_4845_;
goto v___jp_4877_;
}
else
{
lean_dec(v_inputRev_x3f_4876_);
return v___x_4884_;
}
}
}
else
{
lean_dec_ref(v_src_4872_);
v___y_4867_ = v___y_4845_;
goto v___jp_4866_;
}
}
v___jp_4862_:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_4856_);
v___x_4865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4856_, v___x_4864_, v___y_4863_);
v___y_4853_ = v___x_4865_;
goto v___jp_4852_;
}
v___jp_4866_:
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_4856_);
v___x_4869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4856_, v___x_4868_, v___y_4867_);
v___y_4853_ = v___x_4869_;
goto v___jp_4852_;
}
}
else
{
lean_object* v___x_4886_; 
lean_dec(v___x_4860_);
v___x_4886_ = lean_box(0);
v_a_4848_ = v___x_4886_;
goto v___jp_4847_;
}
}
else
{
lean_object* v___x_4887_; 
v___x_4887_ = lean_box(0);
v_a_4848_ = v___x_4887_;
goto v___jp_4847_;
}
}
else
{
lean_object* v___x_4888_; 
v___x_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4888_, 0, v_b_4844_);
return v___x_4888_;
}
v___jp_4847_:
{
size_t v___x_4849_; size_t v___x_4850_; 
v___x_4849_ = ((size_t)1ULL);
v___x_4850_ = lean_usize_add(v_i_4842_, v___x_4849_);
v_i_4842_ = v___x_4850_;
v_b_4844_ = v_a_4848_;
goto _start;
}
v___jp_4852_:
{
if (lean_obj_tag(v___y_4853_) == 0)
{
lean_object* v_a_4854_; 
v_a_4854_ = lean_ctor_get(v___y_4853_, 0);
lean_inc(v_a_4854_);
lean_dec_ref_known(v___y_4853_, 1);
v_a_4848_ = v_a_4854_;
goto v___jp_4847_;
}
else
{
return v___y_4853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4889_, lean_object* v_as_4890_, lean_object* v_i_4891_, lean_object* v_stop_4892_, lean_object* v_b_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
size_t v_i_boxed_4896_; size_t v_stop_boxed_4897_; lean_object* v_res_4898_; 
v_i_boxed_4896_ = lean_unbox_usize(v_i_4891_);
lean_dec(v_i_4891_);
v_stop_boxed_4897_ = lean_unbox_usize(v_stop_4892_);
lean_dec(v_stop_4892_);
v_res_4898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4889_, v_as_4890_, v_i_boxed_4896_, v_stop_boxed_4897_, v_b_4893_, v___y_4894_);
lean_dec_ref(v___y_4894_);
lean_dec_ref(v_as_4890_);
lean_dec(v_pkgEntries_4889_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4899_, lean_object* v_deps_4900_, lean_object* v_a_4901_){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; uint8_t v___x_4906_; 
v___x_4903_ = lean_unsigned_to_nat(0u);
v___x_4904_ = lean_array_get_size(v_deps_4900_);
v___x_4905_ = lean_box(0);
v___x_4906_ = lean_nat_dec_lt(v___x_4903_, v___x_4904_);
if (v___x_4906_ == 0)
{
lean_object* v___x_4907_; 
v___x_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4905_);
return v___x_4907_;
}
else
{
uint8_t v___x_4908_; 
v___x_4908_ = lean_nat_dec_le(v___x_4904_, v___x_4904_);
if (v___x_4908_ == 0)
{
if (v___x_4906_ == 0)
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4905_);
return v___x_4909_;
}
else
{
size_t v___x_4910_; size_t v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = ((size_t)0ULL);
v___x_4911_ = lean_usize_of_nat(v___x_4904_);
v___x_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4899_, v_deps_4900_, v___x_4910_, v___x_4911_, v___x_4905_, v_a_4901_);
return v___x_4912_;
}
}
else
{
size_t v___x_4913_; size_t v___x_4914_; lean_object* v___x_4915_; 
v___x_4913_ = ((size_t)0ULL);
v___x_4914_ = lean_usize_of_nat(v___x_4904_);
v___x_4915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4899_, v_deps_4900_, v___x_4913_, v___x_4914_, v___x_4905_, v_a_4901_);
return v___x_4915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_4916_, lean_object* v_deps_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_4916_, v_deps_4917_, v_a_4918_);
lean_dec_ref(v_a_4918_);
lean_dec_ref(v_deps_4917_);
lean_dec(v_pkgEntries_4916_);
return v_res_4920_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_4921_, lean_object* v_x_4922_){
_start:
{
if (lean_obj_tag(v_x_4921_) == 0)
{
if (lean_obj_tag(v_x_4922_) == 0)
{
uint8_t v___x_4923_; 
v___x_4923_ = 1;
return v___x_4923_;
}
else
{
uint8_t v___x_4924_; 
v___x_4924_ = 0;
return v___x_4924_;
}
}
else
{
if (lean_obj_tag(v_x_4922_) == 0)
{
uint8_t v___x_4925_; 
v___x_4925_ = 0;
return v___x_4925_;
}
else
{
lean_object* v_val_4926_; lean_object* v_val_4927_; uint8_t v___x_4928_; 
v_val_4926_ = lean_ctor_get(v_x_4921_, 0);
v_val_4927_ = lean_ctor_get(v_x_4922_, 0);
v___x_4928_ = lean_string_dec_eq(v_val_4926_, v_val_4927_);
return v___x_4928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_4929_, lean_object* v_x_4930_){
_start:
{
uint8_t v_res_4931_; lean_object* v_r_4932_; 
v_res_4931_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_4929_, v_x_4930_);
lean_dec(v_x_4930_);
lean_dec(v_x_4929_);
v_r_4932_ = lean_box(v_res_4931_);
return v_r_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v_leanOpts_4941_, uint8_t v_reconfigure_4942_, lean_object* v_as_4943_, size_t v_i_4944_, size_t v_stop_4945_, lean_object* v_b_4946_, lean_object* v___y_4947_){
_start:
{
uint8_t v___x_4952_; 
v___x_4952_ = lean_usize_dec_eq(v_i_4944_, v_stop_4945_);
if (v___x_4952_ == 0)
{
lean_object* v_ws_4953_; lean_object* v_depIdxs_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_5102_; 
v_ws_4953_ = lean_ctor_get(v_b_4946_, 0);
v_depIdxs_4954_ = lean_ctor_get(v_b_4946_, 1);
v_isSharedCheck_5102_ = !lean_is_exclusive(v_b_4946_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_4956_ = v_b_4946_;
v_isShared_4957_ = v_isSharedCheck_5102_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_depIdxs_4954_);
lean_inc(v_ws_4953_);
lean_dec(v_b_4946_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_5102_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v_lakeEnv_4958_; lean_object* v_packages_4959_; size_t v___x_4960_; size_t v___x_4961_; lean_object* v___x_4962_; lean_object* v___f_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v_lakeEnv_4958_ = lean_ctor_get(v_ws_4953_, 0);
v_packages_4959_ = lean_ctor_get(v_ws_4953_, 4);
v___x_4960_ = ((size_t)1ULL);
v___x_4961_ = lean_usize_sub(v_i_4944_, v___x_4960_);
v___x_4962_ = lean_array_uget_borrowed(v_as_4943_, v___x_4961_);
lean_inc(v___x_4962_);
v___f_4963_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4963_, 0, v___x_4962_);
v___x_4964_ = lean_unsigned_to_nat(0u);
v___x_4965_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4963_, v_packages_4959_, v___x_4964_);
if (lean_obj_tag(v___x_4965_) == 1)
{
lean_object* v_val_4966_; lean_object* v___x_4967_; lean_object* v___x_4969_; 
v_val_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_val_4966_);
lean_dec_ref_known(v___x_4965_, 1);
v___x_4967_ = lean_array_push(v_depIdxs_4954_, v_val_4966_);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 1, v___x_4967_);
v___x_4969_ = v___x_4956_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_ws_4953_);
lean_ctor_set(v_reuseFailAlloc_4971_, 1, v___x_4967_);
v___x_4969_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
v_i_4944_ = v___x_4961_;
v_b_4946_ = v___x_4969_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_4972_; lean_object* v_baseName_4973_; lean_object* v_name_4974_; lean_object* v_opts_4975_; uint8_t v___x_4976_; 
lean_inc_ref(v_packages_4959_);
lean_dec(v___x_4965_);
v_wsIdx_4972_ = lean_ctor_get(v_pkg_4938_, 0);
v_baseName_4973_ = lean_ctor_get(v_pkg_4938_, 1);
v_name_4974_ = lean_ctor_get(v___x_4962_, 0);
v_opts_4975_ = lean_ctor_get(v___x_4962_, 4);
v___x_4976_ = lean_name_eq(v_baseName_4973_, v_name_4974_);
if (v___x_4976_ == 0)
{
lean_object* v___x_4977_; 
v___x_4977_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_4939_, v_name_4974_);
if (lean_obj_tag(v___x_4977_) == 1)
{
lean_object* v_val_4978_; lean_object* v___x_4979_; lean_object* v_dir_4980_; lean_object* v___x_4981_; 
v_val_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_val_4978_);
lean_dec_ref_known(v___x_4977_, 1);
v___x_4979_ = lean_array_fget_borrowed(v_packages_4959_, v___x_4964_);
v_dir_4980_ = lean_ctor_get(v___x_4979_, 4);
lean_inc_ref(v___y_4940_);
lean_inc_ref(v_dir_4980_);
v___x_4981_ = l_Lake_PackageEntry_materialize(v_val_4978_, v_lakeEnv_4958_, v_dir_4980_, v___y_4940_, v___y_4947_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_5056_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_4984_ = v___x_4981_;
v_isShared_4985_ = v_isSharedCheck_5056_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4981_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_5056_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4986_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4941_);
lean_inc(v_opts_4975_);
v___x_4987_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4953_, v_a_4982_, v_opts_4975_, v_leanOpts_4941_, v_reconfigure_4942_, v___x_4986_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; lean_object* v_a_4989_; lean_object* v_wsIdx_4990_; lean_object* v___x_4991_; lean_object* v___x_4993_; 
lean_del_object(v___x_4984_);
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4988_);
v_a_4989_ = lean_ctor_get(v___x_4987_, 1);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4987_, 2);
v_wsIdx_4990_ = lean_array_get_size(v_packages_4959_);
lean_dec_ref(v_packages_4959_);
v___x_4991_ = lean_array_push(v_depIdxs_4954_, v_wsIdx_4990_);
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 1, v___x_4991_);
lean_ctor_set(v___x_4956_, 0, v_a_4988_);
v___x_4993_ = v___x_4956_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_4988_);
lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_4991_);
v___x_4993_ = v_reuseFailAlloc_5024_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
lean_object* v___x_4994_; uint8_t v___x_4995_; 
v___x_4994_ = lean_array_get_size(v_a_4989_);
v___x_4995_ = lean_nat_dec_lt(v___x_4964_, v___x_4994_);
if (v___x_4995_ == 0)
{
lean_dec(v_a_4989_);
v_i_4944_ = v___x_4961_;
v_b_4946_ = v___x_4993_;
goto _start;
}
else
{
lean_object* v___x_4997_; uint8_t v___x_4998_; 
v___x_4997_ = lean_box(0);
v___x_4998_ = lean_nat_dec_le(v___x_4994_, v___x_4994_);
if (v___x_4998_ == 0)
{
if (v___x_4995_ == 0)
{
lean_dec(v_a_4989_);
v_i_4944_ = v___x_4961_;
v_b_4946_ = v___x_4993_;
goto _start;
}
else
{
size_t v___x_5000_; size_t v___x_5001_; lean_object* v___x_5002_; 
v___x_5000_ = ((size_t)0ULL);
v___x_5001_ = lean_usize_of_nat(v___x_4994_);
v___x_5002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4989_, v___x_5000_, v___x_5001_, v___x_4997_, v___y_4947_);
lean_dec(v_a_4989_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_dec_ref_known(v___x_5002_, 1);
v_i_4944_ = v___x_4961_;
v_b_4946_ = v___x_4993_;
goto _start;
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
lean_dec_ref(v___x_4993_);
lean_dec_ref(v_leanOpts_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_pkg_4938_);
v_a_5004_ = lean_ctor_get(v___x_5002_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_5002_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_5002_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5002_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
}
else
{
size_t v___x_5012_; size_t v___x_5013_; lean_object* v___x_5014_; 
v___x_5012_ = ((size_t)0ULL);
v___x_5013_ = lean_usize_of_nat(v___x_4994_);
v___x_5014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4989_, v___x_5012_, v___x_5013_, v___x_4997_, v___y_4947_);
lean_dec(v_a_4989_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_dec_ref_known(v___x_5014_, 1);
v_i_4944_ = v___x_4961_;
v_b_4946_ = v___x_4993_;
goto _start;
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
lean_dec_ref(v___x_4993_);
lean_dec_ref(v_leanOpts_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_pkg_4938_);
v_a_5016_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_5014_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5014_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; 
lean_dec_ref(v_packages_4959_);
lean_del_object(v___x_4956_);
lean_dec_ref(v_depIdxs_4954_);
lean_dec_ref(v_leanOpts_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_pkg_4938_);
v_a_5025_ = lean_ctor_get(v___x_4987_, 1);
lean_inc(v_a_5025_);
lean_dec_ref_known(v___x_4987_, 2);
v___x_5026_ = lean_array_get_size(v_a_5025_);
v___x_5027_ = lean_nat_dec_lt(v___x_4964_, v___x_5026_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; lean_object* v___x_5030_; 
lean_dec(v_a_5025_);
v___x_5028_ = lean_box(0);
if (v_isShared_4985_ == 0)
{
lean_ctor_set_tag(v___x_4984_, 1);
lean_ctor_set(v___x_4984_, 0, v___x_5028_);
v___x_5030_ = v___x_4984_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
else
{
lean_object* v___x_5032_; uint8_t v___x_5033_; 
lean_del_object(v___x_4984_);
v___x_5032_ = lean_box(0);
v___x_5033_ = lean_nat_dec_le(v___x_5026_, v___x_5026_);
if (v___x_5033_ == 0)
{
if (v___x_5027_ == 0)
{
lean_dec(v_a_5025_);
goto v___jp_4949_;
}
else
{
size_t v___x_5034_; size_t v___x_5035_; lean_object* v___x_5036_; 
v___x_5034_ = ((size_t)0ULL);
v___x_5035_ = lean_usize_of_nat(v___x_5026_);
v___x_5036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5025_, v___x_5034_, v___x_5035_, v___x_5032_, v___y_4947_);
lean_dec(v_a_5025_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_dec_ref_known(v___x_5036_, 1);
goto v___jp_4949_;
}
else
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5044_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5039_ = v___x_5036_;
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5036_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5042_; 
if (v_isShared_5040_ == 0)
{
v___x_5042_ = v___x_5039_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
}
}
else
{
size_t v___x_5045_; size_t v___x_5046_; lean_object* v___x_5047_; 
v___x_5045_ = ((size_t)0ULL);
v___x_5046_ = lean_usize_of_nat(v___x_5026_);
v___x_5047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5025_, v___x_5045_, v___x_5046_, v___x_5032_, v___y_4947_);
lean_dec(v_a_5025_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_dec_ref_known(v___x_5047_, 1);
goto v___jp_4949_;
}
else
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_5047_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5047_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
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
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5064_; 
lean_dec_ref(v_packages_4959_);
lean_del_object(v___x_4956_);
lean_dec_ref(v_depIdxs_4954_);
lean_dec_ref(v_ws_4953_);
lean_dec_ref(v_leanOpts_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_pkg_4938_);
v_a_5057_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5059_ = v___x_4981_;
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v___x_4981_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v___x_5062_; 
if (v_isShared_5060_ == 0)
{
v___x_5062_ = v___x_5059_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
}
else
{
uint8_t v___x_5065_; 
lean_inc(v_baseName_4973_);
lean_inc(v_wsIdx_4972_);
lean_dec(v___x_4977_);
lean_dec_ref(v_packages_4959_);
lean_del_object(v___x_4956_);
lean_dec_ref(v_depIdxs_4954_);
lean_dec_ref(v_ws_4953_);
lean_dec_ref(v_leanOpts_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_pkg_4938_);
v___x_5065_ = lean_nat_dec_eq(v_wsIdx_4972_, v___x_4964_);
lean_dec(v_wsIdx_4972_);
if (v___x_5065_ == 0)
{
lean_object* v___x_5066_; uint8_t v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; uint8_t v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v___x_5066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5067_ = 1;
lean_inc(v_name_4974_);
v___x_5068_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4974_, v___x_5067_);
v___x_5069_ = lean_string_append(v___x_5066_, v___x_5068_);
lean_dec_ref(v___x_5068_);
v___x_5070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5071_ = lean_string_append(v___x_5069_, v___x_5070_);
v___x_5072_ = l_Lean_Name_toString(v_baseName_4973_, v___x_5065_);
v___x_5073_ = lean_string_append(v___x_5071_, v___x_5072_);
lean_dec_ref(v___x_5072_);
v___x_5074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5075_ = lean_string_append(v___x_5073_, v___x_5074_);
v___x_5076_ = 3;
v___x_5077_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5077_, 0, v___x_5075_);
lean_ctor_set_uint8(v___x_5077_, sizeof(void*)*1, v___x_5076_);
lean_inc_ref(v___y_4947_);
v___x_5078_ = lean_apply_2(v___y_4947_, v___x_5077_, lean_box(0));
v___x_5079_ = lean_box(0);
v___x_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
return v___x_5080_;
}
else
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; uint8_t v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
lean_dec(v_baseName_4973_);
v___x_5081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_4974_);
v___x_5082_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4974_, v___x_5065_);
v___x_5083_ = lean_string_append(v___x_5081_, v___x_5082_);
v___x_5084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5085_ = lean_string_append(v___x_5083_, v___x_5084_);
v___x_5086_ = lean_string_append(v___x_5085_, v___x_5082_);
lean_dec_ref(v___x_5082_);
v___x_5087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5088_ = lean_string_append(v___x_5086_, v___x_5087_);
v___x_5089_ = 3;
v___x_5090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5090_, 0, v___x_5088_);
lean_ctor_set_uint8(v___x_5090_, sizeof(void*)*1, v___x_5089_);
lean_inc_ref(v___y_4947_);
v___x_5091_ = lean_apply_2(v___y_4947_, v___x_5090_, lean_box(0));
v___x_5092_ = lean_box(0);
v___x_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5092_);
return v___x_5093_;
}
}
}
else
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; 
lean_inc(v_baseName_4973_);
lean_dec_ref(v_packages_4959_);
lean_del_object(v___x_4956_);
lean_dec_ref(v_depIdxs_4954_);
lean_dec_ref(v_ws_4953_);
lean_dec_ref(v_leanOpts_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_pkg_4938_);
v___x_5094_ = l_Lean_Name_toString(v_baseName_4973_, v___x_4952_);
v___x_5095_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5096_ = lean_string_append(v___x_5094_, v___x_5095_);
v___x_5097_ = 3;
v___x_5098_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5098_, 0, v___x_5096_);
lean_ctor_set_uint8(v___x_5098_, sizeof(void*)*1, v___x_5097_);
lean_inc_ref(v___y_4947_);
v___x_5099_ = lean_apply_2(v___y_4947_, v___x_5098_, lean_box(0));
v___x_5100_ = lean_box(0);
v___x_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5100_);
return v___x_5101_;
}
}
}
}
else
{
lean_object* v___x_5103_; 
lean_dec_ref(v_leanOpts_4941_);
lean_dec_ref(v___y_4940_);
lean_dec_ref(v_pkg_4938_);
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v_b_4946_);
return v___x_5103_;
}
v___jp_4949_:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4950_ = lean_box(0);
v___x_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
return v___x_4951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v_leanOpts_5107_, lean_object* v_reconfigure_5108_, lean_object* v_as_5109_, lean_object* v_i_5110_, lean_object* v_stop_5111_, lean_object* v_b_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
uint8_t v_reconfigure_boxed_5115_; size_t v_i_boxed_5116_; size_t v_stop_boxed_5117_; lean_object* v_res_5118_; 
v_reconfigure_boxed_5115_ = lean_unbox(v_reconfigure_5108_);
v_i_boxed_5116_ = lean_unbox_usize(v_i_5110_);
lean_dec(v_i_5110_);
v_stop_boxed_5117_ = lean_unbox_usize(v_stop_5111_);
lean_dec(v_stop_5111_);
v_res_5118_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5104_, v___y_5105_, v___y_5106_, v_leanOpts_5107_, v_reconfigure_boxed_5115_, v_as_5109_, v_i_boxed_5116_, v_stop_boxed_5117_, v_b_5112_, v___y_5113_);
lean_dec_ref(v___y_5113_);
lean_dec_ref(v_as_5109_);
lean_dec(v___y_5105_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5119_, lean_object* v_pkg_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v_leanOpts_5123_, uint8_t v_reconfigure_5124_, lean_object* v_as_5125_, size_t v_i_5126_, size_t v_stop_5127_, lean_object* v_b_5128_, lean_object* v___y_5129_){
_start:
{
uint8_t v___x_5134_; 
v___x_5134_ = lean_usize_dec_eq(v_i_5126_, v_stop_5127_);
if (v___x_5134_ == 0)
{
lean_object* v_ws_5135_; lean_object* v_depIdxs_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5284_; 
v_ws_5135_ = lean_ctor_get(v_b_5128_, 0);
v_depIdxs_5136_ = lean_ctor_get(v_b_5128_, 1);
v_isSharedCheck_5284_ = !lean_is_exclusive(v_b_5128_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5138_ = v_b_5128_;
v_isShared_5139_ = v_isSharedCheck_5284_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_depIdxs_5136_);
lean_inc(v_ws_5135_);
lean_dec(v_b_5128_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5284_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v_lakeEnv_5140_; lean_object* v_packages_5141_; size_t v___x_5142_; size_t v___x_5143_; lean_object* v___x_5144_; lean_object* v___f_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
v_lakeEnv_5140_ = lean_ctor_get(v_ws_5135_, 0);
v_packages_5141_ = lean_ctor_get(v_ws_5135_, 4);
v___x_5142_ = ((size_t)1ULL);
v___x_5143_ = lean_usize_sub(v_i_5126_, v___x_5142_);
v___x_5144_ = lean_array_uget_borrowed(v_as_5125_, v___x_5143_);
lean_inc(v___x_5144_);
v___f_5145_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5145_, 0, v___x_5144_);
v___x_5146_ = lean_unsigned_to_nat(0u);
v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5145_, v_packages_5141_, v___x_5146_);
if (lean_obj_tag(v___x_5147_) == 1)
{
lean_object* v_val_5148_; lean_object* v___x_5149_; lean_object* v___x_5151_; 
v_val_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_val_5148_);
lean_dec_ref_known(v___x_5147_, 1);
v___x_5149_ = lean_array_push(v_depIdxs_5136_, v_val_5148_);
if (v_isShared_5139_ == 0)
{
lean_ctor_set(v___x_5138_, 1, v___x_5149_);
v___x_5151_ = v___x_5138_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_ws_5135_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v___x_5149_);
v___x_5151_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
lean_object* v___x_5152_; 
v___x_5152_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5120_, v___y_5121_, v___y_5122_, v_leanOpts_5123_, v_reconfigure_5124_, v_as_5125_, v___x_5143_, v_stop_5127_, v___x_5151_, v___y_5129_);
return v___x_5152_;
}
}
else
{
lean_object* v_wsIdx_5154_; lean_object* v_baseName_5155_; lean_object* v_name_5156_; lean_object* v_opts_5157_; uint8_t v___x_5158_; 
lean_inc_ref(v_packages_5141_);
lean_dec(v___x_5147_);
v_wsIdx_5154_ = lean_ctor_get(v_pkg_5120_, 0);
v_baseName_5155_ = lean_ctor_get(v_pkg_5120_, 1);
v_name_5156_ = lean_ctor_get(v___x_5144_, 0);
v_opts_5157_ = lean_ctor_get(v___x_5144_, 4);
v___x_5158_ = lean_name_eq(v_baseName_5155_, v_name_5156_);
if (v___x_5158_ == 0)
{
lean_object* v___x_5159_; 
v___x_5159_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5121_, v_name_5156_);
if (lean_obj_tag(v___x_5159_) == 1)
{
lean_object* v_val_5160_; lean_object* v___x_5161_; lean_object* v_dir_5162_; lean_object* v___x_5163_; 
v_val_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_val_5160_);
lean_dec_ref_known(v___x_5159_, 1);
v___x_5161_ = lean_array_fget_borrowed(v_packages_5141_, v___x_5146_);
v_dir_5162_ = lean_ctor_get(v___x_5161_, 4);
lean_inc_ref(v___y_5122_);
lean_inc_ref(v_dir_5162_);
v___x_5163_ = l_Lake_PackageEntry_materialize(v_val_5160_, v_lakeEnv_5140_, v_dir_5162_, v___y_5122_, v___y_5129_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5238_; 
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5166_ = v___x_5163_;
v_isShared_5167_ = v_isSharedCheck_5238_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5163_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5238_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5168_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5123_);
lean_inc(v_opts_5157_);
v___x_5169_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5135_, v_a_5164_, v_opts_5157_, v_leanOpts_5123_, v_reconfigure_5124_, v___x_5168_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; lean_object* v_a_5171_; lean_object* v_wsIdx_5172_; lean_object* v___x_5173_; lean_object* v___x_5175_; 
lean_del_object(v___x_5166_);
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
v_a_5171_ = lean_ctor_get(v___x_5169_, 1);
lean_inc(v_a_5171_);
lean_dec_ref_known(v___x_5169_, 2);
v_wsIdx_5172_ = lean_array_get_size(v_packages_5141_);
lean_dec_ref(v_packages_5141_);
v___x_5173_ = lean_array_push(v_depIdxs_5136_, v_wsIdx_5172_);
if (v_isShared_5139_ == 0)
{
lean_ctor_set(v___x_5138_, 1, v___x_5173_);
lean_ctor_set(v___x_5138_, 0, v_a_5170_);
v___x_5175_ = v___x_5138_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5170_);
lean_ctor_set(v_reuseFailAlloc_5206_, 1, v___x_5173_);
v___x_5175_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
lean_object* v___x_5176_; uint8_t v___x_5177_; 
v___x_5176_ = lean_array_get_size(v_a_5171_);
v___x_5177_ = lean_nat_dec_lt(v___x_5146_, v___x_5176_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
lean_dec(v_a_5171_);
v___x_5178_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5120_, v___y_5121_, v___y_5122_, v_leanOpts_5123_, v_reconfigure_5124_, v_as_5125_, v___x_5143_, v_stop_5127_, v___x_5175_, v___y_5129_);
return v___x_5178_;
}
else
{
lean_object* v___x_5179_; uint8_t v___x_5180_; 
v___x_5179_ = lean_box(0);
v___x_5180_ = lean_nat_dec_le(v___x_5176_, v___x_5176_);
if (v___x_5180_ == 0)
{
if (v___x_5177_ == 0)
{
lean_object* v___x_5181_; 
lean_dec(v_a_5171_);
v___x_5181_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5120_, v___y_5121_, v___y_5122_, v_leanOpts_5123_, v_reconfigure_5124_, v_as_5125_, v___x_5143_, v_stop_5127_, v___x_5175_, v___y_5129_);
return v___x_5181_;
}
else
{
size_t v___x_5182_; size_t v___x_5183_; lean_object* v___x_5184_; 
v___x_5182_ = ((size_t)0ULL);
v___x_5183_ = lean_usize_of_nat(v___x_5176_);
v___x_5184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5171_, v___x_5182_, v___x_5183_, v___x_5179_, v___y_5129_);
lean_dec(v_a_5171_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v___x_5185_; 
lean_dec_ref_known(v___x_5184_, 1);
v___x_5185_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5120_, v___y_5121_, v___y_5122_, v_leanOpts_5123_, v_reconfigure_5124_, v_as_5125_, v___x_5143_, v_stop_5127_, v___x_5175_, v___y_5129_);
return v___x_5185_;
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
lean_dec_ref(v___x_5175_);
lean_dec_ref(v_leanOpts_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v_pkg_5120_);
v_a_5186_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5184_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5184_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
}
else
{
size_t v___x_5194_; size_t v___x_5195_; lean_object* v___x_5196_; 
v___x_5194_ = ((size_t)0ULL);
v___x_5195_ = lean_usize_of_nat(v___x_5176_);
v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5171_, v___x_5194_, v___x_5195_, v___x_5179_, v___y_5129_);
lean_dec(v_a_5171_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v___x_5197_; 
lean_dec_ref_known(v___x_5196_, 1);
v___x_5197_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5120_, v___y_5121_, v___y_5122_, v_leanOpts_5123_, v_reconfigure_5124_, v_as_5125_, v___x_5143_, v_stop_5127_, v___x_5175_, v___y_5129_);
return v___x_5197_;
}
else
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5205_; 
lean_dec_ref(v___x_5175_);
lean_dec_ref(v_leanOpts_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v_pkg_5120_);
v_a_5198_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5200_ = v___x_5196_;
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v___x_5196_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5205_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
lean_object* v___x_5203_; 
if (v_isShared_5201_ == 0)
{
v___x_5203_ = v___x_5200_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
v___x_5203_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
return v___x_5203_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5208_; uint8_t v___x_5209_; 
lean_dec_ref(v_packages_5141_);
lean_del_object(v___x_5138_);
lean_dec_ref(v_depIdxs_5136_);
lean_dec_ref(v_leanOpts_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v_pkg_5120_);
v_a_5207_ = lean_ctor_get(v___x_5169_, 1);
lean_inc(v_a_5207_);
lean_dec_ref_known(v___x_5169_, 2);
v___x_5208_ = lean_array_get_size(v_a_5207_);
v___x_5209_ = lean_nat_dec_lt(v___x_5146_, v___x_5208_);
if (v___x_5209_ == 0)
{
lean_object* v___x_5210_; lean_object* v___x_5212_; 
lean_dec(v_a_5207_);
v___x_5210_ = lean_box(0);
if (v_isShared_5167_ == 0)
{
lean_ctor_set_tag(v___x_5166_, 1);
lean_ctor_set(v___x_5166_, 0, v___x_5210_);
v___x_5212_ = v___x_5166_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
else
{
lean_object* v___x_5214_; uint8_t v___x_5215_; 
lean_del_object(v___x_5166_);
v___x_5214_ = lean_box(0);
v___x_5215_ = lean_nat_dec_le(v___x_5208_, v___x_5208_);
if (v___x_5215_ == 0)
{
if (v___x_5209_ == 0)
{
lean_dec(v_a_5207_);
goto v___jp_5131_;
}
else
{
size_t v___x_5216_; size_t v___x_5217_; lean_object* v___x_5218_; 
v___x_5216_ = ((size_t)0ULL);
v___x_5217_ = lean_usize_of_nat(v___x_5208_);
v___x_5218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5207_, v___x_5216_, v___x_5217_, v___x_5214_, v___y_5129_);
lean_dec(v_a_5207_);
if (lean_obj_tag(v___x_5218_) == 0)
{
lean_dec_ref_known(v___x_5218_, 1);
goto v___jp_5131_;
}
else
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5226_; 
v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5221_ = v___x_5218_;
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5218_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5224_; 
if (v_isShared_5222_ == 0)
{
v___x_5224_ = v___x_5221_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5219_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
}
else
{
size_t v___x_5227_; size_t v___x_5228_; lean_object* v___x_5229_; 
v___x_5227_ = ((size_t)0ULL);
v___x_5228_ = lean_usize_of_nat(v___x_5208_);
v___x_5229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5207_, v___x_5227_, v___x_5228_, v___x_5214_, v___y_5129_);
lean_dec(v_a_5207_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_dec_ref_known(v___x_5229_, 1);
goto v___jp_5131_;
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5229_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5229_);
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
}
}
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
lean_dec_ref(v_packages_5141_);
lean_del_object(v___x_5138_);
lean_dec_ref(v_depIdxs_5136_);
lean_dec_ref(v_ws_5135_);
lean_dec_ref(v_leanOpts_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v_pkg_5120_);
v_a_5239_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5163_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5163_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
else
{
uint8_t v___x_5247_; 
lean_inc(v_baseName_5155_);
lean_inc(v_wsIdx_5154_);
lean_dec(v___x_5159_);
lean_dec_ref(v_packages_5141_);
lean_del_object(v___x_5138_);
lean_dec_ref(v_depIdxs_5136_);
lean_dec_ref(v_ws_5135_);
lean_dec_ref(v_leanOpts_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v_pkg_5120_);
v___x_5247_ = lean_nat_dec_eq(v_wsIdx_5154_, v___x_5146_);
lean_dec(v_wsIdx_5154_);
if (v___x_5247_ == 0)
{
lean_object* v___x_5248_; uint8_t v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; uint8_t v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5249_ = 1;
lean_inc(v_name_5156_);
v___x_5250_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5156_, v___x_5249_);
v___x_5251_ = lean_string_append(v___x_5248_, v___x_5250_);
lean_dec_ref(v___x_5250_);
v___x_5252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5253_ = lean_string_append(v___x_5251_, v___x_5252_);
v___x_5254_ = l_Lean_Name_toString(v_baseName_5155_, v___x_5247_);
v___x_5255_ = lean_string_append(v___x_5253_, v___x_5254_);
lean_dec_ref(v___x_5254_);
v___x_5256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5257_ = lean_string_append(v___x_5255_, v___x_5256_);
v___x_5258_ = 3;
v___x_5259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5259_, 0, v___x_5257_);
lean_ctor_set_uint8(v___x_5259_, sizeof(void*)*1, v___x_5258_);
lean_inc_ref(v___y_5129_);
v___x_5260_ = lean_apply_2(v___y_5129_, v___x_5259_, lean_box(0));
v___x_5261_ = lean_box(0);
v___x_5262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5262_, 0, v___x_5261_);
return v___x_5262_;
}
else
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; uint8_t v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; 
lean_dec(v_baseName_5155_);
v___x_5263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5156_);
v___x_5264_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5156_, v___x_5247_);
v___x_5265_ = lean_string_append(v___x_5263_, v___x_5264_);
v___x_5266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5267_ = lean_string_append(v___x_5265_, v___x_5266_);
v___x_5268_ = lean_string_append(v___x_5267_, v___x_5264_);
lean_dec_ref(v___x_5264_);
v___x_5269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5270_ = lean_string_append(v___x_5268_, v___x_5269_);
v___x_5271_ = 3;
v___x_5272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5272_, 0, v___x_5270_);
lean_ctor_set_uint8(v___x_5272_, sizeof(void*)*1, v___x_5271_);
lean_inc_ref(v___y_5129_);
v___x_5273_ = lean_apply_2(v___y_5129_, v___x_5272_, lean_box(0));
v___x_5274_ = lean_box(0);
v___x_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5274_);
return v___x_5275_;
}
}
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
lean_inc(v_baseName_5155_);
lean_dec_ref(v_packages_5141_);
lean_del_object(v___x_5138_);
lean_dec_ref(v_depIdxs_5136_);
lean_dec_ref(v_ws_5135_);
lean_dec_ref(v_leanOpts_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v_pkg_5120_);
v___x_5276_ = l_Lean_Name_toString(v_baseName_5155_, v___x_5134_);
v___x_5277_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5278_ = lean_string_append(v___x_5276_, v___x_5277_);
v___x_5279_ = 3;
v___x_5280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5280_, 0, v___x_5278_);
lean_ctor_set_uint8(v___x_5280_, sizeof(void*)*1, v___x_5279_);
lean_inc_ref(v___y_5129_);
v___x_5281_ = lean_apply_2(v___y_5129_, v___x_5280_, lean_box(0));
v___x_5282_ = lean_box(0);
v___x_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
return v___x_5283_;
}
}
}
}
else
{
lean_object* v___x_5285_; 
lean_dec_ref(v_leanOpts_5123_);
lean_dec_ref(v___y_5122_);
lean_dec_ref(v_pkg_5120_);
v___x_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5285_, 0, v_b_5128_);
return v___x_5285_;
}
v___jp_5131_:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = lean_box(0);
v___x_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5132_);
return v___x_5133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5286_, lean_object* v_pkg_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v_leanOpts_5290_, lean_object* v_reconfigure_5291_, lean_object* v_as_5292_, lean_object* v_i_5293_, lean_object* v_stop_5294_, lean_object* v_b_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_){
_start:
{
uint8_t v_reconfigure_boxed_5298_; size_t v_i_boxed_5299_; size_t v_stop_boxed_5300_; lean_object* v_res_5301_; 
v_reconfigure_boxed_5298_ = lean_unbox(v_reconfigure_5291_);
v_i_boxed_5299_ = lean_unbox_usize(v_i_5293_);
lean_dec(v_i_5293_);
v_stop_boxed_5300_ = lean_unbox_usize(v_stop_5294_);
lean_dec(v_stop_5294_);
v_res_5301_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5286_, v_pkg_5287_, v___y_5288_, v___y_5289_, v_leanOpts_5290_, v_reconfigure_boxed_5298_, v_as_5292_, v_i_boxed_5299_, v_stop_boxed_5300_, v_b_5295_, v___y_5296_);
lean_dec_ref(v___y_5296_);
lean_dec_ref(v_as_5292_);
lean_dec(v___y_5288_);
lean_dec(v_start_5286_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v_leanOpts_5304_, uint8_t v_reconfigure_5305_, lean_object* v_ws_5306_, lean_object* v_i_5307_, lean_object* v_next_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v_packages_5311_; lean_object* v_pkg_5312_; lean_object* v_ws_5314_; lean_object* v_depIdxs_5315_; lean_object* v___y_5316_; lean_object* v_____x_5326_; lean_object* v___y_5327_; lean_object* v_depConfigs_5330_; lean_object* v_start_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v_s_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; 
v_packages_5311_ = lean_ctor_get(v_ws_5306_, 4);
v_pkg_5312_ = lean_array_fget(v_packages_5311_, v_i_5307_);
lean_dec(v_i_5307_);
v_depConfigs_5330_ = lean_ctor_get(v_pkg_5312_, 12);
v_start_5331_ = lean_array_get_size(v_packages_5311_);
v___x_5332_ = lean_array_get_size(v_depConfigs_5330_);
v___x_5333_ = lean_mk_empty_array_with_capacity(v___x_5332_);
lean_inc_ref(v___x_5333_);
lean_inc_ref(v_ws_5306_);
v_s_5334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5334_, 0, v_ws_5306_);
lean_ctor_set(v_s_5334_, 1, v___x_5333_);
v___x_5335_ = lean_unsigned_to_nat(0u);
v___x_5336_ = lean_nat_dec_le(v___x_5332_, v___x_5332_);
if (v___x_5336_ == 0)
{
uint8_t v___x_5337_; 
v___x_5337_ = lean_nat_dec_lt(v___x_5335_, v___x_5332_);
if (v___x_5337_ == 0)
{
lean_object* v_ws_5338_; lean_object* v_packages_5339_; lean_object* v___x_5340_; uint8_t v___x_5341_; 
lean_dec_ref_known(v_s_5334_, 2);
v_ws_5338_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5306_, v_pkg_5312_, v___x_5333_);
v_packages_5339_ = lean_ctor_get(v_ws_5338_, 4);
lean_inc_ref(v_packages_5339_);
v___x_5340_ = lean_array_get_size(v_packages_5339_);
lean_dec_ref(v_packages_5339_);
v___x_5341_ = lean_nat_dec_lt(v_next_5308_, v___x_5340_);
if (v___x_5341_ == 0)
{
lean_object* v___x_5342_; 
lean_dec(v_next_5308_);
lean_dec_ref(v_leanOpts_5304_);
lean_dec_ref(v___y_5303_);
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v_ws_5338_);
return v___x_5342_;
}
else
{
lean_object* v___x_5343_; lean_object* v___x_5344_; 
v___x_5343_ = lean_unsigned_to_nat(1u);
v___x_5344_ = lean_nat_add(v_next_5308_, v___x_5343_);
v_ws_5306_ = v_ws_5338_;
v_i_5307_ = v_next_5308_;
v_next_5308_ = v___x_5344_;
goto _start;
}
}
else
{
size_t v___x_5346_; size_t v___x_5347_; lean_object* v___x_5348_; 
lean_dec_ref(v___x_5333_);
lean_dec_ref(v_ws_5306_);
v___x_5346_ = lean_usize_of_nat(v___x_5332_);
v___x_5347_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5304_);
lean_inc_ref(v___y_5303_);
lean_inc(v_pkg_5312_);
v___x_5348_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5331_, v_pkg_5312_, v___y_5302_, v___y_5303_, v_leanOpts_5304_, v_reconfigure_5305_, v_depConfigs_5330_, v___x_5346_, v___x_5347_, v_s_5334_, v___y_5309_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
lean_inc(v_a_5349_);
lean_dec_ref_known(v___x_5348_, 1);
v_____x_5326_ = v_a_5349_;
v___y_5327_ = v___y_5309_;
goto v___jp_5325_;
}
else
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
lean_dec(v_pkg_5312_);
lean_dec(v_next_5308_);
lean_dec_ref(v_leanOpts_5304_);
lean_dec_ref(v___y_5303_);
v_a_5350_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5348_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v___x_5348_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
}
}
else
{
uint8_t v___x_5358_; 
v___x_5358_ = lean_nat_dec_lt(v___x_5335_, v___x_5332_);
if (v___x_5358_ == 0)
{
lean_dec_ref_known(v_s_5334_, 2);
v_ws_5314_ = v_ws_5306_;
v_depIdxs_5315_ = v___x_5333_;
v___y_5316_ = v___y_5309_;
goto v___jp_5313_;
}
else
{
size_t v___x_5359_; size_t v___x_5360_; lean_object* v___x_5361_; 
lean_dec_ref(v___x_5333_);
lean_dec_ref(v_ws_5306_);
v___x_5359_ = lean_usize_of_nat(v___x_5332_);
v___x_5360_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5304_);
lean_inc_ref(v___y_5303_);
lean_inc(v_pkg_5312_);
v___x_5361_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5331_, v_pkg_5312_, v___y_5302_, v___y_5303_, v_leanOpts_5304_, v_reconfigure_5305_, v_depConfigs_5330_, v___x_5359_, v___x_5360_, v_s_5334_, v___y_5309_);
if (lean_obj_tag(v___x_5361_) == 0)
{
lean_object* v_a_5362_; 
v_a_5362_ = lean_ctor_get(v___x_5361_, 0);
lean_inc(v_a_5362_);
lean_dec_ref_known(v___x_5361_, 1);
v_____x_5326_ = v_a_5362_;
v___y_5327_ = v___y_5309_;
goto v___jp_5325_;
}
else
{
lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5370_; 
lean_dec(v_pkg_5312_);
lean_dec(v_next_5308_);
lean_dec_ref(v_leanOpts_5304_);
lean_dec_ref(v___y_5303_);
v_a_5363_ = lean_ctor_get(v___x_5361_, 0);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5361_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5365_ = v___x_5361_;
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5361_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5370_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5368_; 
if (v_isShared_5366_ == 0)
{
v___x_5368_ = v___x_5365_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5363_);
v___x_5368_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
return v___x_5368_;
}
}
}
}
}
v___jp_5313_:
{
lean_object* v_ws_5317_; lean_object* v_packages_5318_; lean_object* v___x_5319_; uint8_t v___x_5320_; 
v_ws_5317_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5314_, v_pkg_5312_, v_depIdxs_5315_);
v_packages_5318_ = lean_ctor_get(v_ws_5317_, 4);
lean_inc_ref(v_packages_5318_);
v___x_5319_ = lean_array_get_size(v_packages_5318_);
lean_dec_ref(v_packages_5318_);
v___x_5320_ = lean_nat_dec_lt(v_next_5308_, v___x_5319_);
if (v___x_5320_ == 0)
{
lean_object* v___x_5321_; 
lean_dec(v_next_5308_);
lean_dec_ref(v_leanOpts_5304_);
lean_dec_ref(v___y_5303_);
v___x_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5321_, 0, v_ws_5317_);
return v___x_5321_;
}
else
{
lean_object* v___x_5322_; lean_object* v___x_5323_; 
v___x_5322_ = lean_unsigned_to_nat(1u);
v___x_5323_ = lean_nat_add(v_next_5308_, v___x_5322_);
v_ws_5306_ = v_ws_5317_;
v_i_5307_ = v_next_5308_;
v_next_5308_ = v___x_5323_;
v___y_5309_ = v___y_5316_;
goto _start;
}
}
v___jp_5325_:
{
lean_object* v_ws_5328_; lean_object* v_depIdxs_5329_; 
v_ws_5328_ = lean_ctor_get(v_____x_5326_, 0);
lean_inc_ref(v_ws_5328_);
v_depIdxs_5329_ = lean_ctor_get(v_____x_5326_, 1);
lean_inc_ref(v_depIdxs_5329_);
lean_dec_ref(v_____x_5326_);
v_ws_5314_ = v_ws_5328_;
v_depIdxs_5315_ = v_depIdxs_5329_;
v___y_5316_ = v___y_5327_;
goto v___jp_5313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v_leanOpts_5373_, lean_object* v_reconfigure_5374_, lean_object* v_ws_5375_, lean_object* v_i_5376_, lean_object* v_next_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
uint8_t v_reconfigure_boxed_5380_; lean_object* v_res_5381_; 
v_reconfigure_boxed_5380_ = lean_unbox(v_reconfigure_5374_);
v_res_5381_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5371_, v___y_5372_, v_leanOpts_5373_, v_reconfigure_boxed_5380_, v_ws_5375_, v_i_5376_, v_next_5377_, v___y_5378_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5371_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5382_, size_t v_i_5383_, size_t v_stop_5384_, lean_object* v_b_5385_){
_start:
{
uint8_t v___x_5386_; 
v___x_5386_ = lean_usize_dec_eq(v_i_5383_, v_stop_5384_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; lean_object* v_name_5388_; lean_object* v___x_5389_; size_t v___x_5390_; size_t v___x_5391_; 
v___x_5387_ = lean_array_uget_borrowed(v_as_5382_, v_i_5383_);
v_name_5388_ = lean_ctor_get(v___x_5387_, 0);
lean_inc(v___x_5387_);
lean_inc(v_name_5388_);
v___x_5389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5388_, v___x_5387_, v_b_5385_);
v___x_5390_ = ((size_t)1ULL);
v___x_5391_ = lean_usize_add(v_i_5383_, v___x_5390_);
v_i_5383_ = v___x_5391_;
v_b_5385_ = v___x_5389_;
goto _start;
}
else
{
return v_b_5385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5393_, lean_object* v_i_5394_, lean_object* v_stop_5395_, lean_object* v_b_5396_){
_start:
{
size_t v_i_boxed_5397_; size_t v_stop_boxed_5398_; lean_object* v_res_5399_; 
v_i_boxed_5397_ = lean_unbox_usize(v_i_5394_);
lean_dec(v_i_5394_);
v_stop_boxed_5398_ = lean_unbox_usize(v_stop_5395_);
lean_dec(v_stop_5395_);
v_res_5399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5393_, v_i_boxed_5397_, v_stop_boxed_5398_, v_b_5396_);
lean_dec_ref(v_as_5393_);
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5400_, size_t v_i_5401_, size_t v_stop_5402_, lean_object* v_b_5403_){
_start:
{
uint8_t v___x_5404_; 
v___x_5404_ = lean_usize_dec_eq(v_i_5401_, v_stop_5402_);
if (v___x_5404_ == 0)
{
lean_object* v___x_5405_; lean_object* v_name_5406_; lean_object* v___x_5407_; size_t v___x_5408_; size_t v___x_5409_; lean_object* v___x_5410_; 
v___x_5405_ = lean_array_uget_borrowed(v_as_5400_, v_i_5401_);
v_name_5406_ = lean_ctor_get(v___x_5405_, 0);
lean_inc(v___x_5405_);
lean_inc(v_name_5406_);
v___x_5407_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5406_, v___x_5405_, v_b_5403_);
v___x_5408_ = ((size_t)1ULL);
v___x_5409_ = lean_usize_add(v_i_5401_, v___x_5408_);
v___x_5410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5400_, v___x_5409_, v_stop_5402_, v___x_5407_);
return v___x_5410_;
}
else
{
return v_b_5403_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5411_, lean_object* v_i_5412_, lean_object* v_stop_5413_, lean_object* v_b_5414_){
_start:
{
size_t v_i_boxed_5415_; size_t v_stop_boxed_5416_; lean_object* v_res_5417_; 
v_i_boxed_5415_ = lean_unbox_usize(v_i_5412_);
lean_dec(v_i_5412_);
v_stop_boxed_5416_ = lean_unbox_usize(v_stop_5413_);
lean_dec(v_stop_5413_);
v_res_5417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5411_, v_i_boxed_5415_, v_stop_boxed_5416_, v_b_5414_);
lean_dec_ref(v_as_5411_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5427_, lean_object* v_manifest_5428_, lean_object* v_leanOpts_5429_, uint8_t v_reconfigure_5430_, lean_object* v_overrides_5431_, lean_object* v_a_5432_){
_start:
{
lean_object* v___y_5435_; lean_object* v___y_5436_; lean_object* v___y_5437_; lean_object* v___y_5438_; lean_object* v___y_5439_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v___y_5470_; lean_object* v___y_5471_; lean_object* v___y_5472_; lean_object* v___y_5473_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v_packagesDir_x3f_5530_; lean_object* v_packages_5531_; lean_object* v___y_5533_; lean_object* v___y_5534_; lean_object* v___y_5547_; uint8_t v___y_5556_; lean_object* v___x_5559_; lean_object* v___x_5560_; uint8_t v___x_5561_; uint8_t v___x_5562_; 
v_packagesDir_x3f_5530_ = lean_ctor_get(v_manifest_5428_, 2);
lean_inc(v_packagesDir_x3f_5530_);
v_packages_5531_ = lean_ctor_get(v_manifest_5428_, 3);
lean_inc_ref(v_packages_5531_);
lean_dec_ref(v_manifest_5428_);
v___x_5559_ = lean_array_get_size(v_packages_5531_);
v___x_5560_ = lean_unsigned_to_nat(0u);
v___x_5561_ = lean_nat_dec_eq(v___x_5559_, v___x_5560_);
v___x_5562_ = lean_bool_not(v___x_5561_);
if (v___x_5562_ == 0)
{
v___y_5556_ = v___x_5562_;
goto v___jp_5555_;
}
else
{
lean_object* v_packages_5563_; lean_object* v___x_5564_; lean_object* v_config_5565_; lean_object* v_toWorkspaceConfig_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; uint8_t v___x_5570_; uint8_t v___x_5571_; 
v_packages_5563_ = lean_ctor_get(v_ws_5427_, 4);
v___x_5564_ = lean_array_fget_borrowed(v_packages_5563_, v___x_5560_);
v_config_5565_ = lean_ctor_get(v___x_5564_, 6);
v_toWorkspaceConfig_5566_ = lean_ctor_get(v_config_5565_, 0);
lean_inc_ref(v_toWorkspaceConfig_5566_);
v___x_5567_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5566_);
v___x_5568_ = l_Lake_mkRelPathString(v___x_5567_);
v___x_5569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5569_, 0, v___x_5568_);
v___x_5570_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5530_, v___x_5569_);
lean_dec_ref_known(v___x_5569_, 1);
v___x_5571_ = lean_bool_not(v___x_5570_);
v___y_5556_ = v___x_5571_;
goto v___jp_5555_;
}
v___jp_5434_:
{
lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5440_ = lean_array_get_size(v___y_5439_);
lean_dec_ref(v___y_5439_);
v___x_5441_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5438_, v___y_5437_, v_leanOpts_5429_, v_reconfigure_5430_, v_ws_5427_, v___y_5436_, v___x_5440_, v___y_5435_);
lean_dec(v___y_5438_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5450_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5450_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5450_ == 0)
{
v___x_5444_ = v___x_5441_;
v_isShared_5445_ = v_isSharedCheck_5450_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5441_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5450_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5446_; lean_object* v___x_5448_; 
v___x_5446_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5442_);
if (v_isShared_5445_ == 0)
{
lean_ctor_set(v___x_5444_, 0, v___x_5446_);
v___x_5448_ = v___x_5444_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v___x_5446_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
else
{
return v___x_5441_;
}
}
v___jp_5451_:
{
if (lean_obj_tag(v___y_5458_) == 0)
{
lean_dec_ref(v___y_5456_);
v___y_5435_ = v___y_5453_;
v___y_5436_ = v___y_5454_;
v___y_5437_ = v___y_5455_;
v___y_5438_ = v___y_5458_;
v___y_5439_ = v___y_5457_;
goto v___jp_5434_;
}
else
{
lean_object* v___x_5459_; uint8_t v___x_5460_; uint8_t v___x_5461_; 
v___x_5459_ = lean_array_get_size(v___y_5456_);
lean_dec_ref(v___y_5456_);
v___x_5460_ = lean_nat_dec_eq(v___x_5459_, v___y_5452_);
v___x_5461_ = lean_bool_not(v___x_5460_);
if (v___x_5461_ == 0)
{
v___y_5435_ = v___y_5453_;
v___y_5436_ = v___y_5454_;
v___y_5437_ = v___y_5455_;
v___y_5438_ = v___y_5458_;
v___y_5439_ = v___y_5457_;
goto v___jp_5434_;
}
else
{
lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
lean_dec_ref(v___y_5457_);
lean_dec_ref(v___y_5455_);
lean_dec(v___y_5454_);
lean_dec_ref(v_leanOpts_5429_);
lean_dec_ref(v_ws_5427_);
v___x_5462_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5453_);
v___x_5463_ = lean_apply_2(v___y_5453_, v___x_5462_, lean_box(0));
v___x_5464_ = lean_box(0);
v___x_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5465_, 0, v___x_5464_);
return v___x_5465_;
}
}
}
v___jp_5466_:
{
lean_object* v___x_5474_; uint8_t v___x_5475_; 
v___x_5474_ = lean_array_get_size(v_overrides_5431_);
v___x_5475_ = lean_nat_dec_lt(v___y_5467_, v___x_5474_);
if (v___x_5475_ == 0)
{
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5468_;
v___y_5454_ = v___y_5469_;
v___y_5455_ = v___y_5470_;
v___y_5456_ = v___y_5471_;
v___y_5457_ = v___y_5472_;
v___y_5458_ = v___y_5473_;
goto v___jp_5451_;
}
else
{
uint8_t v___x_5476_; 
v___x_5476_ = lean_nat_dec_le(v___x_5474_, v___x_5474_);
if (v___x_5476_ == 0)
{
if (v___x_5475_ == 0)
{
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5468_;
v___y_5454_ = v___y_5469_;
v___y_5455_ = v___y_5470_;
v___y_5456_ = v___y_5471_;
v___y_5457_ = v___y_5472_;
v___y_5458_ = v___y_5473_;
goto v___jp_5451_;
}
else
{
size_t v___x_5477_; size_t v___x_5478_; lean_object* v___x_5479_; 
v___x_5477_ = ((size_t)0ULL);
v___x_5478_ = lean_usize_of_nat(v___x_5474_);
v___x_5479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5431_, v___x_5477_, v___x_5478_, v___y_5473_);
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5468_;
v___y_5454_ = v___y_5469_;
v___y_5455_ = v___y_5470_;
v___y_5456_ = v___y_5471_;
v___y_5457_ = v___y_5472_;
v___y_5458_ = v___x_5479_;
goto v___jp_5451_;
}
}
else
{
size_t v___x_5480_; size_t v___x_5481_; lean_object* v___x_5482_; 
v___x_5480_ = ((size_t)0ULL);
v___x_5481_ = lean_usize_of_nat(v___x_5474_);
v___x_5482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5431_, v___x_5480_, v___x_5481_, v___y_5473_);
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5468_;
v___y_5454_ = v___y_5469_;
v___y_5455_ = v___y_5470_;
v___y_5456_ = v___y_5471_;
v___y_5457_ = v___y_5472_;
v___y_5458_ = v___x_5482_;
goto v___jp_5451_;
}
}
}
v___jp_5483_:
{
lean_object* v_packages_5488_; lean_object* v___x_5489_; lean_object* v_wsIdx_5490_; lean_object* v_dir_5491_; lean_object* v_depConfigs_5492_; lean_object* v___x_5493_; 
v_packages_5488_ = lean_ctor_get(v_ws_5427_, 4);
v___x_5489_ = lean_array_fget_borrowed(v_packages_5488_, v___y_5484_);
v_wsIdx_5490_ = lean_ctor_get(v___x_5489_, 0);
v_dir_5491_ = lean_ctor_get(v___x_5489_, 4);
v_depConfigs_5492_ = lean_ctor_get(v___x_5489_, 12);
v___x_5493_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5487_, v_depConfigs_5492_, v___y_5485_);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
lean_dec_ref_known(v___x_5493_, 1);
v___x_5494_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5491_);
v___x_5495_ = l_Lake_joinRelative(v_dir_5491_, v___x_5494_);
v___x_5496_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5497_ = l_Lake_joinRelative(v___x_5495_, v___x_5496_);
v___x_5498_ = l_Lake_Manifest_tryLoadEntries(v___x_5497_);
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_object* v_a_5499_; lean_object* v___x_5500_; uint8_t v___x_5501_; 
v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
lean_inc(v_a_5499_);
lean_dec_ref_known(v___x_5498_, 1);
v___x_5500_ = lean_array_get_size(v_a_5499_);
v___x_5501_ = lean_nat_dec_lt(v___y_5484_, v___x_5500_);
if (v___x_5501_ == 0)
{
lean_dec(v_a_5499_);
lean_inc_ref(v_packages_5488_);
lean_inc_ref(v_depConfigs_5492_);
lean_inc(v_wsIdx_5490_);
v___y_5467_ = v___y_5484_;
v___y_5468_ = v___y_5485_;
v___y_5469_ = v_wsIdx_5490_;
v___y_5470_ = v___y_5486_;
v___y_5471_ = v_depConfigs_5492_;
v___y_5472_ = v_packages_5488_;
v___y_5473_ = v___y_5487_;
goto v___jp_5466_;
}
else
{
uint8_t v___x_5502_; 
v___x_5502_ = lean_nat_dec_le(v___x_5500_, v___x_5500_);
if (v___x_5502_ == 0)
{
if (v___x_5501_ == 0)
{
lean_dec(v_a_5499_);
lean_inc_ref(v_packages_5488_);
lean_inc_ref(v_depConfigs_5492_);
lean_inc(v_wsIdx_5490_);
v___y_5467_ = v___y_5484_;
v___y_5468_ = v___y_5485_;
v___y_5469_ = v_wsIdx_5490_;
v___y_5470_ = v___y_5486_;
v___y_5471_ = v_depConfigs_5492_;
v___y_5472_ = v_packages_5488_;
v___y_5473_ = v___y_5487_;
goto v___jp_5466_;
}
else
{
size_t v___x_5503_; size_t v___x_5504_; lean_object* v___x_5505_; 
v___x_5503_ = ((size_t)0ULL);
v___x_5504_ = lean_usize_of_nat(v___x_5500_);
v___x_5505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5499_, v___x_5503_, v___x_5504_, v___y_5487_);
lean_dec(v_a_5499_);
lean_inc_ref(v_packages_5488_);
lean_inc_ref(v_depConfigs_5492_);
lean_inc(v_wsIdx_5490_);
v___y_5467_ = v___y_5484_;
v___y_5468_ = v___y_5485_;
v___y_5469_ = v_wsIdx_5490_;
v___y_5470_ = v___y_5486_;
v___y_5471_ = v_depConfigs_5492_;
v___y_5472_ = v_packages_5488_;
v___y_5473_ = v___x_5505_;
goto v___jp_5466_;
}
}
else
{
size_t v___x_5506_; size_t v___x_5507_; lean_object* v___x_5508_; 
v___x_5506_ = ((size_t)0ULL);
v___x_5507_ = lean_usize_of_nat(v___x_5500_);
v___x_5508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5499_, v___x_5506_, v___x_5507_, v___y_5487_);
lean_dec(v_a_5499_);
lean_inc_ref(v_packages_5488_);
lean_inc_ref(v_depConfigs_5492_);
lean_inc(v_wsIdx_5490_);
v___y_5467_ = v___y_5484_;
v___y_5468_ = v___y_5485_;
v___y_5469_ = v_wsIdx_5490_;
v___y_5470_ = v___y_5486_;
v___y_5471_ = v_depConfigs_5492_;
v___y_5472_ = v_packages_5488_;
v___y_5473_ = v___x_5508_;
goto v___jp_5466_;
}
}
}
else
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5521_; 
lean_dec(v___y_5487_);
lean_dec_ref(v___y_5486_);
lean_dec_ref(v_leanOpts_5429_);
lean_dec_ref(v_ws_5427_);
v_a_5509_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5511_ = v___x_5498_;
v_isShared_5512_ = v_isSharedCheck_5521_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5498_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5521_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5513_; uint8_t v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5519_; 
v___x_5513_ = lean_io_error_to_string(v_a_5509_);
v___x_5514_ = 3;
v___x_5515_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5515_, 0, v___x_5513_);
lean_ctor_set_uint8(v___x_5515_, sizeof(void*)*1, v___x_5514_);
lean_inc_ref(v___y_5485_);
v___x_5516_ = lean_apply_2(v___y_5485_, v___x_5515_, lean_box(0));
v___x_5517_ = lean_box(0);
if (v_isShared_5512_ == 0)
{
lean_ctor_set(v___x_5511_, 0, v___x_5517_);
v___x_5519_ = v___x_5511_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5517_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
}
else
{
lean_object* v_a_5522_; lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5529_; 
lean_dec(v___y_5487_);
lean_dec_ref(v___y_5486_);
lean_dec_ref(v_leanOpts_5429_);
lean_dec_ref(v_ws_5427_);
v_a_5522_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5529_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5529_ == 0)
{
v___x_5524_ = v___x_5493_;
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
else
{
lean_inc(v_a_5522_);
lean_dec(v___x_5493_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5529_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5527_; 
if (v_isShared_5525_ == 0)
{
v___x_5527_ = v___x_5524_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_a_5522_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
return v___x_5527_;
}
}
}
}
v___jp_5532_:
{
lean_object* v_pkgEntries_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; uint8_t v___x_5538_; 
v_pkgEntries_5535_ = lean_box(1);
v___x_5536_ = lean_unsigned_to_nat(0u);
v___x_5537_ = lean_array_get_size(v_packages_5531_);
v___x_5538_ = lean_nat_dec_lt(v___x_5536_, v___x_5537_);
if (v___x_5538_ == 0)
{
lean_dec_ref(v_packages_5531_);
v___y_5484_ = v___x_5536_;
v___y_5485_ = v___y_5533_;
v___y_5486_ = v___y_5534_;
v___y_5487_ = v_pkgEntries_5535_;
goto v___jp_5483_;
}
else
{
uint8_t v___x_5539_; 
v___x_5539_ = lean_nat_dec_le(v___x_5537_, v___x_5537_);
if (v___x_5539_ == 0)
{
if (v___x_5538_ == 0)
{
lean_dec_ref(v_packages_5531_);
v___y_5484_ = v___x_5536_;
v___y_5485_ = v___y_5533_;
v___y_5486_ = v___y_5534_;
v___y_5487_ = v_pkgEntries_5535_;
goto v___jp_5483_;
}
else
{
size_t v___x_5540_; size_t v___x_5541_; lean_object* v___x_5542_; 
v___x_5540_ = ((size_t)0ULL);
v___x_5541_ = lean_usize_of_nat(v___x_5537_);
v___x_5542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5531_, v___x_5540_, v___x_5541_, v_pkgEntries_5535_);
lean_dec_ref(v_packages_5531_);
v___y_5484_ = v___x_5536_;
v___y_5485_ = v___y_5533_;
v___y_5486_ = v___y_5534_;
v___y_5487_ = v___x_5542_;
goto v___jp_5483_;
}
}
else
{
size_t v___x_5543_; size_t v___x_5544_; lean_object* v___x_5545_; 
v___x_5543_ = ((size_t)0ULL);
v___x_5544_ = lean_usize_of_nat(v___x_5537_);
v___x_5545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5531_, v___x_5543_, v___x_5544_, v_pkgEntries_5535_);
lean_dec_ref(v_packages_5531_);
v___y_5484_ = v___x_5536_;
v___y_5485_ = v___y_5533_;
v___y_5486_ = v___y_5534_;
v___y_5487_ = v___x_5545_;
goto v___jp_5483_;
}
}
}
v___jp_5546_:
{
if (lean_obj_tag(v_packagesDir_x3f_5530_) == 0)
{
lean_object* v_packages_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v_config_5551_; lean_object* v_toWorkspaceConfig_5552_; lean_object* v___x_5553_; 
v_packages_5548_ = lean_ctor_get(v_ws_5427_, 4);
v___x_5549_ = lean_unsigned_to_nat(0u);
v___x_5550_ = lean_array_fget_borrowed(v_packages_5548_, v___x_5549_);
v_config_5551_ = lean_ctor_get(v___x_5550_, 6);
v_toWorkspaceConfig_5552_ = lean_ctor_get(v_config_5551_, 0);
lean_inc_ref(v_toWorkspaceConfig_5552_);
v___x_5553_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5552_);
v___y_5533_ = v___y_5547_;
v___y_5534_ = v___x_5553_;
goto v___jp_5532_;
}
else
{
lean_object* v_val_5554_; 
v_val_5554_ = lean_ctor_get(v_packagesDir_x3f_5530_, 0);
lean_inc(v_val_5554_);
lean_dec_ref_known(v_packagesDir_x3f_5530_, 1);
v___y_5533_ = v___y_5547_;
v___y_5534_ = v_val_5554_;
goto v___jp_5532_;
}
}
v___jp_5555_:
{
if (v___y_5556_ == 0)
{
v___y_5547_ = v_a_5432_;
goto v___jp_5546_;
}
else
{
lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5557_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5432_);
v___x_5558_ = lean_apply_2(v_a_5432_, v___x_5557_, lean_box(0));
v___y_5547_ = v_a_5432_;
goto v___jp_5546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5572_, lean_object* v_manifest_5573_, lean_object* v_leanOpts_5574_, lean_object* v_reconfigure_5575_, lean_object* v_overrides_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_){
_start:
{
uint8_t v_reconfigure_boxed_5579_; lean_object* v_res_5580_; 
v_reconfigure_boxed_5579_ = lean_unbox(v_reconfigure_5575_);
v_res_5580_ = l_Lake_Workspace_materializeDeps(v_ws_5572_, v_manifest_5573_, v_leanOpts_5574_, v_reconfigure_boxed_5579_, v_overrides_5576_, v_a_5577_);
lean_dec_ref(v_a_5577_);
lean_dec_ref(v_overrides_5576_);
return v_res_5580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v_leanOpts_5583_, uint8_t v_reconfigure_5584_, lean_object* v_ws_5585_, lean_object* v_i_5586_, lean_object* v_i__lt_5587_, lean_object* v_next_5588_, lean_object* v_lt__next_5589_, lean_object* v___y_5590_){
_start:
{
lean_object* v___x_5592_; 
v___x_5592_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5581_, v___y_5582_, v_leanOpts_5583_, v_reconfigure_5584_, v_ws_5585_, v_i_5586_, v_next_5588_, v___y_5590_);
return v___x_5592_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v_leanOpts_5595_, lean_object* v_reconfigure_5596_, lean_object* v_ws_5597_, lean_object* v_i_5598_, lean_object* v_i__lt_5599_, lean_object* v_next_5600_, lean_object* v_lt__next_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
uint8_t v_reconfigure_boxed_5604_; lean_object* v_res_5605_; 
v_reconfigure_boxed_5604_ = lean_unbox(v_reconfigure_5596_);
v_res_5605_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5593_, v___y_5594_, v_leanOpts_5595_, v_reconfigure_boxed_5604_, v_ws_5597_, v_i_5598_, v_i__lt_5599_, v_next_5600_, v_lt__next_5601_, v___y_5602_);
lean_dec_ref(v___y_5602_);
lean_dec(v___y_5593_);
return v_res_5605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5606_, lean_object* v_pkg_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v_leanOpts_5610_, uint8_t v_reconfigure_5611_, lean_object* v_as_5612_, size_t v_i_5613_, size_t v_stop_5614_, lean_object* v_b_5615_, lean_object* v___y_5616_){
_start:
{
lean_object* v___x_5618_; 
v___x_5618_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5607_, v___y_5608_, v___y_5609_, v_leanOpts_5610_, v_reconfigure_5611_, v_as_5612_, v_i_5613_, v_stop_5614_, v_b_5615_, v___y_5616_);
return v___x_5618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5619_, lean_object* v_pkg_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v_leanOpts_5623_, lean_object* v_reconfigure_5624_, lean_object* v_as_5625_, lean_object* v_i_5626_, lean_object* v_stop_5627_, lean_object* v_b_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_){
_start:
{
uint8_t v_reconfigure_boxed_5631_; size_t v_i_boxed_5632_; size_t v_stop_boxed_5633_; lean_object* v_res_5634_; 
v_reconfigure_boxed_5631_ = lean_unbox(v_reconfigure_5624_);
v_i_boxed_5632_ = lean_unbox_usize(v_i_5626_);
lean_dec(v_i_5626_);
v_stop_boxed_5633_ = lean_unbox_usize(v_stop_5627_);
lean_dec(v_stop_5627_);
v_res_5634_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5619_, v_pkg_5620_, v___y_5621_, v___y_5622_, v_leanOpts_5623_, v_reconfigure_boxed_5631_, v_as_5625_, v_i_boxed_5632_, v_stop_boxed_5633_, v_b_5628_, v___y_5629_);
lean_dec_ref(v___y_5629_);
lean_dec_ref(v_as_5625_);
lean_dec(v___y_5621_);
lean_dec(v_start_5619_);
return v_res_5634_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Resolve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

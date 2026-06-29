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
lean_object* v___y_1274_; lean_object* v___y_1279_; lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v_packages_1300_; lean_object* v___x_1301_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v_val_1306_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___x_1354_; lean_object* v_baseName_1355_; lean_object* v_dir_1356_; lean_object* v_config_1357_; lean_object* v_relManifestFile_1358_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v_fst_1363_; lean_object* v_snd_1364_; lean_object* v_packagesDir_x3f_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1426_; lean_object* v___y_1427_; uint8_t v___x_1430_; lean_object* v_rootName_1431_; lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_val_1485_; lean_object* v___x_1511_; 
v_packages_1300_ = lean_ctor_get(v_ws_1268_, 4);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1354_ = lean_array_fget_borrowed(v_packages_1300_, v___x_1301_);
v_baseName_1355_ = lean_ctor_get(v___x_1354_, 1);
v_dir_1356_ = lean_ctor_get(v___x_1354_, 4);
v_config_1357_ = lean_ctor_get(v___x_1354_, 6);
v_relManifestFile_1358_ = lean_ctor_get(v___x_1354_, 9);
v___x_1430_ = 0;
lean_inc(v_baseName_1355_);
v_rootName_1431_ = l_Lean_Name_toString(v_baseName_1355_, v___x_1430_);
lean_inc_ref(v_relManifestFile_1358_);
lean_inc_ref(v_dir_1356_);
v___x_1482_ = l_Lake_joinRelative(v_dir_1356_, v_relManifestFile_1358_);
v___x_1483_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1511_ = l_Lake_Manifest_load(v___x_1482_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_val_1485_ = v___x_1517_;
goto v___jp_1484_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1511_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1511_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set_tag(v___x_1522_, 0);
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
v_val_1485_ = v___x_1525_;
goto v___jp_1484_;
}
}
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v___y_1274_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
v___jp_1278_:
{
if (lean_obj_tag(v_fst_1280_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_snd_1281_);
v_a_1282_ = lean_ctor_get(v_fst_1280_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_fst_1280_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1284_ = v_fst_1280_;
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v_fst_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1296_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1286_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1287_ = lean_io_error_to_string(v_a_1282_);
v___x_1288_ = lean_string_append(v___x_1286_, v___x_1287_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = 3;
v___x_1290_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1, v___x_1289_);
lean_inc_ref(v___y_1279_);
v___x_1291_ = lean_apply_2(v___y_1279_, v___x_1290_, lean_box(0));
v___x_1292_ = lean_box(0);
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1292_);
v___x_1294_ = v___x_1284_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v_fst_1280_);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v_snd_1281_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
v___jp_1302_:
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_array_get_size(v___y_1304_);
v___x_1308_ = lean_nat_dec_lt(v___x_1301_, v___x_1307_);
if (v___x_1308_ == 0)
{
v___y_1279_ = v___y_1305_;
v_fst_1280_ = v_val_1306_;
v_snd_1281_ = v___y_1303_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_nat_dec_le(v___x_1307_, v___x_1307_);
if (v___x_1310_ == 0)
{
if (v___x_1308_ == 0)
{
v___y_1279_ = v___y_1305_;
v_fst_1280_ = v_val_1306_;
v_snd_1281_ = v___y_1303_;
goto v___jp_1278_;
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1307_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1304_, v___x_1311_, v___x_1312_, v___x_1309_, v___y_1305_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_dec_ref_known(v___x_1313_, 1);
v___y_1279_ = v___y_1305_;
v_fst_1280_ = v_val_1306_;
v_snd_1281_ = v___y_1303_;
goto v___jp_1278_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v_val_1306_);
lean_dec(v___y_1303_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1307_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1304_, v___x_1322_, v___x_1323_, v___x_1309_, v___y_1305_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_dec_ref_known(v___x_1324_, 1);
v___y_1279_ = v___y_1305_;
v_fst_1280_ = v_val_1306_;
v_snd_1281_ = v___y_1303_;
goto v___jp_1278_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_val_1306_);
lean_dec(v___y_1303_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
v___jp_1333_:
{
if (lean_obj_tag(v___y_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___y_1337_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___y_1337_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___y_1337_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___y_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set_tag(v___x_1340_, 1);
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
v___y_1303_ = v___y_1334_;
v___y_1304_ = v___y_1335_;
v___y_1305_ = v___y_1336_;
v_val_1306_ = v___x_1343_;
goto v___jp_1302_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___y_1337_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___y_1337_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___y_1337_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___y_1337_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 0);
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v___y_1303_ = v___y_1334_;
v___y_1304_ = v___y_1335_;
v___y_1305_ = v___y_1336_;
v_val_1306_ = v___x_1351_;
goto v___jp_1302_;
}
}
}
}
v___jp_1359_:
{
lean_object* v_toWorkspaceConfig_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_toWorkspaceConfig_1365_ = lean_ctor_get(v_config_1357_, 0);
v___x_1366_ = l_System_FilePath_normalize(v___y_1360_);
lean_inc_ref(v_toWorkspaceConfig_1365_);
v___x_1367_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1365_);
lean_inc_ref(v___x_1367_);
v___x_1368_ = l_System_FilePath_normalize(v___x_1367_);
v___x_1369_ = lean_string_dec_eq(v___x_1366_, v___x_1368_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___x_1366_);
if (v___x_1369_ == 0)
{
if (v_fst_1363_ == 0)
{
lean_dec_ref(v___x_1367_);
lean_dec_ref(v___y_1361_);
v___y_1274_ = v_snd_1364_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1370_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1371_ = lean_string_append(v___x_1370_, v___y_1361_);
v___x_1372_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1373_ = lean_string_append(v___x_1371_, v___x_1372_);
lean_inc_ref(v_dir_1356_);
v___x_1374_ = l_Lake_joinRelative(v_dir_1356_, v___x_1367_);
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
v___x_1378_ = 1;
v___x_1379_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set_uint8(v___x_1379_, sizeof(void*)*1, v___x_1378_);
lean_inc_ref(v___y_1362_);
v___x_1380_ = lean_apply_2(v___y_1362_, v___x_1379_, lean_box(0));
v___x_1381_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1374_);
v___x_1382_ = l_Lake_createParentDirs(v___x_1374_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; 
lean_dec_ref_known(v___x_1382_, 1);
v___x_1383_ = lean_io_rename(v___y_1361_, v___x_1374_);
lean_dec_ref(v___x_1374_);
lean_dec_ref(v___y_1361_);
v___y_1334_ = v_snd_1364_;
v___y_1335_ = v___x_1381_;
v___y_1336_ = v___y_1362_;
v___y_1337_ = v___x_1383_;
goto v___jp_1333_;
}
else
{
lean_dec_ref(v___x_1374_);
lean_dec_ref(v___y_1361_);
v___y_1334_ = v_snd_1364_;
v___y_1335_ = v___x_1381_;
v___y_1336_ = v___y_1362_;
v___y_1337_ = v___x_1382_;
goto v___jp_1333_;
}
}
}
else
{
lean_dec_ref(v___x_1367_);
lean_dec_ref(v___y_1361_);
v___y_1274_ = v_snd_1364_;
goto v___jp_1273_;
}
}
v___jp_1384_:
{
if (lean_obj_tag(v_packagesDir_x3f_1385_) == 1)
{
lean_object* v_val_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_val_1388_ = lean_ctor_get(v_packagesDir_x3f_1385_, 0);
lean_inc_n(v_val_1388_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1385_, 1);
lean_inc_ref(v_dir_1356_);
v___x_1389_ = l_Lake_joinRelative(v_dir_1356_, v_val_1388_);
v___x_1390_ = l_System_FilePath_pathExists(v___x_1389_);
v___x_1391_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1392_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1392_ == 0)
{
v___y_1360_ = v_val_1388_;
v___y_1361_ = v___x_1389_;
v___y_1362_ = v___y_1387_;
v_fst_1363_ = v___x_1390_;
v_snd_1364_ = v___y_1386_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1394_ == 0)
{
if (v___x_1392_ == 0)
{
v___y_1360_ = v_val_1388_;
v___y_1361_ = v___x_1389_;
v___y_1362_ = v___y_1387_;
v_fst_1363_ = v___x_1390_;
v_snd_1364_ = v___y_1386_;
goto v___jp_1359_;
}
else
{
size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1391_, v___x_1395_, v___x_1396_, v___x_1393_, v___y_1387_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_dec_ref_known(v___x_1397_, 1);
v___y_1360_ = v_val_1388_;
v___y_1361_ = v___x_1389_;
v___y_1362_ = v___y_1387_;
v_fst_1363_ = v___x_1390_;
v_snd_1364_ = v___y_1386_;
goto v___jp_1359_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v___x_1389_);
lean_dec(v_val_1388_);
lean_dec(v___y_1386_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
else
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1391_, v___x_1406_, v___x_1407_, v___x_1393_, v___y_1387_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_dec_ref_known(v___x_1408_, 1);
v___y_1360_ = v_val_1388_;
v___y_1361_ = v___x_1389_;
v___y_1362_ = v___y_1387_;
v_fst_1363_ = v___x_1390_;
v_snd_1364_ = v___y_1386_;
goto v___jp_1359_;
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v___x_1389_);
lean_dec(v_val_1388_);
lean_dec(v___y_1386_);
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec(v_packagesDir_x3f_1385_);
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v___y_1386_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
v___jp_1420_:
{
lean_object* v_packagesDir_x3f_1424_; 
v_packagesDir_x3f_1424_ = lean_ctor_get(v___y_1421_, 2);
lean_inc(v_packagesDir_x3f_1424_);
lean_dec_ref(v___y_1421_);
v_packagesDir_x3f_1385_ = v_packagesDir_x3f_1424_;
v___y_1386_ = v___y_1422_;
v___y_1387_ = v___y_1423_;
goto v___jp_1384_;
}
v___jp_1425_:
{
if (lean_obj_tag(v___y_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_snd_1429_; 
v_a_1428_ = lean_ctor_get(v___y_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___y_1427_, 1);
v_snd_1429_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_snd_1429_);
lean_dec(v_a_1428_);
v___y_1421_ = v___y_1426_;
v___y_1422_ = v_snd_1429_;
v___y_1423_ = v_a_1271_;
goto v___jp_1420_;
}
else
{
lean_dec_ref(v___y_1426_);
return v___y_1427_;
}
}
v___jp_1432_:
{
if (lean_obj_tag(v_fst_1433_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1467_; 
v_a_1435_ = lean_ctor_get(v_fst_1433_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_fst_1433_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1437_ = v_fst_1433_;
v_isShared_1438_ = v_isSharedCheck_1467_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v_fst_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1467_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
if (lean_obj_tag(v_a_1435_) == 11)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec_ref_known(v_a_1435_, 2);
v___x_1439_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1440_ = lean_string_append(v_rootName_1431_, v___x_1439_);
v___x_1441_ = 1;
v___x_1442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*1, v___x_1441_);
lean_inc_ref(v_a_1271_);
v___x_1443_ = lean_apply_2(v_a_1271_, v___x_1442_, lean_box(0));
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v_snd_1434_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1444_);
v___x_1446_ = v___x_1437_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1269_) == 0)
{
lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
lean_dec(v_snd_1434_);
lean_dec_ref(v_rootName_1431_);
v___x_1448_ = lean_io_error_to_string(v_a_1435_);
v___x_1449_ = 3;
v___x_1450_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set_uint8(v___x_1450_, sizeof(void*)*1, v___x_1449_);
lean_inc_ref(v_a_1271_);
v___x_1451_ = lean_apply_2(v_a_1271_, v___x_1450_, lean_box(0));
v___x_1452_ = lean_box(0);
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 1);
lean_ctor_set(v___x_1437_, 0, v___x_1452_);
v___x_1454_ = v___x_1437_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1456_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_1457_ = lean_string_append(v_rootName_1431_, v___x_1456_);
v___x_1458_ = lean_io_error_to_string(v_a_1435_);
v___x_1459_ = lean_string_append(v___x_1457_, v___x_1458_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = 2;
v___x_1461_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set_uint8(v___x_1461_, sizeof(void*)*1, v___x_1460_);
lean_inc_ref(v_a_1271_);
v___x_1462_ = lean_apply_2(v_a_1271_, v___x_1461_, lean_box(0));
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
lean_ctor_set(v___x_1463_, 1, v_snd_1434_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1463_);
v___x_1465_ = v___x_1437_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1431_);
if (lean_obj_tag(v_toUpdate_1269_) == 0)
{
lean_object* v_a_1468_; lean_object* v_packagesDir_x3f_1469_; lean_object* v_packages_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_a_1468_ = lean_ctor_get(v_fst_1433_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v_fst_1433_, 1);
v_packagesDir_x3f_1469_ = lean_ctor_get(v_a_1468_, 2);
v_packages_1470_ = lean_ctor_get(v_a_1468_, 3);
v___x_1471_ = lean_array_get_size(v_packages_1470_);
v___x_1472_ = lean_nat_dec_lt(v___x_1301_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_inc(v_packagesDir_x3f_1469_);
lean_dec(v_a_1468_);
v_packagesDir_x3f_1385_ = v_packagesDir_x3f_1469_;
v___y_1386_ = v_snd_1434_;
v___y_1387_ = v_a_1271_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_nat_dec_le(v___x_1471_, v___x_1471_);
if (v___x_1474_ == 0)
{
if (v___x_1472_ == 0)
{
lean_inc(v_packagesDir_x3f_1469_);
lean_dec(v_a_1468_);
v_packagesDir_x3f_1385_ = v_packagesDir_x3f_1469_;
v___y_1386_ = v_snd_1434_;
v___y_1387_ = v_a_1271_;
goto v___jp_1384_;
}
else
{
size_t v___x_1475_; size_t v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = ((size_t)0ULL);
v___x_1476_ = lean_usize_of_nat(v___x_1471_);
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1269_, v_packages_1470_, v___x_1475_, v___x_1476_, v___x_1473_, v_snd_1434_);
v___y_1426_ = v_a_1468_;
v___y_1427_ = v___x_1477_;
goto v___jp_1425_;
}
}
else
{
size_t v___x_1478_; size_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = ((size_t)0ULL);
v___x_1479_ = lean_usize_of_nat(v___x_1471_);
v___x_1480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1269_, v_packages_1470_, v___x_1478_, v___x_1479_, v___x_1473_, v_snd_1434_);
v___y_1426_ = v_a_1468_;
v___y_1427_ = v___x_1480_;
goto v___jp_1425_;
}
}
}
else
{
lean_object* v_a_1481_; 
v_a_1481_ = lean_ctor_get(v_fst_1433_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v_fst_1433_, 1);
v___y_1421_ = v_a_1481_;
v___y_1422_ = v_snd_1434_;
v___y_1423_ = v_a_1271_;
goto v___jp_1420_;
}
}
}
v___jp_1484_:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1486_ == 0)
{
v_fst_1433_ = v_val_1485_;
v_snd_1434_ = v_a_1270_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1488_ == 0)
{
if (v___x_1486_ == 0)
{
v_fst_1433_ = v_val_1485_;
v_snd_1434_ = v_a_1270_;
goto v___jp_1432_;
}
else
{
size_t v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = ((size_t)0ULL);
v___x_1490_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1483_, v___x_1489_, v___x_1490_, v___x_1487_, v_a_1271_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
v_fst_1433_ = v_val_1485_;
v_snd_1434_ = v_a_1270_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_val_1485_);
lean_dec_ref(v_rootName_1431_);
lean_dec(v_a_1270_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
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
return v___x_1497_;
}
}
}
}
}
else
{
size_t v___x_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = ((size_t)0ULL);
v___x_1501_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1483_, v___x_1500_, v___x_1501_, v___x_1487_, v_a_1271_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_dec_ref_known(v___x_1502_, 1);
v_fst_1433_ = v_val_1485_;
v_snd_1434_ = v_a_1270_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec_ref(v_val_1485_);
lean_dec_ref(v_rootName_1431_);
lean_dec(v_a_1270_);
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1528_, lean_object* v_toUpdate_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1528_, v_toUpdate_1529_, v_a_1530_, v_a_1531_);
lean_dec_ref(v_a_1531_);
lean_dec(v_toUpdate_1529_);
lean_dec_ref(v_ws_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_toUpdate_1534_, lean_object* v_as_1535_, size_t v_i_1536_, size_t v_stop_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1534_, v_as_1535_, v_i_1536_, v_stop_1537_, v_b_1538_, v___y_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_toUpdate_1543_, lean_object* v_as_1544_, lean_object* v_i_1545_, lean_object* v_stop_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
size_t v_i_boxed_1551_; size_t v_stop_boxed_1552_; lean_object* v_res_1553_; 
v_i_boxed_1551_ = lean_unbox_usize(v_i_1545_);
lean_dec(v_i_1545_);
v_stop_boxed_1552_ = lean_unbox_usize(v_stop_1546_);
lean_dec(v_stop_1546_);
v_res_1553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_toUpdate_1543_, v_as_1544_, v_i_boxed_1551_, v_stop_boxed_1552_, v_b_1547_, v___y_1548_, v___y_1549_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_as_1544_);
lean_dec(v_toUpdate_1543_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1554_, lean_object* v_as_1555_, size_t v_i_1556_, size_t v_stop_1557_, lean_object* v_b_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_fst_1562_; lean_object* v_snd_1563_; lean_object* v___y_1568_; lean_object* v_name_1569_; uint8_t v___x_1572_; 
v___x_1572_ = lean_usize_dec_eq(v_i_1556_, v_stop_1557_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v_name_1574_; lean_object* v_scope_1575_; lean_object* v_configFile_1576_; lean_object* v_manifestFile_x3f_1577_; lean_object* v_src_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1601_; 
v___x_1573_ = lean_array_uget(v_as_1555_, v_i_1556_);
v_name_1574_ = lean_ctor_get(v___x_1573_, 0);
v_scope_1575_ = lean_ctor_get(v___x_1573_, 1);
v_configFile_1576_ = lean_ctor_get(v___x_1573_, 2);
v_manifestFile_x3f_1577_ = lean_ctor_get(v___x_1573_, 3);
v_src_1578_ = lean_ctor_get(v___x_1573_, 4);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1580_ = v___x_1573_;
v_isShared_1581_ = v_isSharedCheck_1601_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_src_1578_);
lean_inc(v_manifestFile_x3f_1577_);
lean_inc(v_configFile_1576_);
lean_inc(v_scope_1575_);
lean_inc(v_name_1574_);
lean_dec(v___x_1573_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1601_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1574_, v___y_1559_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; 
v___x_1583_ = 1;
if (lean_obj_tag(v_src_1578_) == 0)
{
lean_object* v_dir_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1596_; 
v_dir_1584_ = lean_ctor_get(v_src_1578_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_src_1578_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1586_ = v_src_1578_;
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_dir_1584_);
lean_dec(v_src_1578_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_relPkgDir_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v_relPkgDir_1588_ = lean_ctor_get(v_dep_1554_, 1);
lean_inc_ref(v_relPkgDir_1588_);
v___x_1589_ = l_Lake_joinRelative(v_relPkgDir_1588_, v_dir_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; 
lean_inc(v_name_1574_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 4, v___x_1591_);
v___x_1593_ = v___x_1580_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_name_1574_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_scope_1575_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_configFile_1576_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_manifestFile_x3f_1577_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_ctor_set_uint8(v___x_1593_, sizeof(void*)*5, v___x_1583_);
v___y_1568_ = v___x_1593_;
v_name_1569_ = v_name_1574_;
goto v___jp_1567_;
}
}
}
}
else
{
lean_object* v___x_1598_; 
lean_inc(v_name_1574_);
if (v_isShared_1581_ == 0)
{
v___x_1598_ = v___x_1580_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_name_1574_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_scope_1575_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_configFile_1576_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_manifestFile_x3f_1577_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_src_1578_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*5, v___x_1583_);
v___y_1568_ = v___x_1598_;
v_name_1569_ = v_name_1574_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1600_; 
lean_del_object(v___x_1580_);
lean_dec_ref(v_src_1578_);
lean_dec(v_manifestFile_x3f_1577_);
lean_dec_ref(v_configFile_1576_);
lean_dec_ref(v_scope_1575_);
lean_dec(v_name_1574_);
v___x_1600_ = lean_box(0);
v_fst_1562_ = v___x_1600_;
v_snd_1563_ = v___y_1559_;
goto v___jp_1561_;
}
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v_dep_1554_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_b_1558_);
lean_ctor_set(v___x_1602_, 1, v___y_1559_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
v___jp_1561_:
{
size_t v___x_1564_; size_t v___x_1565_; 
v___x_1564_ = ((size_t)1ULL);
v___x_1565_ = lean_usize_add(v_i_1556_, v___x_1564_);
v_i_1556_ = v___x_1565_;
v_b_1558_ = v_fst_1562_;
v___y_1559_ = v_snd_1563_;
goto _start;
}
v___jp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = lean_box(0);
v___x_1571_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1569_, v___y_1568_, v___y_1559_);
v_fst_1562_ = v___x_1570_;
v_snd_1563_ = v___x_1571_;
goto v___jp_1561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1604_, lean_object* v_as_1605_, lean_object* v_i_1606_, lean_object* v_stop_1607_, lean_object* v_b_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_i_boxed_1611_; size_t v_stop_boxed_1612_; lean_object* v_res_1613_; 
v_i_boxed_1611_ = lean_unbox_usize(v_i_1606_);
lean_dec(v_i_1606_);
v_stop_boxed_1612_ = lean_unbox_usize(v_stop_1607_);
lean_dec(v_stop_1607_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1604_, v_as_1605_, v_i_boxed_1611_, v_stop_boxed_1612_, v_b_1608_, v___y_1609_);
lean_dec_ref(v_as_1605_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_manifestEntry_1620_; lean_object* v_pkgDir_1621_; lean_object* v_name_1622_; lean_object* v_manifestFile_x3f_1623_; lean_object* v___y_1625_; lean_object* v_fst_1626_; lean_object* v_snd_1627_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v_val_1687_; lean_object* v___y_1715_; 
v_manifestEntry_1620_ = lean_ctor_get(v_dep_1616_, 4);
v_pkgDir_1621_ = lean_ctor_get(v_dep_1616_, 0);
v_name_1622_ = lean_ctor_get(v_manifestEntry_1620_, 0);
v_manifestFile_x3f_1623_ = lean_ctor_get(v_manifestEntry_1620_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1623_) == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1621_);
v___x_1736_ = l_Lake_joinRelative(v_pkgDir_1621_, v___x_1735_);
v___y_1715_ = v___x_1736_;
goto v___jp_1714_;
}
else
{
lean_object* v_val_1737_; lean_object* v___x_1738_; 
v_val_1737_ = lean_ctor_get(v_manifestFile_x3f_1623_, 0);
lean_inc(v_val_1737_);
lean_inc_ref(v_pkgDir_1621_);
v___x_1738_ = l_Lake_joinRelative(v_pkgDir_1621_, v_val_1737_);
v___y_1715_ = v___x_1738_;
goto v___jp_1714_;
}
v___jp_1624_:
{
if (lean_obj_tag(v_fst_1626_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1657_; 
lean_inc(v_name_1622_);
lean_dec_ref(v_dep_1616_);
v_a_1628_ = lean_ctor_get(v_fst_1626_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_fst_1626_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1630_ = v_fst_1626_;
v_isShared_1631_ = v_isSharedCheck_1657_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v_fst_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1657_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
if (lean_obj_tag(v_a_1628_) == 11)
{
uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
lean_dec_ref_known(v_a_1628_, 2);
v___x_1632_ = 0;
v___x_1633_ = l_Lean_Name_toString(v_name_1622_, v___x_1632_);
v___x_1634_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1635_ = lean_string_append(v___x_1633_, v___x_1634_);
v___x_1636_ = lean_string_append(v___x_1635_, v___y_1625_);
lean_dec_ref(v___y_1625_);
v___x_1637_ = 2;
v___x_1638_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set_uint8(v___x_1638_, sizeof(void*)*1, v___x_1637_);
lean_inc_ref(v_a_1618_);
v___x_1639_ = lean_apply_2(v_a_1618_, v___x_1638_, lean_box(0));
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_snd_1627_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1640_);
v___x_1642_ = v___x_1630_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
else
{
uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_dec_ref(v___y_1625_);
v___x_1644_ = 0;
v___x_1645_ = l_Lean_Name_toString(v_name_1622_, v___x_1644_);
v___x_1646_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
v___x_1648_ = lean_io_error_to_string(v_a_1628_);
v___x_1649_ = lean_string_append(v___x_1647_, v___x_1648_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = 2;
v___x_1651_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*1, v___x_1650_);
lean_inc_ref(v_a_1618_);
v___x_1652_ = lean_apply_2(v_a_1618_, v___x_1651_, lean_box(0));
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v_snd_1627_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1653_);
v___x_1655_ = v___x_1630_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1682_; 
lean_dec_ref(v___y_1625_);
v_a_1658_ = lean_ctor_get(v_fst_1626_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_fst_1626_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1660_ = v_fst_1626_;
v_isShared_1661_ = v_isSharedCheck_1682_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v_fst_1626_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1682_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_packages_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_packages_1662_ = lean_ctor_get(v_a_1658_, 3);
lean_inc_ref(v_packages_1662_);
lean_dec(v_a_1658_);
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = lean_array_get_size(v_packages_1662_);
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_nat_dec_lt(v___x_1663_, v___x_1664_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec_ref(v_packages_1662_);
lean_dec_ref(v_dep_1616_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1665_);
lean_ctor_set(v___x_1667_, 1, v_snd_1627_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1667_);
v___x_1669_ = v___x_1660_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
else
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_nat_dec_le(v___x_1664_, v___x_1664_);
if (v___x_1671_ == 0)
{
if (v___x_1666_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_dec_ref(v_packages_1662_);
lean_dec_ref(v_dep_1616_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1665_);
lean_ctor_set(v___x_1672_, 1, v_snd_1627_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1672_);
v___x_1674_ = v___x_1660_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
else
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
lean_del_object(v___x_1660_);
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = lean_usize_of_nat(v___x_1664_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1616_, v_packages_1662_, v___x_1676_, v___x_1677_, v___x_1665_, v_snd_1627_);
lean_dec_ref(v_packages_1662_);
return v___x_1678_;
}
}
else
{
size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
lean_del_object(v___x_1660_);
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = lean_usize_of_nat(v___x_1664_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1616_, v_packages_1662_, v___x_1679_, v___x_1680_, v___x_1665_, v_snd_1627_);
lean_dec_ref(v_packages_1662_);
return v___x_1681_;
}
}
}
}
}
v___jp_1683_:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = lean_array_get_size(v___y_1684_);
v___x_1689_ = lean_nat_dec_lt(v___y_1685_, v___x_1688_);
if (v___x_1689_ == 0)
{
v___y_1625_ = v___y_1686_;
v_fst_1626_ = v_val_1687_;
v_snd_1627_ = v_a_1617_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_nat_dec_le(v___x_1688_, v___x_1688_);
if (v___x_1691_ == 0)
{
if (v___x_1689_ == 0)
{
v___y_1625_ = v___y_1686_;
v_fst_1626_ = v_val_1687_;
v_snd_1627_ = v_a_1617_;
goto v___jp_1624_;
}
else
{
size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = lean_usize_of_nat(v___x_1688_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1684_, v___x_1692_, v___x_1693_, v___x_1690_, v_a_1618_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_dec_ref_known(v___x_1694_, 1);
v___y_1625_ = v___y_1686_;
v_fst_1626_ = v_val_1687_;
v_snd_1627_ = v_a_1617_;
goto v___jp_1624_;
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v_val_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v_a_1617_);
lean_dec_ref(v_dep_1616_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
else
{
size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1688_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1684_, v___x_1703_, v___x_1704_, v___x_1690_, v_a_1618_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_dec_ref_known(v___x_1705_, 1);
v___y_1625_ = v___y_1686_;
v_fst_1626_ = v_val_1687_;
v_snd_1627_ = v_a_1617_;
goto v___jp_1624_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_val_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v_a_1617_);
lean_dec_ref(v_dep_1616_);
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
v___jp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1715_);
v___x_1718_ = l_Lake_Manifest_load(v___y_1715_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 1);
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
v___y_1684_ = v___x_1717_;
v___y_1685_ = v___x_1716_;
v___y_1686_ = v___y_1715_;
v_val_1687_ = v___x_1724_;
goto v___jp_1683_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_a_1727_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1718_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1718_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 0);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
v___y_1684_ = v___x_1717_;
v___y_1685_ = v___x_1716_;
v___y_1686_ = v___y_1715_;
v_val_1687_ = v___x_1732_;
goto v___jp_1683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1739_, v_a_1740_, v_a_1741_);
lean_dec_ref(v_a_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1744_, lean_object* v_as_1745_, size_t v_i_1746_, size_t v_stop_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1744_, v_as_1745_, v_i_1746_, v_stop_1747_, v_b_1748_, v___y_1749_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1753_, lean_object* v_as_1754_, lean_object* v_i_1755_, lean_object* v_stop_1756_, lean_object* v_b_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_i_boxed_1761_; size_t v_stop_boxed_1762_; lean_object* v_res_1763_; 
v_i_boxed_1761_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_stop_boxed_1762_ = lean_unbox_usize(v_stop_1756_);
lean_dec(v_stop_1756_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1753_, v_as_1754_, v_i_boxed_1761_, v_stop_boxed_1762_, v_b_1757_, v___y_1758_, v___y_1759_);
lean_dec_ref(v___y_1759_);
lean_dec_ref(v_as_1754_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1765_, lean_object* v_pkg_1766_, lean_object* v_dep_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v_name_1803_; lean_object* v___x_1804_; 
v_name_1803_ = lean_ctor_get(v_dep_1767_, 0);
v___x_1804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1768_, v_name_1803_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v_lakeEnv_1806_; lean_object* v_packages_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_config_1810_; lean_object* v_dir_1811_; lean_object* v_toWorkspaceConfig_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec_ref(v_dep_1767_);
lean_dec_ref(v_pkg_1766_);
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v_lakeEnv_1806_ = lean_ctor_get(v_ws_1765_, 0);
lean_inc_ref(v_lakeEnv_1806_);
v_packages_1807_ = lean_ctor_get(v_ws_1765_, 4);
lean_inc_ref(v_packages_1807_);
lean_dec_ref(v_ws_1765_);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_array_fget(v_packages_1807_, v___x_1808_);
lean_dec_ref(v_packages_1807_);
v_config_1810_ = lean_ctor_get(v___x_1809_, 6);
lean_inc_ref(v_config_1810_);
v_dir_1811_ = lean_ctor_get(v___x_1809_, 4);
lean_inc_ref(v_dir_1811_);
lean_dec(v___x_1809_);
v_toWorkspaceConfig_1812_ = lean_ctor_get(v_config_1810_, 0);
lean_inc_ref(v_toWorkspaceConfig_1812_);
lean_dec_ref(v_config_1810_);
v___x_1813_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1812_);
v___x_1814_ = l_Lake_PackageEntry_materialize(v_val_1805_, v_lakeEnv_1806_, v_dir_1811_, v___x_1813_, v_a_1769_);
lean_dec_ref(v_lakeEnv_1806_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1823_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1815_);
lean_ctor_set(v___x_1819_, 1, v_a_1768_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1768_);
v_a_1824_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1814_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1814_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_wsIdx_1832_; lean_object* v_relDir_1833_; uint8_t v___y_1835_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
lean_dec(v___x_1804_);
v_wsIdx_1832_ = lean_ctor_get(v_pkg_1766_, 0);
lean_inc(v_wsIdx_1832_);
v_relDir_1833_ = lean_ctor_get(v_pkg_1766_, 5);
lean_inc_ref(v_relDir_1833_);
lean_dec_ref(v_pkg_1766_);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_nat_dec_eq(v_wsIdx_1832_, v___x_1839_);
lean_dec(v_wsIdx_1832_);
if (v___x_1840_ == 0)
{
uint8_t v___x_1841_; 
v___x_1841_ = 1;
v___y_1835_ = v___x_1841_;
goto v___jp_1834_;
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = 0;
v___y_1835_ = v___x_1842_;
goto v___jp_1834_;
}
v___jp_1834_:
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1837_ = lean_string_dec_eq(v_relDir_1833_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lake_joinRelative(v_relDir_1833_, v___x_1836_);
v___y_1772_ = v___y_1835_;
v___y_1773_ = v___x_1838_;
goto v___jp_1771_;
}
else
{
v___y_1772_ = v___y_1835_;
v___y_1773_ = v_relDir_1833_;
goto v___jp_1771_;
}
}
}
v___jp_1771_:
{
lean_object* v_lakeEnv_1774_; lean_object* v_packages_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v_config_1778_; lean_object* v_dir_1779_; lean_object* v_toWorkspaceConfig_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_lakeEnv_1774_ = lean_ctor_get(v_ws_1765_, 0);
lean_inc_ref(v_lakeEnv_1774_);
v_packages_1775_ = lean_ctor_get(v_ws_1765_, 4);
lean_inc_ref(v_packages_1775_);
lean_dec_ref(v_ws_1765_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_array_fget(v_packages_1775_, v___x_1776_);
lean_dec_ref(v_packages_1775_);
v_config_1778_ = lean_ctor_get(v___x_1777_, 6);
lean_inc_ref(v_config_1778_);
v_dir_1779_ = lean_ctor_get(v___x_1777_, 4);
lean_inc_ref(v_dir_1779_);
lean_dec(v___x_1777_);
v_toWorkspaceConfig_1780_ = lean_ctor_get(v_config_1778_, 0);
lean_inc_ref(v_toWorkspaceConfig_1780_);
lean_dec_ref(v_config_1778_);
v___x_1781_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1780_);
v___x_1782_ = l_Lake_Dependency_materialize(v_dep_1767_, v___y_1772_, v_lakeEnv_1774_, v_dir_1779_, v___x_1781_, v___y_1773_, v_a_1769_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1794_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1794_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_manifestEntry_1787_; lean_object* v_name_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v_manifestEntry_1787_ = lean_ctor_get(v_a_1783_, 4);
v_name_1788_ = lean_ctor_get(v_manifestEntry_1787_, 0);
lean_inc_ref(v_manifestEntry_1787_);
lean_inc(v_name_1788_);
v___x_1789_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1788_, v_manifestEntry_1787_, v_a_1768_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1783_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1790_);
v___x_1792_ = v___x_1785_;
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
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_a_1768_);
v_a_1795_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1782_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1782_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1843_, lean_object* v_pkg_1844_, lean_object* v_dep_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1843_, v_pkg_1844_, v_dep_1845_, v_a_1846_, v_a_1847_);
lean_dec_ref(v_a_1847_);
return v_res_1849_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1850_; 
v___x_1850_ = 4;
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1851_, lean_object* v_tc_x3f_1852_, uint8_t v_fixed_1853_, lean_object* v_self_1854_){
_start:
{
lean_object* v_clashes_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_clashes_1855_ = lean_ctor_get(v_self_1854_, 2);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_self_1854_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; lean_object* v_unused_1864_; 
v_unused_1863_ = lean_ctor_get(v_self_1854_, 1);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_self_1854_, 0);
lean_dec(v_unused_1864_);
v___x_1857_ = v_self_1854_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_clashes_1855_);
lean_dec(v_self_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v_tc_x3f_1852_);
lean_ctor_set(v___x_1857_, 0, v_src_1851_);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_src_1851_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_tc_x3f_1852_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_clashes_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*3, v_fixed_1853_);
return v___x_1860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1865_, lean_object* v_tc_x3f_1866_, lean_object* v_fixed_1867_, lean_object* v_self_1868_){
_start:
{
uint8_t v_fixed_boxed_1869_; lean_object* v_res_1870_; 
v_fixed_boxed_1869_ = lean_unbox(v_fixed_1867_);
v_res_1870_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1865_, v_tc_x3f_1866_, v_fixed_boxed_1869_, v_self_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1871_, lean_object* v_ver_1872_, uint8_t v_fixed_1873_, lean_object* v_self_1874_){
_start:
{
lean_object* v_src_1875_; lean_object* v_tc_x3f_1876_; lean_object* v_clashes_1877_; uint8_t v_fixed_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1887_; 
v_src_1875_ = lean_ctor_get(v_self_1874_, 0);
v_tc_x3f_1876_ = lean_ctor_get(v_self_1874_, 1);
v_clashes_1877_ = lean_ctor_get(v_self_1874_, 2);
v_fixed_1878_ = lean_ctor_get_uint8(v_self_1874_, sizeof(void*)*3);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_self_1874_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1880_ = v_self_1874_;
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_clashes_1877_);
lean_inc(v_tc_x3f_1876_);
lean_inc(v_src_1875_);
lean_dec(v_self_1874_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1882_, 0, v_src_1871_);
lean_ctor_set(v___x_1882_, 1, v_ver_1872_);
lean_ctor_set_uint8(v___x_1882_, sizeof(void*)*2, v_fixed_1873_);
v___x_1883_ = lean_array_push(v_clashes_1877_, v___x_1882_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 2, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_src_1875_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_tc_x3f_1876_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v___x_1883_);
lean_ctor_set_uint8(v_reuseFailAlloc_1886_, sizeof(void*)*3, v_fixed_1878_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1888_, lean_object* v_ver_1889_, lean_object* v_fixed_1890_, lean_object* v_self_1891_){
_start:
{
uint8_t v_fixed_boxed_1892_; lean_object* v_res_1893_; 
v_fixed_boxed_1892_ = lean_unbox(v_fixed_1890_);
v_res_1893_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1888_, v_ver_1889_, v_fixed_boxed_1892_, v_self_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v_as_1898_, size_t v_i_1899_, size_t v_stop_1900_, lean_object* v_b_1901_){
_start:
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_usize_dec_eq(v_i_1899_, v_stop_1900_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v_src_1904_; lean_object* v_ver_1905_; uint8_t v_fixed_1906_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1922_; 
v___x_1903_ = lean_array_uget_borrowed(v_as_1898_, v_i_1899_);
v_src_1904_ = lean_ctor_get(v___x_1903_, 0);
v_ver_1905_ = lean_ctor_get(v___x_1903_, 1);
v_fixed_1906_ = lean_ctor_get_uint8(v___x_1903_, sizeof(void*)*2);
if (v_fixed_1906_ == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1922_ = v___x_1926_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1927_; 
v___x_1927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1922_ = v___x_1927_;
goto v___jp_1921_;
}
v___jp_1907_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; size_t v___x_1918_; size_t v___x_1919_; 
v___x_1911_ = lean_string_append(v___y_1908_, v___y_1910_);
lean_dec_ref(v___y_1910_);
v___x_1912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1913_ = lean_string_append(v___x_1911_, v___x_1912_);
v___x_1914_ = 1;
lean_inc(v_src_1904_);
v___x_1915_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1904_, v___x_1914_);
v___x_1916_ = lean_string_append(v___x_1913_, v___x_1915_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = lean_string_append(v___x_1916_, v___y_1909_);
v___x_1918_ = ((size_t)1ULL);
v___x_1919_ = lean_usize_add(v_i_1899_, v___x_1918_);
v_i_1899_ = v___x_1919_;
v_b_1901_ = v___x_1917_;
goto _start;
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_toString_1925_; 
v___x_1923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1924_ = lean_string_append(v_b_1901_, v___x_1923_);
v_toString_1925_ = lean_ctor_get(v_ver_1905_, 0);
lean_inc_ref(v_toString_1925_);
v___y_1908_ = v___x_1924_;
v___y_1909_ = v___y_1922_;
v___y_1910_ = v_toString_1925_;
goto v___jp_1907_;
}
}
else
{
return v_b_1901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v_as_1928_, lean_object* v_i_1929_, lean_object* v_stop_1930_, lean_object* v_b_1931_){
_start:
{
size_t v_i_boxed_1932_; size_t v_stop_boxed_1933_; lean_object* v_res_1934_; 
v_i_boxed_1932_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_stop_boxed_1933_ = lean_unbox_usize(v_stop_1930_);
lean_dec(v_stop_1930_);
v_res_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1928_, v_i_boxed_1932_, v_stop_boxed_1933_, v_b_1931_);
lean_dec_ref(v_as_1928_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v_as_1935_, size_t v_i_1936_, size_t v_stop_1937_, lean_object* v_b_1938_){
_start:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_usize_dec_eq(v_i_1936_, v_stop_1937_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v_src_1941_; lean_object* v_ver_1942_; uint8_t v_fixed_1943_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1959_; 
v___x_1940_ = lean_array_uget_borrowed(v_as_1935_, v_i_1936_);
v_src_1941_ = lean_ctor_get(v___x_1940_, 0);
v_ver_1942_ = lean_ctor_get(v___x_1940_, 1);
v_fixed_1943_ = lean_ctor_get_uint8(v___x_1940_, sizeof(void*)*2);
if (v_fixed_1943_ == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1959_ = v___x_1963_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1964_; 
v___x_1964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1959_ = v___x_1964_;
goto v___jp_1958_;
}
v___jp_1944_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1948_ = lean_string_append(v___y_1946_, v___y_1947_);
lean_dec_ref(v___y_1947_);
v___x_1949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1950_ = lean_string_append(v___x_1948_, v___x_1949_);
v___x_1951_ = 1;
lean_inc(v_src_1941_);
v___x_1952_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1941_, v___x_1951_);
v___x_1953_ = lean_string_append(v___x_1950_, v___x_1952_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = lean_string_append(v___x_1953_, v___y_1945_);
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1936_, v___x_1955_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1935_, v___x_1956_, v_stop_1937_, v___x_1954_);
return v___x_1957_;
}
v___jp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v_toString_1962_; 
v___x_1960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1961_ = lean_string_append(v_b_1938_, v___x_1960_);
v_toString_1962_ = lean_ctor_get(v_ver_1942_, 0);
lean_inc_ref(v_toString_1962_);
v___y_1945_ = v___y_1959_;
v___y_1946_ = v___x_1961_;
v___y_1947_ = v_toString_1962_;
goto v___jp_1944_;
}
}
else
{
return v_b_1938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v_as_1965_, lean_object* v_i_1966_, lean_object* v_stop_1967_, lean_object* v_b_1968_){
_start:
{
size_t v_i_boxed_1969_; size_t v_stop_boxed_1970_; lean_object* v_res_1971_; 
v_i_boxed_1969_ = lean_unbox_usize(v_i_1966_);
lean_dec(v_i_1966_);
v_stop_boxed_1970_ = lean_unbox_usize(v_stop_1967_);
lean_dec(v_stop_1967_);
v_res_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v_as_1965_, v_i_boxed_1969_, v_stop_boxed_1970_, v_b_1968_);
lean_dec_ref(v_as_1965_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_1972_, lean_object* v_as_1973_, size_t v_i_1974_, size_t v_stop_1975_, lean_object* v_b_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_usize_dec_eq(v_i_1974_, v_stop_1975_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v_relPkgDir_1981_; lean_object* v_manifestEntry_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1980_ = lean_array_uget_borrowed(v_as_1973_, v_i_1974_);
v_relPkgDir_1981_ = lean_ctor_get(v___x_1980_, 1);
v_manifestEntry_1982_ = lean_ctor_get(v___x_1980_, 4);
lean_inc_ref(v_relPkgDir_1981_);
lean_inc_ref(v___x_1972_);
v___x_1983_ = l_Lake_joinRelative(v___x_1972_, v_relPkgDir_1981_);
v___x_1984_ = l_Lake_toolchainFileName;
v___x_1985_ = l_System_FilePath_join(v___x_1983_, v___x_1984_);
v___x_1986_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1985_);
lean_dec_ref(v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v_a_1989_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
if (lean_obj_tag(v_a_1987_) == 1)
{
lean_object* v_tc_x3f_1993_; 
v_tc_x3f_1993_ = lean_ctor_get(v_b_1976_, 1);
if (lean_obj_tag(v_tc_x3f_1993_) == 1)
{
lean_object* v_val_1994_; lean_object* v_src_1995_; lean_object* v_clashes_1996_; uint8_t v_fixed_1997_; lean_object* v_val_1998_; uint8_t v___x_1999_; 
v_val_1994_ = lean_ctor_get(v_a_1987_, 0);
v_src_1995_ = lean_ctor_get(v_b_1976_, 0);
v_clashes_1996_ = lean_ctor_get(v_b_1976_, 2);
v_fixed_1997_ = lean_ctor_get_uint8(v_b_1976_, sizeof(void*)*3);
v_val_1998_ = lean_ctor_get(v_tc_x3f_1993_, 0);
v___x_1999_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1980_);
if (v___x_1999_ == 0)
{
uint8_t v___x_2009_; 
v___x_2009_ = l_Lake_ToolchainVer_ble(v_val_1994_, v_val_1998_);
if (v___x_2009_ == 0)
{
lean_inc_ref(v_clashes_1996_);
lean_inc(v_src_1995_);
lean_inc_ref(v_tc_x3f_1993_);
lean_dec_ref(v_b_1976_);
if (v_fixed_1997_ == 0)
{
goto v___jp_2005_;
}
else
{
if (v___x_1999_ == 0)
{
lean_inc(v_val_1994_);
lean_dec_ref_known(v_a_1987_, 1);
goto v___jp_2000_;
}
else
{
goto v___jp_2005_;
}
}
}
else
{
lean_dec_ref_known(v_a_1987_, 1);
v_a_1989_ = v_b_1976_;
goto v___jp_1988_;
}
}
else
{
if (v_fixed_1997_ == 0)
{
lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2024_; 
lean_inc_ref(v_clashes_1996_);
lean_inc(v_src_1995_);
lean_inc_ref(v_tc_x3f_1993_);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_b_1976_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; lean_object* v_unused_2026_; lean_object* v_unused_2027_; 
v_unused_2025_ = lean_ctor_get(v_b_1976_, 2);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_b_1976_, 1);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_b_1976_, 0);
lean_dec(v_unused_2027_);
v___x_2011_ = v_b_1976_;
v_isShared_2012_ = v_isSharedCheck_2024_;
goto v_resetjp_2010_;
}
else
{
lean_dec(v_b_1976_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2024_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lake_ToolchainVer_ble(v_val_1998_, v_val_1994_);
if (v___x_2013_ == 0)
{
lean_object* v_name_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_inc(v_val_1994_);
lean_dec_ref_known(v_a_1987_, 1);
v_name_2014_ = lean_ctor_get(v_manifestEntry_1982_, 0);
lean_inc(v_name_2014_);
v___x_2015_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2015_, 0, v_name_2014_);
lean_ctor_set(v___x_2015_, 1, v_val_1994_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2, v___x_1999_);
v___x_2016_ = lean_array_push(v_clashes_1996_, v___x_2015_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 2, v___x_2016_);
v___x_2018_ = v___x_2011_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_src_1995_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_tc_x3f_1993_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v___x_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*3, v_fixed_1997_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
v_a_1989_ = v___x_2018_;
goto v___jp_1988_;
}
}
else
{
lean_object* v_name_2020_; lean_object* v___x_2022_; 
lean_dec(v_src_1995_);
lean_dec_ref_known(v_tc_x3f_1993_, 1);
v_name_2020_ = lean_ctor_get(v_manifestEntry_1982_, 0);
lean_inc(v_name_2020_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 1, v_a_1987_);
lean_ctor_set(v___x_2011_, 0, v_name_2020_);
v___x_2022_ = v___x_2011_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_name_2020_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_a_1987_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_clashes_1996_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*3, v___x_1999_);
v_a_1989_ = v___x_2022_;
goto v___jp_1988_;
}
}
}
}
else
{
uint8_t v___x_2028_; 
lean_inc_n(v_val_1994_, 2);
lean_dec_ref_known(v_a_1987_, 1);
lean_inc(v_val_1998_);
v___x_2028_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_1998_, v_val_1994_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2038_; 
lean_inc_ref(v_clashes_1996_);
lean_inc(v_src_1995_);
lean_inc_ref(v_tc_x3f_1993_);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_b_1976_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; lean_object* v_unused_2040_; lean_object* v_unused_2041_; 
v_unused_2039_ = lean_ctor_get(v_b_1976_, 2);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_b_1976_, 1);
lean_dec(v_unused_2040_);
v_unused_2041_ = lean_ctor_get(v_b_1976_, 0);
lean_dec(v_unused_2041_);
v___x_2030_ = v_b_1976_;
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v_b_1976_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_name_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v_name_2032_ = lean_ctor_get(v_manifestEntry_1982_, 0);
lean_inc(v_name_2032_);
v___x_2033_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2033_, 0, v_name_2032_);
lean_ctor_set(v___x_2033_, 1, v_val_1994_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2, v___x_1999_);
v___x_2034_ = lean_array_push(v_clashes_1996_, v___x_2033_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 2, v___x_2034_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_src_1995_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_tc_x3f_1993_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v___x_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2037_, sizeof(void*)*3, v_fixed_1997_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v_a_1989_ = v___x_2036_;
goto v___jp_1988_;
}
}
}
else
{
lean_dec(v_val_1994_);
v_a_1989_ = v_b_1976_;
goto v___jp_1988_;
}
}
}
v___jp_2000_:
{
lean_object* v_name_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_name_2001_ = lean_ctor_get(v_manifestEntry_1982_, 0);
lean_inc(v_name_2001_);
v___x_2002_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2002_, 0, v_name_2001_);
lean_ctor_set(v___x_2002_, 1, v_val_1994_);
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*2, v___x_1999_);
v___x_2003_ = lean_array_push(v_clashes_1996_, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2004_, 0, v_src_1995_);
lean_ctor_set(v___x_2004_, 1, v_tc_x3f_1993_);
lean_ctor_set(v___x_2004_, 2, v___x_2003_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*3, v_fixed_1997_);
v_a_1989_ = v___x_2004_;
goto v___jp_1988_;
}
v___jp_2005_:
{
uint8_t v___x_2006_; 
v___x_2006_ = l_Lake_ToolchainVer_blt(v_val_1998_, v_val_1994_);
if (v___x_2006_ == 0)
{
lean_inc(v_val_1994_);
lean_dec_ref_known(v_a_1987_, 1);
goto v___jp_2000_;
}
else
{
lean_object* v_name_2007_; lean_object* v___x_2008_; 
lean_dec(v_src_1995_);
lean_dec_ref_known(v_tc_x3f_1993_, 1);
v_name_2007_ = lean_ctor_get(v_manifestEntry_1982_, 0);
lean_inc(v_name_2007_);
v___x_2008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2008_, 0, v_name_2007_);
lean_ctor_set(v___x_2008_, 1, v_a_1987_);
lean_ctor_set(v___x_2008_, 2, v_clashes_1996_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*3, v___x_1999_);
v_a_1989_ = v___x_2008_;
goto v___jp_1988_;
}
}
}
else
{
lean_object* v_clashes_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2051_; 
v_clashes_2042_ = lean_ctor_get(v_b_1976_, 2);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_b_1976_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; 
v_unused_2052_ = lean_ctor_get(v_b_1976_, 1);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_b_1976_, 0);
lean_dec(v_unused_2053_);
v___x_2044_ = v_b_1976_;
v_isShared_2045_ = v_isSharedCheck_2051_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_clashes_2042_);
lean_dec(v_b_1976_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2051_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_name_2046_; uint8_t v___x_2047_; lean_object* v___x_2049_; 
v_name_2046_ = lean_ctor_get(v_manifestEntry_1982_, 0);
v___x_2047_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1980_);
lean_inc(v_name_2046_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v_a_1987_);
lean_ctor_set(v___x_2044_, 0, v_name_2046_);
v___x_2049_ = v___x_2044_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_name_2046_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_a_1987_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_clashes_2042_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_ctor_set_uint8(v___x_2049_, sizeof(void*)*3, v___x_2047_);
v_a_1989_ = v___x_2049_;
goto v___jp_1988_;
}
}
}
}
else
{
lean_dec(v_a_1987_);
v_a_1989_ = v_b_1976_;
goto v___jp_1988_;
}
v___jp_1988_:
{
size_t v___x_1990_; size_t v___x_1991_; 
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_add(v_i_1974_, v___x_1990_);
v_i_1974_ = v___x_1991_;
v_b_1976_ = v_a_1989_;
goto _start;
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_b_1976_);
lean_dec_ref(v___x_1972_);
v_a_2054_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2056_ = v___x_1986_;
v_isShared_2057_ = v_isSharedCheck_2066_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_1986_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2066_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2058_ = lean_io_error_to_string(v_a_2054_);
v___x_2059_ = 3;
v___x_2060_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*1, v___x_2059_);
lean_inc_ref(v___y_1977_);
v___x_2061_ = lean_apply_2(v___y_1977_, v___x_2060_, lean_box(0));
v___x_2062_ = lean_box(0);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2062_);
v___x_2064_ = v___x_2056_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v___x_2067_; 
lean_dec_ref(v___x_1972_);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_b_1976_);
return v___x_2067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2068_, lean_object* v_as_2069_, lean_object* v_i_2070_, lean_object* v_stop_2071_, lean_object* v_b_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
size_t v_i_boxed_2075_; size_t v_stop_boxed_2076_; lean_object* v_res_2077_; 
v_i_boxed_2075_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_stop_boxed_2076_ = lean_unbox_usize(v_stop_2071_);
lean_dec(v_stop_2071_);
v_res_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2068_, v_as_2069_, v_i_boxed_2075_, v_stop_boxed_2076_, v_b_2072_, v___y_2073_);
lean_dec_ref(v___y_2073_);
lean_dec_ref(v_as_2069_);
return v_res_2077_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v___x_2088_ = lean_unsigned_to_nat(4u);
v___x_2089_ = lean_mk_empty_array_with_capacity(v___x_2088_);
v___x_2090_ = lean_array_push(v___x_2089_, v___x_2087_);
return v___x_2090_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2092_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6);
v___x_2093_ = lean_array_push(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10(void){
_start:
{
uint32_t v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = 4;
v___x_2099_ = lean_uint32_to_uint8(v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2117_, lean_object* v_rootDeps_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___y_2122_; lean_object* v_lakeEnv_2127_; lean_object* v_lakeArgs_x3f_2128_; lean_object* v_packages_2129_; lean_object* v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2276_; lean_object* v___y_2277_; uint8_t v___y_2278_; lean_object* v___x_2281_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2295_; uint8_t v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2309_; uint8_t v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___x_2317_; lean_object* v_baseName_2318_; lean_object* v_dir_2319_; lean_object* v_config_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_lakeEnv_2127_ = lean_ctor_get(v_ws_2117_, 0);
lean_inc_ref(v_lakeEnv_2127_);
v_lakeArgs_x3f_2128_ = lean_ctor_get(v_ws_2117_, 3);
lean_inc(v_lakeArgs_x3f_2128_);
v_packages_2129_ = lean_ctor_get(v_ws_2117_, 4);
lean_inc_ref(v_packages_2129_);
lean_dec_ref(v_ws_2117_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2317_ = lean_array_fget(v_packages_2129_, v___x_2281_);
lean_dec_ref(v_packages_2129_);
v_baseName_2318_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_baseName_2318_);
v_dir_2319_ = lean_ctor_get(v___x_2317_, 4);
lean_inc_ref_n(v_dir_2319_, 2);
v_config_2320_ = lean_ctor_get(v___x_2317_, 6);
lean_inc_ref(v_config_2320_);
lean_dec(v___x_2317_);
v___x_2321_ = l_Lake_toolchainFileName;
v___x_2322_ = l_System_FilePath_join(v_dir_2319_, v___x_2321_);
v___x_2323_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2322_);
lean_dec_ref(v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2382_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2382_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2382_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_src_2329_; lean_object* v_tc_x3f_2330_; lean_object* v_clashes_2331_; uint8_t v_fixed_2332_; lean_object* v___y_2356_; uint8_t v_fixedToolchain_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v_fixedToolchain_2370_ = lean_ctor_get_uint8(v_config_2320_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_2320_);
v___x_2371_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2372_ = lean_array_get_size(v_rootDeps_2118_);
v___x_2373_ = lean_nat_dec_lt(v___x_2281_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_inc(v_a_2324_);
v_src_2329_ = v_baseName_2318_;
v_tc_x3f_2330_ = v_a_2324_;
v_clashes_2331_ = v___x_2371_;
v_fixed_2332_ = v_fixedToolchain_2370_;
goto v___jp_2328_;
}
else
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
lean_inc(v_a_2324_);
lean_inc(v_baseName_2318_);
v___x_2374_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2374_, 0, v_baseName_2318_);
lean_ctor_set(v___x_2374_, 1, v_a_2324_);
lean_ctor_set(v___x_2374_, 2, v___x_2371_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*3, v_fixedToolchain_2370_);
v___x_2375_ = lean_nat_dec_le(v___x_2372_, v___x_2372_);
if (v___x_2375_ == 0)
{
if (v___x_2373_ == 0)
{
lean_dec_ref_known(v___x_2374_, 3);
lean_inc(v_a_2324_);
v_src_2329_ = v_baseName_2318_;
v_tc_x3f_2330_ = v_a_2324_;
v_clashes_2331_ = v___x_2371_;
v_fixed_2332_ = v_fixedToolchain_2370_;
goto v___jp_2328_;
}
else
{
size_t v___x_2376_; size_t v___x_2377_; lean_object* v___x_2378_; 
lean_dec(v_baseName_2318_);
v___x_2376_ = ((size_t)0ULL);
v___x_2377_ = lean_usize_of_nat(v___x_2372_);
lean_inc_ref(v_dir_2319_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2319_, v_rootDeps_2118_, v___x_2376_, v___x_2377_, v___x_2374_, v_a_2119_);
v___y_2356_ = v___x_2378_;
goto v___jp_2355_;
}
}
else
{
size_t v___x_2379_; size_t v___x_2380_; lean_object* v___x_2381_; 
lean_dec(v_baseName_2318_);
v___x_2379_ = ((size_t)0ULL);
v___x_2380_ = lean_usize_of_nat(v___x_2372_);
lean_inc_ref(v_dir_2319_);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2319_, v_rootDeps_2118_, v___x_2379_, v___x_2380_, v___x_2374_, v_a_2119_);
v___y_2356_ = v___x_2381_;
goto v___jp_2355_;
}
}
v___jp_2328_:
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = lean_array_get_size(v_clashes_2331_);
v___x_2334_ = lean_nat_dec_lt(v___x_2281_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v_clashes_2331_);
lean_dec(v_src_2329_);
if (lean_obj_tag(v_tc_x3f_2330_) == 1)
{
lean_object* v_val_2335_; lean_object* v_rootToolchainFile_2336_; 
v_val_2335_ = lean_ctor_get(v_tc_x3f_2330_, 0);
lean_inc(v_val_2335_);
lean_dec_ref_known(v_tc_x3f_2330_, 1);
v_rootToolchainFile_2336_ = l_Lake_joinRelative(v_dir_2319_, v___x_2321_);
if (lean_obj_tag(v_a_2324_) == 0)
{
lean_del_object(v___x_2326_);
v___y_2276_ = v_rootToolchainFile_2336_;
v___y_2277_ = v_val_2335_;
v___y_2278_ = v___x_2334_;
goto v___jp_2275_;
}
else
{
lean_object* v_val_2337_; uint8_t v___x_2338_; 
v_val_2337_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v_a_2324_, 1);
lean_inc(v_val_2335_);
v___x_2338_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2337_, v_val_2335_);
if (v___x_2338_ == 0)
{
lean_del_object(v___x_2326_);
v___y_2276_ = v_rootToolchainFile_2336_;
v___y_2277_ = v_val_2335_;
v___y_2278_ = v___x_2338_;
goto v___jp_2275_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
lean_dec_ref(v_rootToolchainFile_2336_);
lean_dec(v_val_2335_);
lean_dec(v_lakeArgs_x3f_2128_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2339_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2119_);
v___x_2340_ = lean_apply_2(v_a_2119_, v___x_2339_, lean_box(0));
v___x_2341_ = lean_box(0);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2341_);
v___x_2343_ = v___x_2326_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
lean_dec(v_tc_x3f_2330_);
lean_dec(v_a_2324_);
lean_dec_ref(v_dir_2319_);
lean_dec(v_lakeArgs_x3f_2128_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2345_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2119_);
v___x_2346_ = lean_apply_2(v_a_2119_, v___x_2345_, lean_box(0));
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2346_);
v___x_2348_ = v___x_2326_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
else
{
lean_del_object(v___x_2326_);
lean_dec(v_a_2324_);
lean_dec_ref(v_dir_2319_);
lean_dec(v_lakeArgs_x3f_2128_);
lean_dec_ref(v_lakeEnv_2127_);
if (lean_obj_tag(v_tc_x3f_2330_) == 1)
{
if (v_fixed_2332_ == 0)
{
lean_object* v_val_2350_; lean_object* v___x_2351_; 
v_val_2350_ = lean_ctor_get(v_tc_x3f_2330_, 0);
lean_inc(v_val_2350_);
lean_dec_ref_known(v_tc_x3f_2330_, 1);
v___x_2351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2309_ = v_val_2350_;
v___y_2310_ = v___x_2334_;
v___y_2311_ = v_src_2329_;
v___y_2312_ = v___x_2333_;
v___y_2313_ = v_clashes_2331_;
v___y_2314_ = v___x_2351_;
goto v___jp_2308_;
}
else
{
lean_object* v_val_2352_; lean_object* v___x_2353_; 
v_val_2352_ = lean_ctor_get(v_tc_x3f_2330_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v_tc_x3f_2330_, 1);
v___x_2353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2309_ = v_val_2352_;
v___y_2310_ = v___x_2334_;
v___y_2311_ = v_src_2329_;
v___y_2312_ = v___x_2333_;
v___y_2313_ = v_clashes_2331_;
v___y_2314_ = v___x_2353_;
goto v___jp_2308_;
}
}
else
{
lean_object* v___x_2354_; 
lean_dec(v_tc_x3f_2330_);
lean_dec(v_src_2329_);
v___x_2354_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2283_ = v___x_2333_;
v___y_2284_ = v_clashes_2331_;
v___y_2285_ = v___x_2354_;
goto v___jp_2282_;
}
}
}
v___jp_2355_:
{
if (lean_obj_tag(v___y_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v_src_2358_; lean_object* v_tc_x3f_2359_; lean_object* v_clashes_2360_; uint8_t v_fixed_2361_; 
v_a_2357_ = lean_ctor_get(v___y_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___y_2356_, 1);
v_src_2358_ = lean_ctor_get(v_a_2357_, 0);
lean_inc(v_src_2358_);
v_tc_x3f_2359_ = lean_ctor_get(v_a_2357_, 1);
lean_inc(v_tc_x3f_2359_);
v_clashes_2360_ = lean_ctor_get(v_a_2357_, 2);
lean_inc_ref(v_clashes_2360_);
v_fixed_2361_ = lean_ctor_get_uint8(v_a_2357_, sizeof(void*)*3);
lean_dec(v_a_2357_);
v_src_2329_ = v_src_2358_;
v_tc_x3f_2330_ = v_tc_x3f_2359_;
v_clashes_2331_ = v_clashes_2360_;
v_fixed_2332_ = v_fixed_2361_;
goto v___jp_2328_;
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_del_object(v___x_2326_);
lean_dec(v_a_2324_);
lean_dec_ref(v_dir_2319_);
lean_dec(v_lakeArgs_x3f_2128_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2362_ = lean_ctor_get(v___y_2356_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___y_2356_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___y_2356_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___y_2356_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref(v_config_2320_);
lean_dec_ref(v_dir_2319_);
lean_dec(v_baseName_2318_);
lean_dec(v_lakeArgs_x3f_2128_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2383_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2385_ = v___x_2323_;
v_isShared_2386_ = v_isSharedCheck_2395_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2323_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2395_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2387_ = lean_io_error_to_string(v_a_2383_);
v___x_2388_ = 3;
v___x_2389_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set_uint8(v___x_2389_, sizeof(void*)*1, v___x_2388_);
lean_inc_ref(v_a_2119_);
v___x_2390_ = lean_apply_2(v_a_2119_, v___x_2389_, lean_box(0));
v___x_2391_ = lean_box(0);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2391_);
v___x_2393_ = v___x_2385_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
v___jp_2121_:
{
uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = 2;
v___x_2124_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2124_, 0, v___y_2122_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1, v___x_2123_);
lean_inc_ref(v_a_2119_);
v___x_2125_ = lean_apply_2(v_a_2119_, v___x_2124_, lean_box(0));
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
}
v___jp_2130_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_inc_ref(v___y_2132_);
v___x_2135_ = lean_string_append(v___y_2132_, v___y_2134_);
v___x_2136_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2137_ = lean_string_append(v___x_2135_, v___x_2136_);
v___x_2138_ = 1;
v___x_2139_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2139_, 0, v___x_2137_);
lean_ctor_set_uint8(v___x_2139_, sizeof(void*)*1, v___x_2138_);
lean_inc_ref(v_a_2119_);
v___x_2140_ = lean_apply_2(v_a_2119_, v___x_2139_, lean_box(0));
v___x_2141_ = l_IO_FS_writeFile(v___y_2131_, v___y_2134_);
lean_dec_ref(v___y_2131_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_dec_ref_known(v___x_2141_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2128_) == 1)
{
lean_object* v_elan_x3f_2142_; 
v_elan_x3f_2142_ = lean_ctor_get(v_lakeEnv_2127_, 2);
if (lean_obj_tag(v_elan_x3f_2142_) == 1)
{
lean_object* v_val_2143_; lean_object* v_val_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_elan_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_val_2143_ = lean_ctor_get(v_lakeArgs_x3f_2128_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_lakeArgs_x3f_2128_, 1);
v_val_2144_ = lean_ctor_get(v_elan_x3f_2142_, 0);
v___x_2145_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2119_);
v___x_2146_ = lean_apply_2(v_a_2119_, v___x_2145_, lean_box(0));
v___x_2147_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2148_ = lean_ctor_get(v_val_2144_, 1);
lean_inc_ref(v_elan_2148_);
v___x_2149_ = 1;
v___x_2150_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2151_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2152_ = lean_array_push(v___x_2151_, v___y_2134_);
v___x_2153_ = lean_array_push(v___x_2152_, v___x_2150_);
v___x_2154_ = l_Array_append___redArg(v___x_2153_, v_val_2143_);
lean_dec(v_val_2143_);
v___x_2155_ = lean_box(0);
v___x_2156_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2127_);
v___x_2157_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2157_, 0, v___x_2147_);
lean_ctor_set(v___x_2157_, 1, v_elan_2148_);
lean_ctor_set(v___x_2157_, 2, v___x_2154_);
lean_ctor_set(v___x_2157_, 3, v___x_2155_);
lean_ctor_set(v___x_2157_, 4, v___x_2156_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*5, v___x_2149_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*5 + 1, v___y_2133_);
v___x_2158_ = lean_io_process_spawn(v___x_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2160_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2160_ = lean_io_process_child_wait(v___x_2147_, v_a_2159_);
lean_dec(v_a_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; uint32_t v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = lean_unbox_uint32(v_a_2161_);
lean_dec(v_a_2161_);
v___x_2163_ = lean_uint32_to_uint8(v___x_2162_);
v___x_2164_ = lean_io_exit(v___x_2163_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2185_; 
v_a_2173_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2175_ = v___x_2164_;
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2164_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2185_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2177_ = lean_io_error_to_string(v_a_2173_);
v___x_2178_ = 3;
v___x_2179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*1, v___x_2178_);
lean_inc_ref(v_a_2119_);
v___x_2180_ = lean_apply_2(v_a_2119_, v___x_2179_, lean_box(0));
v___x_2181_ = lean_box(0);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2181_);
v___x_2183_ = v___x_2175_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2198_; 
v_a_2186_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2188_ = v___x_2160_;
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2160_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2198_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2190_ = lean_io_error_to_string(v_a_2186_);
v___x_2191_ = 3;
v___x_2192_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*1, v___x_2191_);
lean_inc_ref(v_a_2119_);
v___x_2193_ = lean_apply_2(v_a_2119_, v___x_2192_, lean_box(0));
v___x_2194_ = lean_box(0);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2194_);
v___x_2196_ = v___x_2188_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2211_; 
v_a_2199_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2201_ = v___x_2158_;
v_isShared_2202_ = v_isSharedCheck_2211_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2158_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2211_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2203_ = lean_io_error_to_string(v_a_2199_);
v___x_2204_ = 3;
v___x_2205_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*1, v___x_2204_);
lean_inc_ref(v_a_2119_);
v___x_2206_ = lean_apply_2(v_a_2119_, v___x_2205_, lean_box(0));
v___x_2207_ = lean_box(0);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2207_);
v___x_2209_ = v___x_2201_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; 
lean_dec_ref_known(v_lakeArgs_x3f_2128_, 1);
lean_dec_ref(v___y_2134_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2212_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2119_);
v___x_2213_ = lean_apply_2(v_a_2119_, v___x_2212_, lean_box(0));
v___x_2214_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2215_ = lean_io_exit(v___x_2214_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2236_; 
v_a_2224_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2226_ = v___x_2215_;
v_isShared_2227_ = v_isSharedCheck_2236_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2215_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2236_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; uint8_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2228_ = lean_io_error_to_string(v_a_2224_);
v___x_2229_ = 3;
v___x_2230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*1, v___x_2229_);
lean_inc_ref(v_a_2119_);
v___x_2231_ = lean_apply_2(v_a_2119_, v___x_2230_, lean_box(0));
v___x_2232_ = lean_box(0);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v___x_2232_);
v___x_2234_ = v___x_2226_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v___y_2134_);
lean_dec(v_lakeArgs_x3f_2128_);
lean_dec_ref(v_lakeEnv_2127_);
v___x_2237_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2119_);
v___x_2238_ = lean_apply_2(v_a_2119_, v___x_2237_, lean_box(0));
v___x_2239_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2240_ = lean_io_exit(v___x_2239_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2261_; 
v_a_2249_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2251_ = v___x_2240_;
v_isShared_2252_ = v_isSharedCheck_2261_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2240_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2261_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2253_ = lean_io_error_to_string(v_a_2249_);
v___x_2254_ = 3;
v___x_2255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*1, v___x_2254_);
lean_inc_ref(v_a_2119_);
v___x_2256_ = lean_apply_2(v_a_2119_, v___x_2255_, lean_box(0));
v___x_2257_ = lean_box(0);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2257_);
v___x_2259_ = v___x_2251_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v___y_2134_);
lean_dec(v_lakeArgs_x3f_2128_);
lean_dec_ref(v_lakeEnv_2127_);
v_a_2262_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2264_ = v___x_2141_;
v_isShared_2265_ = v_isSharedCheck_2274_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2141_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2274_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2266_ = lean_io_error_to_string(v_a_2262_);
v___x_2267_ = 3;
v___x_2268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2268_, 0, v___x_2266_);
lean_ctor_set_uint8(v___x_2268_, sizeof(void*)*1, v___x_2267_);
lean_inc_ref(v_a_2119_);
v___x_2269_ = lean_apply_2(v_a_2119_, v___x_2268_, lean_box(0));
v___x_2270_ = lean_box(0);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2270_);
v___x_2272_ = v___x_2264_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
v___jp_2275_:
{
lean_object* v___x_2279_; lean_object* v_toString_2280_; 
v___x_2279_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2280_ = lean_ctor_get(v___y_2277_, 0);
lean_inc_ref(v_toString_2280_);
lean_dec_ref(v___y_2277_);
v___y_2131_ = v___y_2276_;
v___y_2132_ = v___x_2279_;
v___y_2133_ = v___y_2278_;
v___y_2134_ = v_toString_2280_;
goto v___jp_2130_;
}
v___jp_2282_:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_nat_dec_lt(v___x_2281_, v___y_2283_);
if (v___x_2286_ == 0)
{
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
v___y_2122_ = v___y_2285_;
goto v___jp_2121_;
}
else
{
uint8_t v___x_2287_; 
v___x_2287_ = lean_nat_dec_le(v___y_2283_, v___y_2283_);
if (v___x_2287_ == 0)
{
if (v___x_2286_ == 0)
{
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
v___y_2122_ = v___y_2285_;
goto v___jp_2121_;
}
else
{
size_t v___x_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = lean_usize_of_nat(v___y_2283_);
lean_dec(v___y_2283_);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2284_, v___x_2288_, v___x_2289_, v___y_2285_);
lean_dec_ref(v___y_2284_);
v___y_2122_ = v___x_2290_;
goto v___jp_2121_;
}
}
else
{
size_t v___x_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = ((size_t)0ULL);
v___x_2292_ = lean_usize_of_nat(v___y_2283_);
lean_dec(v___y_2283_);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2284_, v___x_2291_, v___x_2292_, v___y_2285_);
lean_dec_ref(v___y_2284_);
v___y_2122_ = v___x_2293_;
goto v___jp_2121_;
}
}
}
v___jp_2294_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_inc_ref(v___y_2297_);
v___x_2302_ = lean_string_append(v___y_2297_, v___y_2301_);
lean_dec_ref(v___y_2301_);
v___x_2303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2304_ = lean_string_append(v___x_2302_, v___x_2303_);
v___x_2305_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2299_, v___y_2296_);
v___x_2306_ = lean_string_append(v___x_2304_, v___x_2305_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = lean_string_append(v___x_2306_, v___y_2295_);
v___y_2283_ = v___y_2298_;
v___y_2284_ = v___y_2300_;
v___y_2285_ = v___x_2307_;
goto v___jp_2282_;
}
v___jp_2308_:
{
lean_object* v___x_2315_; lean_object* v_toString_2316_; 
v___x_2315_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2316_ = lean_ctor_get(v___y_2309_, 0);
lean_inc_ref(v_toString_2316_);
lean_dec_ref(v___y_2309_);
v___y_2295_ = v___y_2314_;
v___y_2296_ = v___y_2310_;
v___y_2297_ = v___x_2315_;
v___y_2298_ = v___y_2312_;
v___y_2299_ = v___y_2311_;
v___y_2300_ = v___y_2313_;
v___y_2301_ = v_toString_2316_;
goto v___jp_2294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2396_, lean_object* v_rootDeps_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2396_, v_rootDeps_2397_, v_a_2398_);
lean_dec_ref(v_a_2398_);
lean_dec_ref(v_rootDeps_2397_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2401_, lean_object* v_dep_2402_, lean_object* v_ws_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2403_, v_pkg_2401_, v_dep_2402_, v_a_2404_, v_a_2405_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2411_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v_fst_2409_ = lean_ctor_get(v_a_2408_, 0);
lean_inc_n(v_fst_2409_, 2);
v_snd_2410_ = lean_ctor_get(v_a_2408_, 1);
lean_inc(v_snd_2410_);
lean_dec(v_a_2408_);
v___x_2411_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2409_, v_snd_2410_, v_a_2405_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2428_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2428_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2428_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v_snd_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2426_; 
v_snd_2416_ = lean_ctor_get(v_a_2412_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_a_2412_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v_a_2412_, 0);
lean_dec(v_unused_2427_);
v___x_2418_ = v_a_2412_;
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_snd_2416_);
lean_dec(v_a_2412_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2426_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v_fst_2409_);
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_fst_2409_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_snd_2416_);
v___x_2421_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2421_);
v___x_2423_ = v___x_2414_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_fst_2409_);
v_a_2429_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2411_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2411_);
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
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2437_, lean_object* v_dep_2438_, lean_object* v_ws_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2437_, v_dep_2438_, v_ws_2439_, v_a_2440_, v_a_2441_);
lean_dec_ref(v_a_2441_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2444_, lean_object* v_ws_2445_, lean_object* v_pkg_2446_, lean_object* v_dep_2447_, lean_object* v_a_2448_){
_start:
{
uint8_t v___y_2451_; lean_object* v___y_2452_; lean_object* v_name_2482_; lean_object* v___x_2483_; 
v_name_2482_ = lean_ctor_get(v_dep_2447_, 0);
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2448_, v_name_2482_);
if (lean_obj_tag(v___x_2483_) == 1)
{
lean_object* v_val_2484_; lean_object* v_lakeEnv_2485_; lean_object* v_packages_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_config_2489_; lean_object* v_dir_2490_; lean_object* v_toWorkspaceConfig_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec_ref(v_dep_2447_);
lean_dec_ref(v_pkg_2446_);
v_val_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v_lakeEnv_2485_ = lean_ctor_get(v_ws_2445_, 0);
lean_inc_ref(v_lakeEnv_2485_);
v_packages_2486_ = lean_ctor_get(v_ws_2445_, 4);
lean_inc_ref(v_packages_2486_);
lean_dec_ref(v_ws_2445_);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_array_fget(v_packages_2486_, v___x_2487_);
lean_dec_ref(v_packages_2486_);
v_config_2489_ = lean_ctor_get(v___x_2488_, 6);
lean_inc_ref(v_config_2489_);
v_dir_2490_ = lean_ctor_get(v___x_2488_, 4);
lean_inc_ref(v_dir_2490_);
lean_dec(v___x_2488_);
v_toWorkspaceConfig_2491_ = lean_ctor_get(v_config_2489_, 0);
lean_inc_ref(v_toWorkspaceConfig_2491_);
lean_dec_ref(v_config_2489_);
v___x_2492_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2491_);
v___x_2493_ = l_Lake_PackageEntry_materialize(v_val_2484_, v_lakeEnv_2485_, v_dir_2490_, v___x_2492_, v___y_2444_);
lean_dec_ref(v_lakeEnv_2485_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2502_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_a_2494_);
lean_ctor_set(v___x_2498_, 1, v_a_2448_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_a_2448_);
v_a_2503_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2493_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2493_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_wsIdx_2511_; lean_object* v_relDir_2512_; uint8_t v___y_2514_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
lean_dec(v___x_2483_);
v_wsIdx_2511_ = lean_ctor_get(v_pkg_2446_, 0);
lean_inc(v_wsIdx_2511_);
v_relDir_2512_ = lean_ctor_get(v_pkg_2446_, 5);
lean_inc_ref(v_relDir_2512_);
lean_dec_ref(v_pkg_2446_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_nat_dec_eq(v_wsIdx_2511_, v___x_2518_);
lean_dec(v_wsIdx_2511_);
if (v___x_2519_ == 0)
{
uint8_t v___x_2520_; 
v___x_2520_ = 1;
v___y_2514_ = v___x_2520_;
goto v___jp_2513_;
}
else
{
uint8_t v___x_2521_; 
v___x_2521_ = 0;
v___y_2514_ = v___x_2521_;
goto v___jp_2513_;
}
v___jp_2513_:
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2516_ = lean_string_dec_eq(v_relDir_2512_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lake_joinRelative(v_relDir_2512_, v___x_2515_);
v___y_2451_ = v___y_2514_;
v___y_2452_ = v___x_2517_;
goto v___jp_2450_;
}
else
{
v___y_2451_ = v___y_2514_;
v___y_2452_ = v_relDir_2512_;
goto v___jp_2450_;
}
}
}
v___jp_2450_:
{
lean_object* v_lakeEnv_2453_; lean_object* v_packages_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v_config_2457_; lean_object* v_dir_2458_; lean_object* v_toWorkspaceConfig_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_lakeEnv_2453_ = lean_ctor_get(v_ws_2445_, 0);
lean_inc_ref(v_lakeEnv_2453_);
v_packages_2454_ = lean_ctor_get(v_ws_2445_, 4);
lean_inc_ref(v_packages_2454_);
lean_dec_ref(v_ws_2445_);
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = lean_array_fget(v_packages_2454_, v___x_2455_);
lean_dec_ref(v_packages_2454_);
v_config_2457_ = lean_ctor_get(v___x_2456_, 6);
lean_inc_ref(v_config_2457_);
v_dir_2458_ = lean_ctor_get(v___x_2456_, 4);
lean_inc_ref(v_dir_2458_);
lean_dec(v___x_2456_);
v_toWorkspaceConfig_2459_ = lean_ctor_get(v_config_2457_, 0);
lean_inc_ref(v_toWorkspaceConfig_2459_);
lean_dec_ref(v_config_2457_);
v___x_2460_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2459_);
v___x_2461_ = l_Lake_Dependency_materialize(v_dep_2447_, v___y_2451_, v_lakeEnv_2453_, v_dir_2458_, v___x_2460_, v___y_2452_, v___y_2444_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2473_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_manifestEntry_2466_; lean_object* v_name_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v_manifestEntry_2466_ = lean_ctor_get(v_a_2462_, 4);
v_name_2467_ = lean_ctor_get(v_manifestEntry_2466_, 0);
lean_inc_ref(v_manifestEntry_2466_);
lean_inc(v_name_2467_);
v___x_2468_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2467_, v_manifestEntry_2466_, v_a_2448_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_a_2462_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2469_);
v___x_2471_ = v___x_2464_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_a_2448_);
v_a_2474_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2461_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2461_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2522_, lean_object* v_ws_2523_, lean_object* v_pkg_2524_, lean_object* v_dep_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2522_, v_ws_2523_, v_pkg_2524_, v_dep_2525_, v_a_2526_);
lean_dec_ref(v___y_2522_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2529_, lean_object* v_dep_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_manifestEntry_2533_; lean_object* v_pkgDir_2534_; lean_object* v_name_2535_; lean_object* v_manifestFile_x3f_2536_; lean_object* v___y_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v_val_2600_; lean_object* v___y_2628_; 
v_manifestEntry_2533_ = lean_ctor_get(v_dep_2530_, 4);
v_pkgDir_2534_ = lean_ctor_get(v_dep_2530_, 0);
v_name_2535_ = lean_ctor_get(v_manifestEntry_2533_, 0);
v_manifestFile_x3f_2536_ = lean_ctor_get(v_manifestEntry_2533_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2536_) == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2534_);
v___x_2649_ = l_Lake_joinRelative(v_pkgDir_2534_, v___x_2648_);
v___y_2628_ = v___x_2649_;
goto v___jp_2627_;
}
else
{
lean_object* v_val_2650_; lean_object* v___x_2651_; 
v_val_2650_ = lean_ctor_get(v_manifestFile_x3f_2536_, 0);
lean_inc(v_val_2650_);
lean_inc_ref(v_pkgDir_2534_);
v___x_2651_ = l_Lake_joinRelative(v_pkgDir_2534_, v_val_2650_);
v___y_2628_ = v___x_2651_;
goto v___jp_2627_;
}
v___jp_2537_:
{
if (lean_obj_tag(v_fst_2539_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2570_; 
lean_inc(v_name_2535_);
lean_dec_ref(v_dep_2530_);
v_a_2541_ = lean_ctor_get(v_fst_2539_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_fst_2539_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2543_ = v_fst_2539_;
v_isShared_2544_ = v_isSharedCheck_2570_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v_fst_2539_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2570_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
if (lean_obj_tag(v_a_2541_) == 11)
{
uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_dec_ref_known(v_a_2541_, 2);
v___x_2545_ = 0;
v___x_2546_ = l_Lean_Name_toString(v_name_2535_, v___x_2545_);
v___x_2547_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2548_ = lean_string_append(v___x_2546_, v___x_2547_);
v___x_2549_ = lean_string_append(v___x_2548_, v___y_2538_);
lean_dec_ref(v___y_2538_);
v___x_2550_ = 2;
v___x_2551_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set_uint8(v___x_2551_, sizeof(void*)*1, v___x_2550_);
v___x_2552_ = lean_apply_2(v___y_2529_, v___x_2551_, lean_box(0));
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v_snd_2540_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2553_);
v___x_2555_ = v___x_2543_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
else
{
uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_dec_ref(v___y_2538_);
v___x_2557_ = 0;
v___x_2558_ = l_Lean_Name_toString(v_name_2535_, v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2560_ = lean_string_append(v___x_2558_, v___x_2559_);
v___x_2561_ = lean_io_error_to_string(v_a_2541_);
v___x_2562_ = lean_string_append(v___x_2560_, v___x_2561_);
lean_dec_ref(v___x_2561_);
v___x_2563_ = 2;
v___x_2564_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2564_, 0, v___x_2562_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*1, v___x_2563_);
v___x_2565_ = lean_apply_2(v___y_2529_, v___x_2564_, lean_box(0));
v___x_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_snd_2540_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2566_);
v___x_2568_ = v___x_2543_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2529_);
v_a_2571_ = lean_ctor_get(v_fst_2539_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_fst_2539_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2573_ = v_fst_2539_;
v_isShared_2574_ = v_isSharedCheck_2595_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v_fst_2539_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2595_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_packages_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v_packages_2575_ = lean_ctor_get(v_a_2571_, 3);
lean_inc_ref(v_packages_2575_);
lean_dec(v_a_2571_);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_array_get_size(v_packages_2575_);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_nat_dec_lt(v___x_2576_, v___x_2577_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_dec_ref(v_packages_2575_);
lean_dec_ref(v_dep_2530_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v_snd_2540_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2580_);
v___x_2582_ = v___x_2573_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
else
{
uint8_t v___x_2584_; 
v___x_2584_ = lean_nat_dec_le(v___x_2577_, v___x_2577_);
if (v___x_2584_ == 0)
{
if (v___x_2579_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec_ref(v_packages_2575_);
lean_dec_ref(v_dep_2530_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2578_);
lean_ctor_set(v___x_2585_, 1, v_snd_2540_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2585_);
v___x_2587_ = v___x_2573_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
else
{
size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
lean_del_object(v___x_2573_);
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = lean_usize_of_nat(v___x_2577_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2530_, v_packages_2575_, v___x_2589_, v___x_2590_, v___x_2578_, v_snd_2540_);
lean_dec_ref(v_packages_2575_);
return v___x_2591_;
}
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
lean_del_object(v___x_2573_);
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2577_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2530_, v_packages_2575_, v___x_2592_, v___x_2593_, v___x_2578_, v_snd_2540_);
lean_dec_ref(v_packages_2575_);
return v___x_2594_;
}
}
}
}
}
v___jp_2596_:
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = lean_array_get_size(v___y_2598_);
v___x_2602_ = lean_nat_dec_lt(v___y_2599_, v___x_2601_);
if (v___x_2602_ == 0)
{
v___y_2538_ = v___y_2597_;
v_fst_2539_ = v_val_2600_;
v_snd_2540_ = v_a_2531_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_nat_dec_le(v___x_2601_, v___x_2601_);
if (v___x_2604_ == 0)
{
if (v___x_2602_ == 0)
{
v___y_2538_ = v___y_2597_;
v_fst_2539_ = v_val_2600_;
v_snd_2540_ = v_a_2531_;
goto v___jp_2537_;
}
else
{
size_t v___x_2605_; size_t v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = lean_usize_of_nat(v___x_2601_);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2598_, v___x_2605_, v___x_2606_, v___x_2603_, v___y_2529_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_dec_ref_known(v___x_2607_, 1);
v___y_2538_ = v___y_2597_;
v_fst_2539_ = v_val_2600_;
v_snd_2540_ = v_a_2531_;
goto v___jp_2537_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec_ref(v_val_2600_);
lean_dec_ref(v___y_2597_);
lean_dec(v_a_2531_);
lean_dec_ref(v_dep_2530_);
lean_dec_ref(v___y_2529_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
else
{
size_t v___x_2616_; size_t v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = ((size_t)0ULL);
v___x_2617_ = lean_usize_of_nat(v___x_2601_);
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2598_, v___x_2616_, v___x_2617_, v___x_2603_, v___y_2529_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_dec_ref_known(v___x_2618_, 1);
v___y_2538_ = v___y_2597_;
v_fst_2539_ = v_val_2600_;
v_snd_2540_ = v_a_2531_;
goto v___jp_2537_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_val_2600_);
lean_dec_ref(v___y_2597_);
lean_dec(v_a_2531_);
lean_dec_ref(v_dep_2530_);
lean_dec_ref(v___y_2529_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
}
v___jp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2628_);
v___x_2631_ = l_Lake_Manifest_load(v___y_2628_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 1);
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
v___y_2597_ = v___y_2628_;
v___y_2598_ = v___x_2630_;
v___y_2599_ = v___x_2629_;
v_val_2600_ = v___x_2637_;
goto v___jp_2596_;
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_a_2640_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2631_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2631_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 0);
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
v___y_2597_ = v___y_2628_;
v___y_2598_ = v___x_2630_;
v___y_2599_ = v___x_2629_;
v_val_2600_ = v___x_2645_;
goto v___jp_2596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2652_, lean_object* v_dep_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2652_, v_dep_2653_, v_a_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2661_, v___y_2659_, v___y_2657_, v___y_2658_, v___y_2660_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___x_2667_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v_fst_2665_ = lean_ctor_get(v_a_2664_, 0);
lean_inc_n(v_fst_2665_, 2);
v_snd_2666_ = lean_ctor_get(v_a_2664_, 1);
lean_inc(v_snd_2666_);
lean_dec(v_a_2664_);
v___x_2667_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2661_, v_fst_2665_, v_snd_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2684_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2684_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2684_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_snd_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2682_; 
v_snd_2672_ = lean_ctor_get(v_a_2668_, 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_a_2668_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v_a_2668_, 0);
lean_dec(v_unused_2683_);
v___x_2674_ = v_a_2668_;
v_isShared_2675_ = v_isSharedCheck_2682_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_snd_2672_);
lean_dec(v_a_2668_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2682_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v_fst_2665_);
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_fst_2665_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_snd_2672_);
v___x_2677_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2677_);
v___x_2679_ = v___x_2670_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_fst_2665_);
v_a_2685_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2667_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2667_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_dec_ref(v___y_2661_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2700_, lean_object* v_ws_2701_, lean_object* v_toUpdate_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___y_2706_; lean_object* v___y_2711_; lean_object* v_fst_2712_; lean_object* v_snd_2713_; lean_object* v_packages_2732_; lean_object* v___x_2733_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v_val_2738_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___x_2786_; lean_object* v_baseName_2787_; lean_object* v_dir_2788_; lean_object* v_config_2789_; lean_object* v_relManifestFile_2790_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; uint8_t v_fst_2795_; lean_object* v_snd_2796_; lean_object* v_packagesDir_x3f_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2858_; lean_object* v___y_2859_; uint8_t v___x_2862_; lean_object* v_rootName_2863_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v_val_2917_; lean_object* v___x_2943_; 
v_packages_2732_ = lean_ctor_get(v_ws_2701_, 4);
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2786_ = lean_array_fget_borrowed(v_packages_2732_, v___x_2733_);
v_baseName_2787_ = lean_ctor_get(v___x_2786_, 1);
v_dir_2788_ = lean_ctor_get(v___x_2786_, 4);
v_config_2789_ = lean_ctor_get(v___x_2786_, 6);
v_relManifestFile_2790_ = lean_ctor_get(v___x_2786_, 9);
v___x_2862_ = 0;
lean_inc(v_baseName_2787_);
v_rootName_2863_ = l_Lean_Name_toString(v_baseName_2787_, v___x_2862_);
lean_inc_ref(v_relManifestFile_2790_);
lean_inc_ref(v_dir_2788_);
v___x_2914_ = l_Lake_joinRelative(v_dir_2788_, v_relManifestFile_2790_);
v___x_2915_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2943_ = l_Lake_Manifest_load(v___x_2914_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set_tag(v___x_2946_, 1);
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
v_val_2917_ = v___x_2949_;
goto v___jp_2916_;
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_a_2952_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2943_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2943_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 0);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
v_val_2917_ = v___x_2957_;
goto v___jp_2916_;
}
}
}
v___jp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v___y_2706_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
v___jp_2710_:
{
if (lean_obj_tag(v_fst_2712_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_snd_2713_);
v_a_2714_ = lean_ctor_get(v_fst_2712_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_fst_2712_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2716_ = v_fst_2712_;
v_isShared_2717_ = v_isSharedCheck_2728_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v_fst_2712_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2728_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2718_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2719_ = lean_io_error_to_string(v_a_2714_);
v___x_2720_ = lean_string_append(v___x_2718_, v___x_2719_);
lean_dec_ref(v___x_2719_);
v___x_2721_ = 3;
v___x_2722_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*1, v___x_2721_);
lean_inc_ref(v___y_2711_);
v___x_2723_ = lean_apply_2(v___y_2711_, v___x_2722_, lean_box(0));
v___x_2724_ = lean_box(0);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 1);
lean_ctor_set(v___x_2716_, 0, v___x_2724_);
v___x_2726_ = v___x_2716_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_dec_ref(v_fst_2712_);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v_snd_2713_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
v___jp_2734_:
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = lean_array_get_size(v___y_2736_);
v___x_2740_ = lean_nat_dec_lt(v___x_2733_, v___x_2739_);
if (v___x_2740_ == 0)
{
v___y_2711_ = v___y_2737_;
v_fst_2712_ = v_val_2738_;
v_snd_2713_ = v___y_2735_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2741_ = lean_box(0);
v___x_2742_ = lean_nat_dec_le(v___x_2739_, v___x_2739_);
if (v___x_2742_ == 0)
{
if (v___x_2740_ == 0)
{
v___y_2711_ = v___y_2737_;
v_fst_2712_ = v_val_2738_;
v_snd_2713_ = v___y_2735_;
goto v___jp_2710_;
}
else
{
size_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = lean_usize_of_nat(v___x_2739_);
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2736_, v___x_2743_, v___x_2744_, v___x_2741_, v___y_2737_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_dec_ref_known(v___x_2745_, 1);
v___y_2711_ = v___y_2737_;
v_fst_2712_ = v_val_2738_;
v_snd_2713_ = v___y_2735_;
goto v___jp_2710_;
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v_val_2738_);
lean_dec(v___y_2735_);
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
else
{
size_t v___x_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = lean_usize_of_nat(v___x_2739_);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2736_, v___x_2754_, v___x_2755_, v___x_2741_, v___y_2737_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_dec_ref_known(v___x_2756_, 1);
v___y_2711_ = v___y_2737_;
v_fst_2712_ = v_val_2738_;
v_snd_2713_ = v___y_2735_;
goto v___jp_2710_;
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_val_2738_);
lean_dec(v___y_2735_);
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
}
v___jp_2765_:
{
if (lean_obj_tag(v___y_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
v_a_2770_ = lean_ctor_get(v___y_2769_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___y_2769_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___y_2769_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___y_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 1);
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
v___y_2735_ = v___y_2766_;
v___y_2736_ = v___y_2767_;
v___y_2737_ = v___y_2768_;
v_val_2738_ = v___x_2775_;
goto v___jp_2734_;
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_a_2778_ = lean_ctor_get(v___y_2769_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___y_2769_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___y_2769_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___y_2769_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 0);
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
v___y_2735_ = v___y_2766_;
v___y_2736_ = v___y_2767_;
v___y_2737_ = v___y_2768_;
v_val_2738_ = v___x_2783_;
goto v___jp_2734_;
}
}
}
}
v___jp_2791_:
{
lean_object* v_toWorkspaceConfig_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_toWorkspaceConfig_2797_ = lean_ctor_get(v_config_2789_, 0);
v___x_2798_ = l_System_FilePath_normalize(v___y_2793_);
lean_inc_ref(v_toWorkspaceConfig_2797_);
v___x_2799_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2797_);
lean_inc_ref(v___x_2799_);
v___x_2800_ = l_System_FilePath_normalize(v___x_2799_);
v___x_2801_ = lean_string_dec_eq(v___x_2798_, v___x_2800_);
lean_dec_ref(v___x_2800_);
lean_dec_ref(v___x_2798_);
if (v___x_2801_ == 0)
{
if (v_fst_2795_ == 0)
{
lean_dec_ref(v___x_2799_);
lean_dec_ref(v___y_2792_);
v___y_2706_ = v_snd_2796_;
goto v___jp_2705_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2802_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2803_ = lean_string_append(v___x_2802_, v___y_2792_);
v___x_2804_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2805_ = lean_string_append(v___x_2803_, v___x_2804_);
lean_inc_ref(v_dir_2788_);
v___x_2806_ = l_Lake_joinRelative(v_dir_2788_, v___x_2799_);
v___x_2807_ = lean_string_append(v___x_2805_, v___x_2806_);
v___x_2808_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2809_ = lean_string_append(v___x_2807_, v___x_2808_);
v___x_2810_ = 1;
v___x_2811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*1, v___x_2810_);
lean_inc_ref(v___y_2794_);
v___x_2812_ = lean_apply_2(v___y_2794_, v___x_2811_, lean_box(0));
v___x_2813_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2806_);
v___x_2814_ = l_Lake_createParentDirs(v___x_2806_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v___x_2815_; 
lean_dec_ref_known(v___x_2814_, 1);
v___x_2815_ = lean_io_rename(v___y_2792_, v___x_2806_);
lean_dec_ref(v___x_2806_);
lean_dec_ref(v___y_2792_);
v___y_2766_ = v_snd_2796_;
v___y_2767_ = v___x_2813_;
v___y_2768_ = v___y_2794_;
v___y_2769_ = v___x_2815_;
goto v___jp_2765_;
}
else
{
lean_dec_ref(v___x_2806_);
lean_dec_ref(v___y_2792_);
v___y_2766_ = v_snd_2796_;
v___y_2767_ = v___x_2813_;
v___y_2768_ = v___y_2794_;
v___y_2769_ = v___x_2814_;
goto v___jp_2765_;
}
}
}
else
{
lean_dec_ref(v___x_2799_);
lean_dec_ref(v___y_2792_);
v___y_2706_ = v_snd_2796_;
goto v___jp_2705_;
}
}
v___jp_2816_:
{
if (lean_obj_tag(v_packagesDir_x3f_2817_) == 1)
{
lean_object* v_val_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_val_2820_ = lean_ctor_get(v_packagesDir_x3f_2817_, 0);
lean_inc_n(v_val_2820_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2817_, 1);
lean_inc_ref(v_dir_2788_);
v___x_2821_ = l_Lake_joinRelative(v_dir_2788_, v_val_2820_);
v___x_2822_ = l_System_FilePath_pathExists(v___x_2821_);
v___x_2823_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2824_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2824_ == 0)
{
v___y_2792_ = v___x_2821_;
v___y_2793_ = v_val_2820_;
v___y_2794_ = v___y_2819_;
v_fst_2795_ = v___x_2822_;
v_snd_2796_ = v___y_2818_;
goto v___jp_2791_;
}
else
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = lean_box(0);
v___x_2826_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2826_ == 0)
{
if (v___x_2824_ == 0)
{
v___y_2792_ = v___x_2821_;
v___y_2793_ = v_val_2820_;
v___y_2794_ = v___y_2819_;
v_fst_2795_ = v___x_2822_;
v_snd_2796_ = v___y_2818_;
goto v___jp_2791_;
}
else
{
size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2823_, v___x_2827_, v___x_2828_, v___x_2825_, v___y_2819_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_dec_ref_known(v___x_2829_, 1);
v___y_2792_ = v___x_2821_;
v___y_2793_ = v_val_2820_;
v___y_2794_ = v___y_2819_;
v_fst_2795_ = v___x_2822_;
v_snd_2796_ = v___y_2818_;
goto v___jp_2791_;
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec_ref(v___x_2821_);
lean_dec(v_val_2820_);
lean_dec(v___y_2818_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
else
{
size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v___x_2838_ = ((size_t)0ULL);
v___x_2839_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2823_, v___x_2838_, v___x_2839_, v___x_2825_, v___y_2819_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_dec_ref_known(v___x_2840_, 1);
v___y_2792_ = v___x_2821_;
v___y_2793_ = v_val_2820_;
v___y_2794_ = v___y_2819_;
v_fst_2795_ = v___x_2822_;
v_snd_2796_ = v___y_2818_;
goto v___jp_2791_;
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec_ref(v___x_2821_);
lean_dec(v_val_2820_);
lean_dec(v___y_2818_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
}
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec(v_packagesDir_x3f_2817_);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___y_2818_);
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
return v___x_2851_;
}
}
v___jp_2852_:
{
lean_object* v_packagesDir_x3f_2856_; 
v_packagesDir_x3f_2856_ = lean_ctor_get(v___y_2853_, 2);
lean_inc(v_packagesDir_x3f_2856_);
lean_dec_ref(v___y_2853_);
v_packagesDir_x3f_2817_ = v_packagesDir_x3f_2856_;
v___y_2818_ = v___y_2854_;
v___y_2819_ = v___y_2855_;
goto v___jp_2816_;
}
v___jp_2857_:
{
if (lean_obj_tag(v___y_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v_snd_2861_; 
v_a_2860_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___y_2859_, 1);
v_snd_2861_ = lean_ctor_get(v_a_2860_, 1);
lean_inc(v_snd_2861_);
lean_dec(v_a_2860_);
v___y_2853_ = v___y_2858_;
v___y_2854_ = v_snd_2861_;
v___y_2855_ = v_a_2700_;
goto v___jp_2852_;
}
else
{
lean_dec_ref(v___y_2858_);
return v___y_2859_;
}
}
v___jp_2864_:
{
if (lean_obj_tag(v_fst_2865_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2899_; 
v_a_2867_ = lean_ctor_get(v_fst_2865_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_fst_2865_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2869_ = v_fst_2865_;
v_isShared_2870_ = v_isSharedCheck_2899_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v_fst_2865_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2899_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
if (lean_obj_tag(v_a_2867_) == 11)
{
lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
lean_dec_ref_known(v_a_2867_, 2);
v___x_2871_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2872_ = lean_string_append(v_rootName_2863_, v___x_2871_);
v___x_2873_ = 1;
v___x_2874_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set_uint8(v___x_2874_, sizeof(void*)*1, v___x_2873_);
lean_inc_ref(v_a_2700_);
v___x_2875_ = lean_apply_2(v_a_2700_, v___x_2874_, lean_box(0));
v___x_2876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v_snd_2866_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2876_);
v___x_2878_ = v___x_2869_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2702_) == 0)
{
lean_object* v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_dec(v_snd_2866_);
lean_dec_ref(v_rootName_2863_);
v___x_2880_ = lean_io_error_to_string(v_a_2867_);
v___x_2881_ = 3;
v___x_2882_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set_uint8(v___x_2882_, sizeof(void*)*1, v___x_2881_);
lean_inc_ref(v_a_2700_);
v___x_2883_ = lean_apply_2(v_a_2700_, v___x_2882_, lean_box(0));
v___x_2884_ = lean_box(0);
if (v_isShared_2870_ == 0)
{
lean_ctor_set_tag(v___x_2869_, 1);
lean_ctor_set(v___x_2869_, 0, v___x_2884_);
v___x_2886_ = v___x_2869_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2888_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_2889_ = lean_string_append(v_rootName_2863_, v___x_2888_);
v___x_2890_ = lean_io_error_to_string(v_a_2867_);
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
lean_dec_ref(v___x_2890_);
v___x_2892_ = 2;
v___x_2893_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*1, v___x_2892_);
lean_inc_ref(v_a_2700_);
v___x_2894_ = lean_apply_2(v_a_2700_, v___x_2893_, lean_box(0));
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
lean_ctor_set(v___x_2895_, 1, v_snd_2866_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2895_);
v___x_2897_ = v___x_2869_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_2863_);
if (lean_obj_tag(v_toUpdate_2702_) == 0)
{
lean_object* v_a_2900_; lean_object* v_packagesDir_x3f_2901_; lean_object* v_packages_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v_a_2900_ = lean_ctor_get(v_fst_2865_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v_fst_2865_, 1);
v_packagesDir_x3f_2901_ = lean_ctor_get(v_a_2900_, 2);
v_packages_2902_ = lean_ctor_get(v_a_2900_, 3);
v___x_2903_ = lean_array_get_size(v_packages_2902_);
v___x_2904_ = lean_nat_dec_lt(v___x_2733_, v___x_2903_);
if (v___x_2904_ == 0)
{
lean_inc(v_packagesDir_x3f_2901_);
lean_dec(v_a_2900_);
v_packagesDir_x3f_2817_ = v_packagesDir_x3f_2901_;
v___y_2818_ = v_snd_2866_;
v___y_2819_ = v_a_2700_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_nat_dec_le(v___x_2903_, v___x_2903_);
if (v___x_2906_ == 0)
{
if (v___x_2904_ == 0)
{
lean_inc(v_packagesDir_x3f_2901_);
lean_dec(v_a_2900_);
v_packagesDir_x3f_2817_ = v_packagesDir_x3f_2901_;
v___y_2818_ = v_snd_2866_;
v___y_2819_ = v_a_2700_;
goto v___jp_2816_;
}
else
{
size_t v___x_2907_; size_t v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = lean_usize_of_nat(v___x_2903_);
v___x_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2702_, v_packages_2902_, v___x_2907_, v___x_2908_, v___x_2905_, v_snd_2866_);
v___y_2858_ = v_a_2900_;
v___y_2859_ = v___x_2909_;
goto v___jp_2857_;
}
}
else
{
size_t v___x_2910_; size_t v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = ((size_t)0ULL);
v___x_2911_ = lean_usize_of_nat(v___x_2903_);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2702_, v_packages_2902_, v___x_2910_, v___x_2911_, v___x_2905_, v_snd_2866_);
v___y_2858_ = v_a_2900_;
v___y_2859_ = v___x_2912_;
goto v___jp_2857_;
}
}
}
else
{
lean_object* v_a_2913_; 
v_a_2913_ = lean_ctor_get(v_fst_2865_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v_fst_2865_, 1);
v___y_2853_ = v_a_2913_;
v___y_2854_ = v_snd_2866_;
v___y_2855_ = v_a_2700_;
goto v___jp_2852_;
}
}
}
v___jp_2916_:
{
uint8_t v___x_2918_; 
v___x_2918_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2918_ == 0)
{
v_fst_2865_ = v_val_2917_;
v_snd_2866_ = v_a_2703_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2920_ == 0)
{
if (v___x_2918_ == 0)
{
v_fst_2865_ = v_val_2917_;
v_snd_2866_ = v_a_2703_;
goto v___jp_2864_;
}
else
{
size_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2915_, v___x_2921_, v___x_2922_, v___x_2919_, v_a_2700_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_dec_ref_known(v___x_2923_, 1);
v_fst_2865_ = v_val_2917_;
v_snd_2866_ = v_a_2703_;
goto v___jp_2864_;
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v_val_2917_);
lean_dec_ref(v_rootName_2863_);
lean_dec(v_a_2703_);
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
else
{
size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = ((size_t)0ULL);
v___x_2933_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2915_, v___x_2932_, v___x_2933_, v___x_2919_, v_a_2700_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_dec_ref_known(v___x_2934_, 1);
v_fst_2865_ = v_val_2917_;
v_snd_2866_ = v_a_2703_;
goto v___jp_2864_;
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec_ref(v_val_2917_);
lean_dec_ref(v_rootName_2863_);
lean_dec(v_a_2703_);
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2934_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_2960_, lean_object* v_ws_2961_, lean_object* v_toUpdate_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_2960_, v_ws_2961_, v_toUpdate_2962_, v_a_2963_);
lean_dec(v_toUpdate_2962_);
lean_dec_ref(v_ws_2961_);
lean_dec_ref(v_a_2960_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_2966_, lean_object* v_ws_2967_, lean_object* v_rootDeps_2968_){
_start:
{
lean_object* v___y_2971_; lean_object* v_lakeEnv_2976_; lean_object* v_lakeArgs_x3f_2977_; lean_object* v_packages_2978_; lean_object* v___y_2980_; uint8_t v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_3127_; lean_object* v___y_3128_; uint8_t v___y_3129_; lean_object* v___x_3132_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; uint8_t v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; uint8_t v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___x_3168_; lean_object* v_baseName_3169_; lean_object* v_dir_3170_; lean_object* v_config_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_lakeEnv_2976_ = lean_ctor_get(v_ws_2967_, 0);
lean_inc_ref(v_lakeEnv_2976_);
v_lakeArgs_x3f_2977_ = lean_ctor_get(v_ws_2967_, 3);
lean_inc(v_lakeArgs_x3f_2977_);
v_packages_2978_ = lean_ctor_get(v_ws_2967_, 4);
lean_inc_ref(v_packages_2978_);
lean_dec_ref(v_ws_2967_);
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3168_ = lean_array_fget(v_packages_2978_, v___x_3132_);
lean_dec_ref(v_packages_2978_);
v_baseName_3169_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_baseName_3169_);
v_dir_3170_ = lean_ctor_get(v___x_3168_, 4);
lean_inc_ref_n(v_dir_3170_, 2);
v_config_3171_ = lean_ctor_get(v___x_3168_, 6);
lean_inc_ref(v_config_3171_);
lean_dec(v___x_3168_);
v___x_3172_ = l_Lake_toolchainFileName;
v___x_3173_ = l_System_FilePath_join(v_dir_3170_, v___x_3172_);
v___x_3174_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3173_);
lean_dec_ref(v___x_3173_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3233_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3233_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3233_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v_src_3180_; lean_object* v_tc_x3f_3181_; lean_object* v_clashes_3182_; uint8_t v_fixed_3183_; lean_object* v___y_3207_; uint8_t v_fixedToolchain_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v_fixedToolchain_3221_ = lean_ctor_get_uint8(v_config_3171_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_3171_);
v___x_3222_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3223_ = lean_array_get_size(v_rootDeps_2968_);
v___x_3224_ = lean_nat_dec_lt(v___x_3132_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_inc(v_a_3175_);
v_src_3180_ = v_baseName_3169_;
v_tc_x3f_3181_ = v_a_3175_;
v_clashes_3182_ = v___x_3222_;
v_fixed_3183_ = v_fixedToolchain_3221_;
goto v___jp_3179_;
}
else
{
lean_object* v___x_3225_; uint8_t v___x_3226_; 
lean_inc(v_a_3175_);
lean_inc(v_baseName_3169_);
v___x_3225_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3225_, 0, v_baseName_3169_);
lean_ctor_set(v___x_3225_, 1, v_a_3175_);
lean_ctor_set(v___x_3225_, 2, v___x_3222_);
lean_ctor_set_uint8(v___x_3225_, sizeof(void*)*3, v_fixedToolchain_3221_);
v___x_3226_ = lean_nat_dec_le(v___x_3223_, v___x_3223_);
if (v___x_3226_ == 0)
{
if (v___x_3224_ == 0)
{
lean_dec_ref_known(v___x_3225_, 3);
lean_inc(v_a_3175_);
v_src_3180_ = v_baseName_3169_;
v_tc_x3f_3181_ = v_a_3175_;
v_clashes_3182_ = v___x_3222_;
v_fixed_3183_ = v_fixedToolchain_3221_;
goto v___jp_3179_;
}
else
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
lean_dec(v_baseName_3169_);
v___x_3227_ = ((size_t)0ULL);
v___x_3228_ = lean_usize_of_nat(v___x_3223_);
lean_inc_ref(v_dir_3170_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3170_, v_rootDeps_2968_, v___x_3227_, v___x_3228_, v___x_3225_, v_a_2966_);
v___y_3207_ = v___x_3229_;
goto v___jp_3206_;
}
}
else
{
size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v_baseName_3169_);
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = lean_usize_of_nat(v___x_3223_);
lean_inc_ref(v_dir_3170_);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3170_, v_rootDeps_2968_, v___x_3230_, v___x_3231_, v___x_3225_, v_a_2966_);
v___y_3207_ = v___x_3232_;
goto v___jp_3206_;
}
}
v___jp_3179_:
{
lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3184_ = lean_array_get_size(v_clashes_3182_);
v___x_3185_ = lean_nat_dec_lt(v___x_3132_, v___x_3184_);
if (v___x_3185_ == 0)
{
lean_dec_ref(v_clashes_3182_);
lean_dec(v_src_3180_);
if (lean_obj_tag(v_tc_x3f_3181_) == 1)
{
lean_object* v_val_3186_; lean_object* v_rootToolchainFile_3187_; 
v_val_3186_ = lean_ctor_get(v_tc_x3f_3181_, 0);
lean_inc(v_val_3186_);
lean_dec_ref_known(v_tc_x3f_3181_, 1);
v_rootToolchainFile_3187_ = l_Lake_joinRelative(v_dir_3170_, v___x_3172_);
if (lean_obj_tag(v_a_3175_) == 0)
{
lean_del_object(v___x_3177_);
v___y_3127_ = v_val_3186_;
v___y_3128_ = v_rootToolchainFile_3187_;
v___y_3129_ = v___x_3185_;
goto v___jp_3126_;
}
else
{
lean_object* v_val_3188_; uint8_t v___x_3189_; 
v_val_3188_ = lean_ctor_get(v_a_3175_, 0);
lean_inc(v_val_3188_);
lean_dec_ref_known(v_a_3175_, 1);
lean_inc(v_val_3186_);
v___x_3189_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3188_, v_val_3186_);
if (v___x_3189_ == 0)
{
lean_del_object(v___x_3177_);
v___y_3127_ = v_val_3186_;
v___y_3128_ = v_rootToolchainFile_3187_;
v___y_3129_ = v___x_3189_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec_ref(v_rootToolchainFile_3187_);
lean_dec(v_val_3186_);
lean_dec(v_lakeArgs_x3f_2977_);
lean_dec_ref(v_lakeEnv_2976_);
v___x_3190_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2966_);
v___x_3191_ = lean_apply_2(v_a_2966_, v___x_3190_, lean_box(0));
v___x_3192_ = lean_box(0);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3192_);
v___x_3194_ = v___x_3177_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_dec(v_tc_x3f_3181_);
lean_dec(v_a_3175_);
lean_dec_ref(v_dir_3170_);
lean_dec(v_lakeArgs_x3f_2977_);
lean_dec_ref(v_lakeEnv_2976_);
v___x_3196_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2966_);
v___x_3197_ = lean_apply_2(v_a_2966_, v___x_3196_, lean_box(0));
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3197_);
v___x_3199_ = v___x_3177_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_del_object(v___x_3177_);
lean_dec(v_a_3175_);
lean_dec_ref(v_dir_3170_);
lean_dec(v_lakeArgs_x3f_2977_);
lean_dec_ref(v_lakeEnv_2976_);
if (lean_obj_tag(v_tc_x3f_3181_) == 1)
{
if (v_fixed_3183_ == 0)
{
lean_object* v_val_3201_; lean_object* v___x_3202_; 
v_val_3201_ = lean_ctor_get(v_tc_x3f_3181_, 0);
lean_inc(v_val_3201_);
lean_dec_ref_known(v_tc_x3f_3181_, 1);
v___x_3202_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3160_ = v___x_3185_;
v___y_3161_ = v___x_3184_;
v___y_3162_ = v_src_3180_;
v___y_3163_ = v_clashes_3182_;
v___y_3164_ = v_val_3201_;
v___y_3165_ = v___x_3202_;
goto v___jp_3159_;
}
else
{
lean_object* v_val_3203_; lean_object* v___x_3204_; 
v_val_3203_ = lean_ctor_get(v_tc_x3f_3181_, 0);
lean_inc(v_val_3203_);
lean_dec_ref_known(v_tc_x3f_3181_, 1);
v___x_3204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3160_ = v___x_3185_;
v___y_3161_ = v___x_3184_;
v___y_3162_ = v_src_3180_;
v___y_3163_ = v_clashes_3182_;
v___y_3164_ = v_val_3203_;
v___y_3165_ = v___x_3204_;
goto v___jp_3159_;
}
}
else
{
lean_object* v___x_3205_; 
lean_dec(v_tc_x3f_3181_);
lean_dec(v_src_3180_);
v___x_3205_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3134_ = v___x_3184_;
v___y_3135_ = v_clashes_3182_;
v___y_3136_ = v___x_3205_;
goto v___jp_3133_;
}
}
}
v___jp_3206_:
{
if (lean_obj_tag(v___y_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v_src_3209_; lean_object* v_tc_x3f_3210_; lean_object* v_clashes_3211_; uint8_t v_fixed_3212_; 
v_a_3208_ = lean_ctor_get(v___y_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___y_3207_, 1);
v_src_3209_ = lean_ctor_get(v_a_3208_, 0);
lean_inc(v_src_3209_);
v_tc_x3f_3210_ = lean_ctor_get(v_a_3208_, 1);
lean_inc(v_tc_x3f_3210_);
v_clashes_3211_ = lean_ctor_get(v_a_3208_, 2);
lean_inc_ref(v_clashes_3211_);
v_fixed_3212_ = lean_ctor_get_uint8(v_a_3208_, sizeof(void*)*3);
lean_dec(v_a_3208_);
v_src_3180_ = v_src_3209_;
v_tc_x3f_3181_ = v_tc_x3f_3210_;
v_clashes_3182_ = v_clashes_3211_;
v_fixed_3183_ = v_fixed_3212_;
goto v___jp_3179_;
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_del_object(v___x_3177_);
lean_dec(v_a_3175_);
lean_dec_ref(v_dir_3170_);
lean_dec(v_lakeArgs_x3f_2977_);
lean_dec_ref(v_lakeEnv_2976_);
v_a_3213_ = lean_ctor_get(v___y_3207_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___y_3207_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___y_3207_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___y_3207_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3246_; 
lean_dec_ref(v_config_3171_);
lean_dec_ref(v_dir_3170_);
lean_dec(v_baseName_3169_);
lean_dec(v_lakeArgs_x3f_2977_);
lean_dec_ref(v_lakeEnv_2976_);
v_a_3234_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3236_ = v___x_3174_;
v_isShared_3237_ = v_isSharedCheck_3246_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3174_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3246_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3238_ = lean_io_error_to_string(v_a_3234_);
v___x_3239_ = 3;
v___x_3240_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set_uint8(v___x_3240_, sizeof(void*)*1, v___x_3239_);
lean_inc_ref(v_a_2966_);
v___x_3241_ = lean_apply_2(v_a_2966_, v___x_3240_, lean_box(0));
v___x_3242_ = lean_box(0);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3242_);
v___x_3244_ = v___x_3236_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2970_:
{
uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2972_ = 2;
v___x_2973_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2973_, 0, v___y_2971_);
lean_ctor_set_uint8(v___x_2973_, sizeof(void*)*1, v___x_2972_);
lean_inc_ref(v_a_2966_);
v___x_2974_ = lean_apply_2(v_a_2966_, v___x_2973_, lean_box(0));
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
v___jp_2979_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_inc_ref(v___y_2980_);
v___x_2984_ = lean_string_append(v___y_2980_, v___y_2983_);
v___x_2985_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2986_ = lean_string_append(v___x_2984_, v___x_2985_);
v___x_2987_ = 1;
v___x_2988_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set_uint8(v___x_2988_, sizeof(void*)*1, v___x_2987_);
lean_inc_ref(v_a_2966_);
v___x_2989_ = lean_apply_2(v_a_2966_, v___x_2988_, lean_box(0));
v___x_2990_ = l_IO_FS_writeFile(v___y_2982_, v___y_2983_);
lean_dec_ref(v___y_2982_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_dec_ref_known(v___x_2990_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2977_) == 1)
{
lean_object* v_elan_x3f_2991_; 
v_elan_x3f_2991_ = lean_ctor_get(v_lakeEnv_2976_, 2);
if (lean_obj_tag(v_elan_x3f_2991_) == 1)
{
lean_object* v_val_2992_; lean_object* v_val_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_elan_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v_val_2992_ = lean_ctor_get(v_lakeArgs_x3f_2977_, 0);
lean_inc(v_val_2992_);
lean_dec_ref_known(v_lakeArgs_x3f_2977_, 1);
v_val_2993_ = lean_ctor_get(v_elan_x3f_2991_, 0);
v___x_2994_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2966_);
v___x_2995_ = lean_apply_2(v_a_2966_, v___x_2994_, lean_box(0));
v___x_2996_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2997_ = lean_ctor_get(v_val_2993_, 1);
lean_inc_ref(v_elan_2997_);
v___x_2998_ = 1;
v___x_2999_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_3000_ = lean_unsigned_to_nat(4u);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_3000_);
lean_dec_ref(v___x_3001_);
v___x_3002_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_3003_ = lean_array_push(v___x_3002_, v___y_2983_);
v___x_3004_ = lean_array_push(v___x_3003_, v___x_2999_);
v___x_3005_ = l_Array_append___redArg(v___x_3004_, v_val_2992_);
lean_dec(v_val_2992_);
v___x_3006_ = lean_box(0);
v___x_3007_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2976_);
v___x_3008_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3008_, 0, v___x_2996_);
lean_ctor_set(v___x_3008_, 1, v_elan_2997_);
lean_ctor_set(v___x_3008_, 2, v___x_3005_);
lean_ctor_set(v___x_3008_, 3, v___x_3006_);
lean_ctor_set(v___x_3008_, 4, v___x_3007_);
lean_ctor_set_uint8(v___x_3008_, sizeof(void*)*5, v___x_2998_);
lean_ctor_set_uint8(v___x_3008_, sizeof(void*)*5 + 1, v___y_2981_);
v___x_3009_ = lean_io_process_spawn(v___x_3008_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = lean_io_process_child_wait(v___x_2996_, v_a_3010_);
lean_dec(v_a_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; uint32_t v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = lean_unbox_uint32(v_a_3012_);
lean_dec(v_a_3012_);
v___x_3014_ = lean_uint32_to_uint8(v___x_3013_);
v___x_3015_ = lean_io_exit(v___x_3014_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3036_; 
v_a_3024_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3026_ = v___x_3015_;
v_isShared_3027_ = v_isSharedCheck_3036_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3015_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3036_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3028_ = lean_io_error_to_string(v_a_3024_);
v___x_3029_ = 3;
v___x_3030_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set_uint8(v___x_3030_, sizeof(void*)*1, v___x_3029_);
lean_inc_ref(v_a_2966_);
v___x_3031_ = lean_apply_2(v_a_2966_, v___x_3030_, lean_box(0));
v___x_3032_ = lean_box(0);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3032_);
v___x_3034_ = v___x_3026_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3049_; 
v_a_3037_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3039_ = v___x_3011_;
v_isShared_3040_ = v_isSharedCheck_3049_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3011_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3049_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3041_ = lean_io_error_to_string(v_a_3037_);
v___x_3042_ = 3;
v___x_3043_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*1, v___x_3042_);
lean_inc_ref(v_a_2966_);
v___x_3044_ = lean_apply_2(v_a_2966_, v___x_3043_, lean_box(0));
v___x_3045_ = lean_box(0);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3045_);
v___x_3047_ = v___x_3039_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3062_; 
v_a_3050_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3052_ = v___x_3009_;
v_isShared_3053_ = v_isSharedCheck_3062_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3009_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3062_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; uint8_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3054_ = lean_io_error_to_string(v_a_3050_);
v___x_3055_ = 3;
v___x_3056_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*1, v___x_3055_);
lean_inc_ref(v_a_2966_);
v___x_3057_ = lean_apply_2(v_a_2966_, v___x_3056_, lean_box(0));
v___x_3058_ = lean_box(0);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3058_);
v___x_3060_ = v___x_3052_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; 
lean_dec_ref_known(v_lakeArgs_x3f_2977_, 1);
lean_dec_ref(v___y_2983_);
lean_dec_ref(v_lakeEnv_2976_);
v___x_3063_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2966_);
v___x_3064_ = lean_apply_2(v_a_2966_, v___x_3063_, lean_box(0));
v___x_3065_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3066_ = lean_io_exit(v___x_3065_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3087_; 
v_a_3075_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3077_ = v___x_3066_;
v_isShared_3078_ = v_isSharedCheck_3087_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3066_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3087_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3079_ = lean_io_error_to_string(v_a_3075_);
v___x_3080_ = 3;
v___x_3081_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set_uint8(v___x_3081_, sizeof(void*)*1, v___x_3080_);
lean_inc_ref(v_a_2966_);
v___x_3082_ = lean_apply_2(v_a_2966_, v___x_3081_, lean_box(0));
v___x_3083_ = lean_box(0);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3083_);
v___x_3085_ = v___x_3077_;
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
}
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref(v___y_2983_);
lean_dec(v_lakeArgs_x3f_2977_);
lean_dec_ref(v_lakeEnv_2976_);
v___x_3088_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2966_);
v___x_3089_ = lean_apply_2(v_a_2966_, v___x_3088_, lean_box(0));
v___x_3090_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3091_ = lean_io_exit(v___x_3090_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3112_; 
v_a_3100_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3102_ = v___x_3091_;
v_isShared_3103_ = v_isSharedCheck_3112_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3091_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3112_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; uint8_t v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3104_ = lean_io_error_to_string(v_a_3100_);
v___x_3105_ = 3;
v___x_3106_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*1, v___x_3105_);
lean_inc_ref(v_a_2966_);
v___x_3107_ = lean_apply_2(v_a_2966_, v___x_3106_, lean_box(0));
v___x_3108_ = lean_box(0);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3108_);
v___x_3110_ = v___x_3102_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v___y_2983_);
lean_dec(v_lakeArgs_x3f_2977_);
lean_dec_ref(v_lakeEnv_2976_);
v_a_3113_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3115_ = v___x_2990_;
v_isShared_3116_ = v_isSharedCheck_3125_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_2990_);
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
lean_inc_ref(v_a_2966_);
v___x_3120_ = lean_apply_2(v_a_2966_, v___x_3119_, lean_box(0));
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
v___jp_3126_:
{
lean_object* v___x_3130_; lean_object* v_toString_3131_; 
v___x_3130_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3131_ = lean_ctor_get(v___y_3127_, 0);
lean_inc_ref(v_toString_3131_);
lean_dec_ref(v___y_3127_);
v___y_2980_ = v___x_3130_;
v___y_2981_ = v___y_3129_;
v___y_2982_ = v___y_3128_;
v___y_2983_ = v_toString_3131_;
goto v___jp_2979_;
}
v___jp_3133_:
{
uint8_t v___x_3137_; 
v___x_3137_ = lean_nat_dec_lt(v___x_3132_, v___y_3134_);
if (v___x_3137_ == 0)
{
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
v___y_2971_ = v___y_3136_;
goto v___jp_2970_;
}
else
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_nat_dec_le(v___y_3134_, v___y_3134_);
if (v___x_3138_ == 0)
{
if (v___x_3137_ == 0)
{
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
v___y_2971_ = v___y_3136_;
goto v___jp_2970_;
}
else
{
size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = ((size_t)0ULL);
v___x_3140_ = lean_usize_of_nat(v___y_3134_);
lean_dec(v___y_3134_);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3135_, v___x_3139_, v___x_3140_, v___y_3136_);
lean_dec_ref(v___y_3135_);
v___y_2971_ = v___x_3141_;
goto v___jp_2970_;
}
}
else
{
size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = ((size_t)0ULL);
v___x_3143_ = lean_usize_of_nat(v___y_3134_);
lean_dec(v___y_3134_);
v___x_3144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3135_, v___x_3142_, v___x_3143_, v___y_3136_);
lean_dec_ref(v___y_3135_);
v___y_2971_ = v___x_3144_;
goto v___jp_2970_;
}
}
}
v___jp_3145_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_inc_ref(v___y_3147_);
v___x_3153_ = lean_string_append(v___y_3147_, v___y_3152_);
lean_dec_ref(v___y_3152_);
v___x_3154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3155_ = lean_string_append(v___x_3153_, v___x_3154_);
v___x_3156_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3150_, v___y_3146_);
v___x_3157_ = lean_string_append(v___x_3155_, v___x_3156_);
lean_dec_ref(v___x_3156_);
v___x_3158_ = lean_string_append(v___x_3157_, v___y_3148_);
v___y_3134_ = v___y_3149_;
v___y_3135_ = v___y_3151_;
v___y_3136_ = v___x_3158_;
goto v___jp_3133_;
}
v___jp_3159_:
{
lean_object* v___x_3166_; lean_object* v_toString_3167_; 
v___x_3166_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3167_ = lean_ctor_get(v___y_3164_, 0);
lean_inc_ref(v_toString_3167_);
lean_dec_ref(v___y_3164_);
v___y_3146_ = v___y_3160_;
v___y_3147_ = v___x_3166_;
v___y_3148_ = v___y_3165_;
v___y_3149_ = v___y_3161_;
v___y_3150_ = v___y_3162_;
v___y_3151_ = v___y_3163_;
v___y_3152_ = v_toString_3167_;
goto v___jp_3145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3247_, lean_object* v_ws_3248_, lean_object* v_rootDeps_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3247_, v_ws_3248_, v_rootDeps_3249_);
lean_dec_ref(v_rootDeps_3249_);
lean_dec_ref(v_a_3247_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(lean_object* v_msg_3252_){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = lean_box(1);
v___x_3254_ = lean_panic_fn_borrowed(v___x_3253_, v_msg_3252_);
return v___x_3254_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3258_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3259_ = lean_unsigned_to_nat(35u);
v___x_3260_ = lean_unsigned_to_nat(182u);
v___x_3261_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3262_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3263_ = l_mkPanicMessageWithDecl(v___x_3262_, v___x_3261_, v___x_3260_, v___x_3259_, v___x_3258_);
return v___x_3263_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3264_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__2));
v___x_3265_ = lean_unsigned_to_nat(21u);
v___x_3266_ = lean_unsigned_to_nat(183u);
v___x_3267_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__1));
v___x_3268_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3269_ = l_mkPanicMessageWithDecl(v___x_3268_, v___x_3267_, v___x_3266_, v___x_3265_, v___x_3264_);
return v___x_3269_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3272_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3273_ = lean_unsigned_to_nat(35u);
v___x_3274_ = lean_unsigned_to_nat(276u);
v___x_3275_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3276_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3277_ = l_mkPanicMessageWithDecl(v___x_3276_, v___x_3275_, v___x_3274_, v___x_3273_, v___x_3272_);
return v___x_3277_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3278_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__6));
v___x_3279_ = lean_unsigned_to_nat(21u);
v___x_3280_ = lean_unsigned_to_nat(277u);
v___x_3281_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__5));
v___x_3282_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__0));
v___x_3283_ = l_mkPanicMessageWithDecl(v___x_3282_, v___x_3281_, v___x_3280_, v___x_3279_, v___x_3278_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(lean_object* v_k_3284_, lean_object* v_v_3285_, lean_object* v_t_3286_){
_start:
{
if (lean_obj_tag(v_t_3286_) == 0)
{
lean_object* v_size_3287_; lean_object* v_k_3288_; lean_object* v_v_3289_; lean_object* v_l_3290_; lean_object* v_r_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3647_; 
v_size_3287_ = lean_ctor_get(v_t_3286_, 0);
v_k_3288_ = lean_ctor_get(v_t_3286_, 1);
v_v_3289_ = lean_ctor_get(v_t_3286_, 2);
v_l_3290_ = lean_ctor_get(v_t_3286_, 3);
v_r_3291_ = lean_ctor_get(v_t_3286_, 4);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_t_3286_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3293_ = v_t_3286_;
v_isShared_3294_ = v_isSharedCheck_3647_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_r_3291_);
lean_inc(v_l_3290_);
lean_inc(v_v_3289_);
lean_inc(v_k_3288_);
lean_inc(v_size_3287_);
lean_dec(v_t_3286_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3647_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
uint8_t v___x_3295_; 
v___x_3295_ = lean_string_compare(v_k_3284_, v_k_3288_);
switch(v___x_3295_)
{
case 0:
{
lean_object* v___x_3296_; 
lean_dec(v_size_3287_);
v___x_3296_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3284_, v_v_3285_, v_l_3290_);
if (lean_obj_tag(v_r_3291_) == 0)
{
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_size_3297_; lean_object* v_size_3298_; lean_object* v_k_3299_; lean_object* v_v_3300_; lean_object* v_l_3301_; lean_object* v_r_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_size_3297_ = lean_ctor_get(v_r_3291_, 0);
v_size_3298_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_size_3298_);
v_k_3299_ = lean_ctor_get(v___x_3296_, 1);
lean_inc(v_k_3299_);
v_v_3300_ = lean_ctor_get(v___x_3296_, 2);
lean_inc(v_v_3300_);
v_l_3301_ = lean_ctor_get(v___x_3296_, 3);
lean_inc(v_l_3301_);
v_r_3302_ = lean_ctor_get(v___x_3296_, 4);
lean_inc(v_r_3302_);
v___x_3303_ = lean_unsigned_to_nat(3u);
v___x_3304_ = lean_nat_mul(v___x_3303_, v_size_3297_);
v___x_3305_ = lean_nat_dec_lt(v___x_3304_, v_size_3298_);
lean_dec(v___x_3304_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
lean_dec(v_r_3302_);
lean_dec(v_l_3301_);
lean_dec(v_v_3300_);
lean_dec(v_k_3299_);
v___x_3306_ = lean_unsigned_to_nat(1u);
v___x_3307_ = lean_nat_add(v___x_3306_, v_size_3298_);
lean_dec(v_size_3298_);
v___x_3308_ = lean_nat_add(v___x_3307_, v_size_3297_);
lean_dec(v___x_3307_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 3, v___x_3296_);
lean_ctor_set(v___x_3293_, 0, v___x_3308_);
v___x_3310_ = v___x_3293_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3311_, 3, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3311_, 4, v_r_3291_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
else
{
lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3383_; 
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; lean_object* v_unused_3385_; lean_object* v_unused_3386_; lean_object* v_unused_3387_; lean_object* v_unused_3388_; 
v_unused_3384_ = lean_ctor_get(v___x_3296_, 4);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v___x_3296_, 3);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v___x_3296_, 2);
lean_dec(v_unused_3386_);
v_unused_3387_ = lean_ctor_get(v___x_3296_, 1);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v___x_3296_, 0);
lean_dec(v_unused_3388_);
v___x_3313_ = v___x_3296_;
v_isShared_3314_ = v_isSharedCheck_3383_;
goto v_resetjp_3312_;
}
else
{
lean_dec(v___x_3296_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3383_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
if (lean_obj_tag(v_l_3301_) == 0)
{
if (lean_obj_tag(v_r_3302_) == 0)
{
lean_object* v_size_3315_; lean_object* v_size_3316_; lean_object* v_k_3317_; lean_object* v_v_3318_; lean_object* v_l_3319_; lean_object* v_r_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v_size_3315_ = lean_ctor_get(v_l_3301_, 0);
v_size_3316_ = lean_ctor_get(v_r_3302_, 0);
v_k_3317_ = lean_ctor_get(v_r_3302_, 1);
v_v_3318_ = lean_ctor_get(v_r_3302_, 2);
v_l_3319_ = lean_ctor_get(v_r_3302_, 3);
v_r_3320_ = lean_ctor_get(v_r_3302_, 4);
v___x_3321_ = lean_unsigned_to_nat(2u);
v___x_3322_ = lean_nat_mul(v___x_3321_, v_size_3315_);
v___x_3323_ = lean_nat_dec_lt(v_size_3316_, v___x_3322_);
lean_dec(v___x_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3353_; 
lean_inc(v_r_3320_);
lean_inc(v_l_3319_);
lean_inc(v_v_3318_);
lean_inc(v_k_3317_);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_r_3302_);
if (v_isSharedCheck_3353_ == 0)
{
lean_object* v_unused_3354_; lean_object* v_unused_3355_; lean_object* v_unused_3356_; lean_object* v_unused_3357_; lean_object* v_unused_3358_; 
v_unused_3354_ = lean_ctor_get(v_r_3302_, 4);
lean_dec(v_unused_3354_);
v_unused_3355_ = lean_ctor_get(v_r_3302_, 3);
lean_dec(v_unused_3355_);
v_unused_3356_ = lean_ctor_get(v_r_3302_, 2);
lean_dec(v_unused_3356_);
v_unused_3357_ = lean_ctor_get(v_r_3302_, 1);
lean_dec(v_unused_3357_);
v_unused_3358_ = lean_ctor_get(v_r_3302_, 0);
lean_dec(v_unused_3358_);
v___x_3325_ = v_r_3302_;
v_isShared_3326_ = v_isSharedCheck_3353_;
goto v_resetjp_3324_;
}
else
{
lean_dec(v_r_3302_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3353_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___x_3341_; lean_object* v___y_3343_; 
v___x_3327_ = lean_unsigned_to_nat(1u);
v___x_3328_ = lean_nat_add(v___x_3327_, v_size_3298_);
lean_dec(v_size_3298_);
v___x_3329_ = lean_nat_add(v___x_3328_, v_size_3297_);
lean_dec(v___x_3328_);
v___x_3341_ = lean_nat_add(v___x_3327_, v_size_3315_);
if (lean_obj_tag(v_l_3319_) == 0)
{
lean_object* v_size_3351_; 
v_size_3351_ = lean_ctor_get(v_l_3319_, 0);
lean_inc(v_size_3351_);
v___y_3343_ = v_size_3351_;
goto v___jp_3342_;
}
else
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_unsigned_to_nat(0u);
v___y_3343_ = v___x_3352_;
goto v___jp_3342_;
}
v___jp_3330_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3334_ = lean_nat_add(v___y_3331_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec(v___y_3331_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 4, v_r_3291_);
lean_ctor_set(v___x_3325_, 3, v_r_3320_);
lean_ctor_set(v___x_3325_, 2, v_v_3289_);
lean_ctor_set(v___x_3325_, 1, v_k_3288_);
lean_ctor_set(v___x_3325_, 0, v___x_3334_);
v___x_3336_ = v___x_3325_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_r_3320_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v_r_3291_);
v___x_3336_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 4, v___x_3336_);
lean_ctor_set(v___x_3313_, 3, v___y_3332_);
lean_ctor_set(v___x_3313_, 2, v_v_3318_);
lean_ctor_set(v___x_3313_, 1, v_k_3317_);
lean_ctor_set(v___x_3313_, 0, v___x_3329_);
v___x_3338_ = v___x_3313_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_k_3317_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_v_3318_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v___y_3332_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
v___jp_3342_:
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3344_ = lean_nat_add(v___x_3341_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec(v___x_3341_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v_l_3319_);
lean_ctor_set(v___x_3293_, 3, v_l_3301_);
lean_ctor_set(v___x_3293_, 2, v_v_3300_);
lean_ctor_set(v___x_3293_, 1, v_k_3299_);
lean_ctor_set(v___x_3293_, 0, v___x_3344_);
v___x_3346_ = v___x_3293_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_k_3299_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_v_3300_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_l_3301_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_l_3319_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_nat_add(v___x_3327_, v_size_3297_);
if (lean_obj_tag(v_r_3320_) == 0)
{
lean_object* v_size_3348_; 
v_size_3348_ = lean_ctor_get(v_r_3320_, 0);
lean_inc(v_size_3348_);
v___y_3331_ = v___x_3347_;
v___y_3332_ = v___x_3346_;
v___y_3333_ = v_size_3348_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_unsigned_to_nat(0u);
v___y_3331_ = v___x_3347_;
v___y_3332_ = v___x_3346_;
v___y_3333_ = v___x_3349_;
goto v___jp_3330_;
}
}
}
}
}
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
lean_del_object(v___x_3293_);
v___x_3359_ = lean_unsigned_to_nat(1u);
v___x_3360_ = lean_nat_add(v___x_3359_, v_size_3298_);
lean_dec(v_size_3298_);
v___x_3361_ = lean_nat_add(v___x_3360_, v_size_3297_);
lean_dec(v___x_3360_);
v___x_3362_ = lean_nat_add(v___x_3359_, v_size_3297_);
v___x_3363_ = lean_nat_add(v___x_3362_, v_size_3316_);
lean_dec(v___x_3362_);
lean_inc_ref(v_r_3291_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 4, v_r_3291_);
lean_ctor_set(v___x_3313_, 3, v_r_3302_);
lean_ctor_set(v___x_3313_, 2, v_v_3289_);
lean_ctor_set(v___x_3313_, 1, v_k_3288_);
lean_ctor_set(v___x_3313_, 0, v___x_3363_);
v___x_3365_ = v___x_3313_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_r_3302_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_r_3291_);
v___x_3365_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
v_isSharedCheck_3372_ = !lean_is_exclusive(v_r_3291_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; lean_object* v_unused_3374_; lean_object* v_unused_3375_; lean_object* v_unused_3376_; lean_object* v_unused_3377_; 
v_unused_3373_ = lean_ctor_get(v_r_3291_, 4);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_r_3291_, 3);
lean_dec(v_unused_3374_);
v_unused_3375_ = lean_ctor_get(v_r_3291_, 2);
lean_dec(v_unused_3375_);
v_unused_3376_ = lean_ctor_get(v_r_3291_, 1);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_r_3291_, 0);
lean_dec(v_unused_3377_);
v___x_3367_ = v_r_3291_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_dec(v_r_3291_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 4, v___x_3365_);
lean_ctor_set(v___x_3367_, 3, v_l_3301_);
lean_ctor_set(v___x_3367_, 2, v_v_3300_);
lean_ctor_set(v___x_3367_, 1, v_k_3299_);
lean_ctor_set(v___x_3367_, 0, v___x_3361_);
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_k_3299_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_v_3300_);
lean_ctor_set(v_reuseFailAlloc_3371_, 3, v_l_3301_);
lean_ctor_set(v_reuseFailAlloc_3371_, 4, v___x_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec_ref_known(v_l_3301_, 5);
lean_del_object(v___x_3313_);
lean_dec(v_v_3300_);
lean_dec(v_k_3299_);
lean_dec(v_size_3298_);
lean_dec_ref_known(v_r_3291_, 5);
lean_del_object(v___x_3293_);
lean_dec(v_v_3289_);
lean_dec(v_k_3288_);
v___x_3379_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__3);
v___x_3380_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3379_);
return v___x_3380_;
}
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_del_object(v___x_3313_);
lean_dec(v_r_3302_);
lean_dec(v_v_3300_);
lean_dec(v_k_3299_);
lean_dec(v_size_3298_);
lean_dec_ref_known(v_r_3291_, 5);
lean_del_object(v___x_3293_);
lean_dec(v_v_3289_);
lean_dec(v_k_3288_);
v___x_3381_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__4);
v___x_3382_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3381_);
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_size_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v_size_3389_ = lean_ctor_get(v_r_3291_, 0);
v___x_3390_ = lean_unsigned_to_nat(1u);
v___x_3391_ = lean_nat_add(v___x_3390_, v_size_3389_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 3, v___x_3296_);
lean_ctor_set(v___x_3293_, 0, v___x_3391_);
v___x_3393_ = v___x_3293_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3394_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3394_, 3, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3394_, 4, v_r_3291_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
else
{
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_l_3395_; 
v_l_3395_ = lean_ctor_get(v___x_3296_, 3);
lean_inc(v_l_3395_);
if (lean_obj_tag(v_l_3395_) == 0)
{
lean_object* v_r_3396_; 
v_r_3396_ = lean_ctor_get(v___x_3296_, 4);
lean_inc(v_r_3396_);
if (lean_obj_tag(v_r_3396_) == 0)
{
lean_object* v_size_3397_; lean_object* v_k_3398_; lean_object* v_v_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3413_; 
v_size_3397_ = lean_ctor_get(v___x_3296_, 0);
v_k_3398_ = lean_ctor_get(v___x_3296_, 1);
v_v_3399_ = lean_ctor_get(v___x_3296_, 2);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; lean_object* v_unused_3415_; 
v_unused_3414_ = lean_ctor_get(v___x_3296_, 4);
lean_dec(v_unused_3414_);
v_unused_3415_ = lean_ctor_get(v___x_3296_, 3);
lean_dec(v_unused_3415_);
v___x_3401_ = v___x_3296_;
v_isShared_3402_ = v_isSharedCheck_3413_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_v_3399_);
lean_inc(v_k_3398_);
lean_inc(v_size_3397_);
lean_dec(v___x_3296_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3413_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_size_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v_size_3403_ = lean_ctor_get(v_r_3396_, 0);
v___x_3404_ = lean_unsigned_to_nat(1u);
v___x_3405_ = lean_nat_add(v___x_3404_, v_size_3397_);
lean_dec(v_size_3397_);
v___x_3406_ = lean_nat_add(v___x_3404_, v_size_3403_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 4, v_r_3291_);
lean_ctor_set(v___x_3401_, 3, v_r_3396_);
lean_ctor_set(v___x_3401_, 2, v_v_3289_);
lean_ctor_set(v___x_3401_, 1, v_k_3288_);
lean_ctor_set(v___x_3401_, 0, v___x_3406_);
v___x_3408_ = v___x_3401_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_r_3396_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_r_3291_);
v___x_3408_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3410_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3408_);
lean_ctor_set(v___x_3293_, 3, v_l_3395_);
lean_ctor_set(v___x_3293_, 2, v_v_3399_);
lean_ctor_set(v___x_3293_, 1, v_k_3398_);
lean_ctor_set(v___x_3293_, 0, v___x_3405_);
v___x_3410_ = v___x_3293_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_k_3398_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v_v_3399_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v_l_3395_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_object* v_k_3416_; lean_object* v_v_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3429_; 
v_k_3416_ = lean_ctor_get(v___x_3296_, 1);
v_v_3417_ = lean_ctor_get(v___x_3296_, 2);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; lean_object* v_unused_3431_; lean_object* v_unused_3432_; 
v_unused_3430_ = lean_ctor_get(v___x_3296_, 4);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v___x_3296_, 3);
lean_dec(v_unused_3431_);
v_unused_3432_ = lean_ctor_get(v___x_3296_, 0);
lean_dec(v_unused_3432_);
v___x_3419_ = v___x_3296_;
v_isShared_3420_ = v_isSharedCheck_3429_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_v_3417_);
lean_inc(v_k_3416_);
lean_dec(v___x_3296_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3429_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3421_ = lean_unsigned_to_nat(3u);
v___x_3422_ = lean_unsigned_to_nat(1u);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 3, v_r_3396_);
lean_ctor_set(v___x_3419_, 2, v_v_3289_);
lean_ctor_set(v___x_3419_, 1, v_k_3288_);
lean_ctor_set(v___x_3419_, 0, v___x_3422_);
v___x_3424_ = v___x_3419_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3428_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3428_, 3, v_r_3396_);
lean_ctor_set(v_reuseFailAlloc_3428_, 4, v_r_3396_);
v___x_3424_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3426_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3424_);
lean_ctor_set(v___x_3293_, 3, v_l_3395_);
lean_ctor_set(v___x_3293_, 2, v_v_3417_);
lean_ctor_set(v___x_3293_, 1, v_k_3416_);
lean_ctor_set(v___x_3293_, 0, v___x_3421_);
v___x_3426_ = v___x_3293_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_k_3416_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_v_3417_);
lean_ctor_set(v_reuseFailAlloc_3427_, 3, v_l_3395_);
lean_ctor_set(v_reuseFailAlloc_3427_, 4, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
else
{
lean_object* v_r_3433_; 
v_r_3433_ = lean_ctor_get(v___x_3296_, 4);
lean_inc(v_r_3433_);
if (lean_obj_tag(v_r_3433_) == 0)
{
lean_object* v_k_3434_; lean_object* v_v_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3459_; 
v_k_3434_ = lean_ctor_get(v___x_3296_, 1);
v_v_3435_ = lean_ctor_get(v___x_3296_, 2);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3459_ == 0)
{
lean_object* v_unused_3460_; lean_object* v_unused_3461_; lean_object* v_unused_3462_; 
v_unused_3460_ = lean_ctor_get(v___x_3296_, 4);
lean_dec(v_unused_3460_);
v_unused_3461_ = lean_ctor_get(v___x_3296_, 3);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v___x_3296_, 0);
lean_dec(v_unused_3462_);
v___x_3437_ = v___x_3296_;
v_isShared_3438_ = v_isSharedCheck_3459_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_v_3435_);
lean_inc(v_k_3434_);
lean_dec(v___x_3296_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3459_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v_k_3439_; lean_object* v_v_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3455_; 
v_k_3439_ = lean_ctor_get(v_r_3433_, 1);
v_v_3440_ = lean_ctor_get(v_r_3433_, 2);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_r_3433_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; lean_object* v_unused_3457_; lean_object* v_unused_3458_; 
v_unused_3456_ = lean_ctor_get(v_r_3433_, 4);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_r_3433_, 3);
lean_dec(v_unused_3457_);
v_unused_3458_ = lean_ctor_get(v_r_3433_, 0);
lean_dec(v_unused_3458_);
v___x_3442_ = v_r_3433_;
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_v_3440_);
lean_inc(v_k_3439_);
lean_dec(v_r_3433_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3444_ = lean_unsigned_to_nat(3u);
v___x_3445_ = lean_unsigned_to_nat(1u);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 4, v_l_3395_);
lean_ctor_set(v___x_3442_, 3, v_l_3395_);
lean_ctor_set(v___x_3442_, 2, v_v_3435_);
lean_ctor_set(v___x_3442_, 1, v_k_3434_);
lean_ctor_set(v___x_3442_, 0, v___x_3445_);
v___x_3447_ = v___x_3442_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_k_3434_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_v_3435_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_l_3395_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_l_3395_);
v___x_3447_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 4, v_l_3395_);
lean_ctor_set(v___x_3437_, 2, v_v_3289_);
lean_ctor_set(v___x_3437_, 1, v_k_3288_);
lean_ctor_set(v___x_3437_, 0, v___x_3445_);
v___x_3449_ = v___x_3437_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_l_3395_);
lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_l_3395_);
v___x_3449_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3449_);
lean_ctor_set(v___x_3293_, 3, v___x_3447_);
lean_ctor_set(v___x_3293_, 2, v_v_3440_);
lean_ctor_set(v___x_3293_, 1, v_k_3439_);
lean_ctor_set(v___x_3293_, 0, v___x_3444_);
v___x_3451_ = v___x_3293_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3444_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_k_3439_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_v_3440_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v___x_3447_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = lean_unsigned_to_nat(2u);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v_r_3433_);
lean_ctor_set(v___x_3293_, 3, v___x_3296_);
lean_ctor_set(v___x_3293_, 0, v___x_3463_);
v___x_3465_ = v___x_3293_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3466_, 4, v_r_3433_);
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
else
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = lean_unsigned_to_nat(1u);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3296_);
lean_ctor_set(v___x_3293_, 3, v___x_3296_);
lean_ctor_set(v___x_3293_, 0, v___x_3467_);
v___x_3469_ = v___x_3293_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v___x_3296_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
case 1:
{
lean_object* v___x_3472_; 
lean_dec(v_v_3289_);
lean_dec(v_k_3288_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 2, v_v_3285_);
lean_ctor_set(v___x_3293_, 1, v_k_3284_);
v___x_3472_ = v___x_3293_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_size_3287_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_k_3284_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_v_3285_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v_l_3290_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_r_3291_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
default: 
{
lean_object* v___x_3474_; 
lean_dec(v_size_3287_);
v___x_3474_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_3284_, v_v_3285_, v_r_3291_);
if (lean_obj_tag(v_l_3290_) == 0)
{
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_size_3475_; lean_object* v_size_3476_; lean_object* v_k_3477_; lean_object* v_v_3478_; lean_object* v_l_3479_; lean_object* v_r_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; 
v_size_3475_ = lean_ctor_get(v_l_3290_, 0);
v_size_3476_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_size_3476_);
v_k_3477_ = lean_ctor_get(v___x_3474_, 1);
lean_inc(v_k_3477_);
v_v_3478_ = lean_ctor_get(v___x_3474_, 2);
lean_inc(v_v_3478_);
v_l_3479_ = lean_ctor_get(v___x_3474_, 3);
lean_inc(v_l_3479_);
v_r_3480_ = lean_ctor_get(v___x_3474_, 4);
lean_inc(v_r_3480_);
v___x_3481_ = lean_unsigned_to_nat(3u);
v___x_3482_ = lean_nat_mul(v___x_3481_, v_size_3475_);
v___x_3483_ = lean_nat_dec_lt(v___x_3482_, v_size_3476_);
lean_dec(v___x_3482_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_dec(v_r_3480_);
lean_dec(v_l_3479_);
lean_dec(v_v_3478_);
lean_dec(v_k_3477_);
v___x_3484_ = lean_unsigned_to_nat(1u);
v___x_3485_ = lean_nat_add(v___x_3484_, v_size_3475_);
v___x_3486_ = lean_nat_add(v___x_3485_, v_size_3476_);
lean_dec(v_size_3476_);
lean_dec(v___x_3485_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3474_);
lean_ctor_set(v___x_3293_, 0, v___x_3486_);
v___x_3488_ = v___x_3293_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_l_3290_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v___x_3474_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
else
{
lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3559_; 
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; lean_object* v_unused_3563_; lean_object* v_unused_3564_; 
v_unused_3560_ = lean_ctor_get(v___x_3474_, 4);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v___x_3474_, 3);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v___x_3474_, 2);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v___x_3474_, 1);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v___x_3474_, 0);
lean_dec(v_unused_3564_);
v___x_3491_ = v___x_3474_;
v_isShared_3492_ = v_isSharedCheck_3559_;
goto v_resetjp_3490_;
}
else
{
lean_dec(v___x_3474_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3559_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
if (lean_obj_tag(v_l_3479_) == 0)
{
if (lean_obj_tag(v_r_3480_) == 0)
{
lean_object* v_size_3493_; lean_object* v_k_3494_; lean_object* v_v_3495_; lean_object* v_l_3496_; lean_object* v_r_3497_; lean_object* v_size_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v_size_3493_ = lean_ctor_get(v_l_3479_, 0);
v_k_3494_ = lean_ctor_get(v_l_3479_, 1);
v_v_3495_ = lean_ctor_get(v_l_3479_, 2);
v_l_3496_ = lean_ctor_get(v_l_3479_, 3);
v_r_3497_ = lean_ctor_get(v_l_3479_, 4);
v_size_3498_ = lean_ctor_get(v_r_3480_, 0);
v___x_3499_ = lean_unsigned_to_nat(2u);
v___x_3500_ = lean_nat_mul(v___x_3499_, v_size_3498_);
v___x_3501_ = lean_nat_dec_lt(v_size_3493_, v___x_3500_);
lean_dec(v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3530_; 
lean_inc(v_r_3497_);
lean_inc(v_l_3496_);
lean_inc(v_v_3495_);
lean_inc(v_k_3494_);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_l_3479_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; lean_object* v_unused_3532_; lean_object* v_unused_3533_; lean_object* v_unused_3534_; lean_object* v_unused_3535_; 
v_unused_3531_ = lean_ctor_get(v_l_3479_, 4);
lean_dec(v_unused_3531_);
v_unused_3532_ = lean_ctor_get(v_l_3479_, 3);
lean_dec(v_unused_3532_);
v_unused_3533_ = lean_ctor_get(v_l_3479_, 2);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_l_3479_, 1);
lean_dec(v_unused_3534_);
v_unused_3535_ = lean_ctor_get(v_l_3479_, 0);
lean_dec(v_unused_3535_);
v___x_3503_ = v_l_3479_;
v_isShared_3504_ = v_isSharedCheck_3530_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v_l_3479_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3530_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3520_; 
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3506_ = lean_nat_add(v___x_3505_, v_size_3475_);
v___x_3507_ = lean_nat_add(v___x_3506_, v_size_3476_);
lean_dec(v_size_3476_);
if (lean_obj_tag(v_l_3496_) == 0)
{
lean_object* v_size_3528_; 
v_size_3528_ = lean_ctor_get(v_l_3496_, 0);
lean_inc(v_size_3528_);
v___y_3520_ = v_size_3528_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_unsigned_to_nat(0u);
v___y_3520_ = v___x_3529_;
goto v___jp_3519_;
}
v___jp_3508_:
{
lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3512_ = lean_nat_add(v___y_3509_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec(v___y_3509_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 4, v_r_3480_);
lean_ctor_set(v___x_3503_, 3, v_r_3497_);
lean_ctor_set(v___x_3503_, 2, v_v_3478_);
lean_ctor_set(v___x_3503_, 1, v_k_3477_);
lean_ctor_set(v___x_3503_, 0, v___x_3512_);
v___x_3514_ = v___x_3503_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_k_3477_);
lean_ctor_set(v_reuseFailAlloc_3518_, 2, v_v_3478_);
lean_ctor_set(v_reuseFailAlloc_3518_, 3, v_r_3497_);
lean_ctor_set(v_reuseFailAlloc_3518_, 4, v_r_3480_);
v___x_3514_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3516_; 
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 4, v___x_3514_);
lean_ctor_set(v___x_3491_, 3, v___y_3510_);
lean_ctor_set(v___x_3491_, 2, v_v_3495_);
lean_ctor_set(v___x_3491_, 1, v_k_3494_);
lean_ctor_set(v___x_3491_, 0, v___x_3507_);
v___x_3516_ = v___x_3491_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3507_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_k_3494_);
lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_v_3495_);
lean_ctor_set(v_reuseFailAlloc_3517_, 3, v___y_3510_);
lean_ctor_set(v_reuseFailAlloc_3517_, 4, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
v___jp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = lean_nat_add(v___x_3506_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec(v___x_3506_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v_l_3496_);
lean_ctor_set(v___x_3293_, 0, v___x_3521_);
v___x_3523_ = v___x_3293_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_l_3290_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_l_3496_);
v___x_3523_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_nat_add(v___x_3505_, v_size_3498_);
if (lean_obj_tag(v_r_3497_) == 0)
{
lean_object* v_size_3525_; 
v_size_3525_ = lean_ctor_get(v_r_3497_, 0);
lean_inc(v_size_3525_);
v___y_3509_ = v___x_3524_;
v___y_3510_ = v___x_3523_;
v___y_3511_ = v_size_3525_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3526_; 
v___x_3526_ = lean_unsigned_to_nat(0u);
v___y_3509_ = v___x_3524_;
v___y_3510_ = v___x_3523_;
v___y_3511_ = v___x_3526_;
goto v___jp_3508_;
}
}
}
}
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3541_; 
lean_del_object(v___x_3293_);
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = lean_nat_add(v___x_3536_, v_size_3475_);
v___x_3538_ = lean_nat_add(v___x_3537_, v_size_3476_);
lean_dec(v_size_3476_);
v___x_3539_ = lean_nat_add(v___x_3537_, v_size_3493_);
lean_dec(v___x_3537_);
lean_inc_ref(v_l_3290_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 4, v_l_3479_);
lean_ctor_set(v___x_3491_, 3, v_l_3290_);
lean_ctor_set(v___x_3491_, 2, v_v_3289_);
lean_ctor_set(v___x_3491_, 1, v_k_3288_);
lean_ctor_set(v___x_3491_, 0, v___x_3539_);
v___x_3541_ = v___x_3491_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3554_, 3, v_l_3290_);
lean_ctor_set(v_reuseFailAlloc_3554_, 4, v_l_3479_);
v___x_3541_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
v_isSharedCheck_3548_ = !lean_is_exclusive(v_l_3290_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; lean_object* v_unused_3550_; lean_object* v_unused_3551_; lean_object* v_unused_3552_; lean_object* v_unused_3553_; 
v_unused_3549_ = lean_ctor_get(v_l_3290_, 4);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_l_3290_, 3);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_l_3290_, 2);
lean_dec(v_unused_3551_);
v_unused_3552_ = lean_ctor_get(v_l_3290_, 1);
lean_dec(v_unused_3552_);
v_unused_3553_ = lean_ctor_get(v_l_3290_, 0);
lean_dec(v_unused_3553_);
v___x_3543_ = v_l_3290_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_dec(v_l_3290_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 4, v_r_3480_);
lean_ctor_set(v___x_3543_, 3, v___x_3541_);
lean_ctor_set(v___x_3543_, 2, v_v_3478_);
lean_ctor_set(v___x_3543_, 1, v_k_3477_);
lean_ctor_set(v___x_3543_, 0, v___x_3538_);
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_k_3477_);
lean_ctor_set(v_reuseFailAlloc_3547_, 2, v_v_3478_);
lean_ctor_set(v_reuseFailAlloc_3547_, 3, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3547_, 4, v_r_3480_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec_ref_known(v_l_3479_, 5);
lean_del_object(v___x_3491_);
lean_dec(v_v_3478_);
lean_dec(v_k_3477_);
lean_dec(v_size_3476_);
lean_dec_ref_known(v_l_3290_, 5);
lean_del_object(v___x_3293_);
lean_dec(v_v_3289_);
lean_dec(v_k_3288_);
v___x_3555_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__7);
v___x_3556_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3555_);
return v___x_3556_;
}
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_del_object(v___x_3491_);
lean_dec(v_r_3480_);
lean_dec(v_v_3478_);
lean_dec(v_k_3477_);
lean_dec(v_size_3476_);
lean_dec_ref_known(v_l_3290_, 5);
lean_del_object(v___x_3293_);
lean_dec(v_v_3289_);
lean_dec(v_k_3288_);
v___x_3557_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg___closed__8);
v___x_3558_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v___x_3557_);
return v___x_3558_;
}
}
}
}
else
{
lean_object* v_size_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v_size_3565_ = lean_ctor_get(v_l_3290_, 0);
v___x_3566_ = lean_unsigned_to_nat(1u);
v___x_3567_ = lean_nat_add(v___x_3566_, v_size_3565_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3474_);
lean_ctor_set(v___x_3293_, 0, v___x_3567_);
v___x_3569_ = v___x_3293_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_l_3290_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v___x_3474_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
else
{
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_l_3571_; 
v_l_3571_ = lean_ctor_get(v___x_3474_, 3);
lean_inc(v_l_3571_);
if (lean_obj_tag(v_l_3571_) == 0)
{
lean_object* v_r_3572_; 
v_r_3572_ = lean_ctor_get(v___x_3474_, 4);
lean_inc(v_r_3572_);
if (lean_obj_tag(v_r_3572_) == 0)
{
lean_object* v_size_3573_; lean_object* v_k_3574_; lean_object* v_v_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3589_; 
v_size_3573_ = lean_ctor_get(v___x_3474_, 0);
v_k_3574_ = lean_ctor_get(v___x_3474_, 1);
v_v_3575_ = lean_ctor_get(v___x_3474_, 2);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; lean_object* v_unused_3591_; 
v_unused_3590_ = lean_ctor_get(v___x_3474_, 4);
lean_dec(v_unused_3590_);
v_unused_3591_ = lean_ctor_get(v___x_3474_, 3);
lean_dec(v_unused_3591_);
v___x_3577_ = v___x_3474_;
v_isShared_3578_ = v_isSharedCheck_3589_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_v_3575_);
lean_inc(v_k_3574_);
lean_inc(v_size_3573_);
lean_dec(v___x_3474_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3589_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v_size_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v_size_3579_ = lean_ctor_get(v_l_3571_, 0);
v___x_3580_ = lean_unsigned_to_nat(1u);
v___x_3581_ = lean_nat_add(v___x_3580_, v_size_3573_);
lean_dec(v_size_3573_);
v___x_3582_ = lean_nat_add(v___x_3580_, v_size_3579_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 4, v_l_3571_);
lean_ctor_set(v___x_3577_, 3, v_l_3290_);
lean_ctor_set(v___x_3577_, 2, v_v_3289_);
lean_ctor_set(v___x_3577_, 1, v_k_3288_);
lean_ctor_set(v___x_3577_, 0, v___x_3582_);
v___x_3584_ = v___x_3577_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_l_3290_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_l_3571_);
v___x_3584_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3586_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v_r_3572_);
lean_ctor_set(v___x_3293_, 3, v___x_3584_);
lean_ctor_set(v___x_3293_, 2, v_v_3575_);
lean_ctor_set(v___x_3293_, 1, v_k_3574_);
lean_ctor_set(v___x_3293_, 0, v___x_3581_);
v___x_3586_ = v___x_3293_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3574_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3575_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_r_3572_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v_k_3592_; lean_object* v_v_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3617_; 
v_k_3592_ = lean_ctor_get(v___x_3474_, 1);
v_v_3593_ = lean_ctor_get(v___x_3474_, 2);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; lean_object* v_unused_3619_; lean_object* v_unused_3620_; 
v_unused_3618_ = lean_ctor_get(v___x_3474_, 4);
lean_dec(v_unused_3618_);
v_unused_3619_ = lean_ctor_get(v___x_3474_, 3);
lean_dec(v_unused_3619_);
v_unused_3620_ = lean_ctor_get(v___x_3474_, 0);
lean_dec(v_unused_3620_);
v___x_3595_ = v___x_3474_;
v_isShared_3596_ = v_isSharedCheck_3617_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_v_3593_);
lean_inc(v_k_3592_);
lean_dec(v___x_3474_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3617_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v_k_3597_; lean_object* v_v_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3613_; 
v_k_3597_ = lean_ctor_get(v_l_3571_, 1);
v_v_3598_ = lean_ctor_get(v_l_3571_, 2);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_l_3571_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; lean_object* v_unused_3615_; lean_object* v_unused_3616_; 
v_unused_3614_ = lean_ctor_get(v_l_3571_, 4);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_l_3571_, 3);
lean_dec(v_unused_3615_);
v_unused_3616_ = lean_ctor_get(v_l_3571_, 0);
lean_dec(v_unused_3616_);
v___x_3600_ = v_l_3571_;
v_isShared_3601_ = v_isSharedCheck_3613_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_v_3598_);
lean_inc(v_k_3597_);
lean_dec(v_l_3571_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3613_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3602_ = lean_unsigned_to_nat(3u);
v___x_3603_ = lean_unsigned_to_nat(1u);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 4, v_r_3572_);
lean_ctor_set(v___x_3600_, 3, v_r_3572_);
lean_ctor_set(v___x_3600_, 2, v_v_3289_);
lean_ctor_set(v___x_3600_, 1, v_k_3288_);
lean_ctor_set(v___x_3600_, 0, v___x_3603_);
v___x_3605_ = v___x_3600_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_r_3572_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_r_3572_);
v___x_3605_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 3, v_r_3572_);
lean_ctor_set(v___x_3595_, 0, v___x_3603_);
v___x_3607_ = v___x_3595_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_k_3592_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_v_3593_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_r_3572_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_r_3572_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3607_);
lean_ctor_set(v___x_3293_, 3, v___x_3605_);
lean_ctor_set(v___x_3293_, 2, v_v_3598_);
lean_ctor_set(v___x_3293_, 1, v_k_3597_);
lean_ctor_set(v___x_3293_, 0, v___x_3602_);
v___x_3609_ = v___x_3293_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3597_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3598_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v___x_3605_);
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
}
}
else
{
lean_object* v_r_3621_; 
v_r_3621_ = lean_ctor_get(v___x_3474_, 4);
lean_inc(v_r_3621_);
if (lean_obj_tag(v_r_3621_) == 0)
{
lean_object* v_k_3622_; lean_object* v_v_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3635_; 
v_k_3622_ = lean_ctor_get(v___x_3474_, 1);
v_v_3623_ = lean_ctor_get(v___x_3474_, 2);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3635_ == 0)
{
lean_object* v_unused_3636_; lean_object* v_unused_3637_; lean_object* v_unused_3638_; 
v_unused_3636_ = lean_ctor_get(v___x_3474_, 4);
lean_dec(v_unused_3636_);
v_unused_3637_ = lean_ctor_get(v___x_3474_, 3);
lean_dec(v_unused_3637_);
v_unused_3638_ = lean_ctor_get(v___x_3474_, 0);
lean_dec(v_unused_3638_);
v___x_3625_ = v___x_3474_;
v_isShared_3626_ = v_isSharedCheck_3635_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_v_3623_);
lean_inc(v_k_3622_);
lean_dec(v___x_3474_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3635_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3627_ = lean_unsigned_to_nat(3u);
v___x_3628_ = lean_unsigned_to_nat(1u);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 4, v_l_3571_);
lean_ctor_set(v___x_3625_, 2, v_v_3289_);
lean_ctor_set(v___x_3625_, 1, v_k_3288_);
lean_ctor_set(v___x_3625_, 0, v___x_3628_);
v___x_3630_ = v___x_3625_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v_l_3571_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v_l_3571_);
v___x_3630_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3632_; 
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v_r_3621_);
lean_ctor_set(v___x_3293_, 3, v___x_3630_);
lean_ctor_set(v___x_3293_, 2, v_v_3623_);
lean_ctor_set(v___x_3293_, 1, v_k_3622_);
lean_ctor_set(v___x_3293_, 0, v___x_3627_);
v___x_3632_ = v___x_3293_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_k_3622_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_v_3623_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v_r_3621_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = lean_unsigned_to_nat(2u);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3474_);
lean_ctor_set(v___x_3293_, 3, v_r_3621_);
lean_ctor_set(v___x_3293_, 0, v___x_3639_);
v___x_3641_ = v___x_3293_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3642_, 3, v_r_3621_);
lean_ctor_set(v_reuseFailAlloc_3642_, 4, v___x_3474_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
v___x_3643_ = lean_unsigned_to_nat(1u);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 4, v___x_3474_);
lean_ctor_set(v___x_3293_, 3, v___x_3474_);
lean_ctor_set(v___x_3293_, 0, v___x_3643_);
v___x_3645_ = v___x_3293_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_k_3288_);
lean_ctor_set(v_reuseFailAlloc_3646_, 2, v_v_3289_);
lean_ctor_set(v_reuseFailAlloc_3646_, 3, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3646_, 4, v___x_3474_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
lean_ctor_set(v___x_3649_, 1, v_k_3284_);
lean_ctor_set(v___x_3649_, 2, v_v_3285_);
lean_ctor_set(v___x_3649_, 3, v_t_3286_);
lean_ctor_set(v___x_3649_, 4, v_t_3286_);
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(lean_object* v_init_3650_, lean_object* v_x_3651_){
_start:
{
if (lean_obj_tag(v_x_3651_) == 0)
{
lean_object* v_k_3652_; lean_object* v_v_3653_; lean_object* v_l_3654_; lean_object* v_r_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v_k_3652_ = lean_ctor_get(v_x_3651_, 1);
lean_inc(v_k_3652_);
v_v_3653_ = lean_ctor_get(v_x_3651_, 2);
lean_inc(v_v_3653_);
v_l_3654_ = lean_ctor_get(v_x_3651_, 3);
lean_inc(v_l_3654_);
v_r_3655_ = lean_ctor_get(v_x_3651_, 4);
lean_inc(v_r_3655_);
lean_dec_ref_known(v_x_3651_, 5);
v___x_3656_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_3650_, v_l_3654_);
v___x_3657_ = 1;
v___x_3658_ = l_Lean_Name_toString(v_k_3652_, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3659_, 0, v_v_3653_);
v___x_3660_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v___x_3658_, v___x_3659_, v___x_3656_);
v_init_3650_ = v___x_3660_;
v_x_3651_ = v_r_3655_;
goto _start;
}
else
{
return v_init_3650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3662_){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_box(1);
v___x_3664_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v___x_3663_, v_m_3662_);
v___x_3665_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3668_, uint8_t v_updateToolchain_3669_, lean_object* v_ws_3670_, lean_object* v_dep_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_baseName_3675_; lean_object* v_name_3676_; lean_object* v_opts_3677_; uint8_t v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v_baseName_3675_ = lean_ctor_get(v___x_3668_, 1);
v_name_3676_ = lean_ctor_get(v_dep_3671_, 0);
v_opts_3677_ = lean_ctor_get(v_dep_3671_, 4);
v___x_3678_ = 0;
lean_inc(v_baseName_3675_);
v___x_3679_ = l_Lean_Name_toString(v_baseName_3675_, v___x_3678_);
v___x_3680_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3681_ = lean_string_append(v___x_3679_, v___x_3680_);
lean_inc(v_name_3676_);
v___x_3682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3676_, v_updateToolchain_3669_);
v___x_3683_ = lean_string_append(v___x_3681_, v___x_3682_);
lean_dec_ref(v___x_3682_);
v___x_3684_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3685_ = lean_string_append(v___x_3683_, v___x_3684_);
lean_inc(v_opts_3677_);
v___x_3686_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3677_);
v___x_3687_ = lean_unsigned_to_nat(80u);
v___x_3688_ = l_Lean_Json_pretty(v___x_3686_, v___x_3687_);
v___x_3689_ = lean_string_append(v___x_3685_, v___x_3688_);
lean_dec_ref(v___x_3688_);
v___x_3690_ = 0;
v___x_3691_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3691_, 0, v___x_3689_);
lean_ctor_set_uint8(v___x_3691_, sizeof(void*)*1, v___x_3690_);
lean_inc_ref(v___y_3673_);
v___x_3692_ = lean_apply_2(v___y_3673_, v___x_3691_, lean_box(0));
v___x_3693_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3670_, v___x_3668_, v_dep_3671_, v___y_3672_, v___y_3673_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3694_, lean_object* v_updateToolchain_3695_, lean_object* v_ws_3696_, lean_object* v_dep_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
uint8_t v_updateToolchain_boxed_3701_; lean_object* v_res_3702_; 
v_updateToolchain_boxed_3701_ = lean_unbox(v_updateToolchain_3695_);
v_res_3702_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3694_, v_updateToolchain_boxed_3701_, v_ws_3696_, v_dep_3697_, v___y_3698_, v___y_3699_);
lean_dec_ref(v___y_3699_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_a_3703_, lean_object* v_b_3704_){
_start:
{
lean_object* v_next_3705_; 
v_next_3705_ = lean_ctor_get(v_a_3703_, 0);
lean_inc(v_next_3705_);
if (lean_obj_tag(v_next_3705_) == 0)
{
lean_dec_ref(v_a_3703_);
return v_b_3704_;
}
else
{
lean_object* v_upperBound_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3726_; 
v_upperBound_3706_ = lean_ctor_get(v_a_3703_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_a_3703_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; 
v_unused_3727_ = lean_ctor_get(v_a_3703_, 0);
lean_dec(v_unused_3727_);
v___x_3708_ = v_a_3703_;
v_isShared_3709_ = v_isSharedCheck_3726_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_upperBound_3706_);
lean_dec(v_a_3703_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3726_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v_val_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3725_; 
v_val_3710_ = lean_ctor_get(v_next_3705_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_next_3705_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3712_ = v_next_3705_;
v_isShared_3713_ = v_isSharedCheck_3725_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_val_3710_);
lean_dec(v_next_3705_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3725_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
uint8_t v___x_3714_; 
v___x_3714_ = lean_nat_dec_lt(v_val_3710_, v_upperBound_3706_);
if (v___x_3714_ == 0)
{
lean_del_object(v___x_3712_);
lean_dec(v_val_3710_);
lean_del_object(v___x_3708_);
lean_dec(v_upperBound_3706_);
return v_b_3704_;
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
v___x_3715_ = lean_unsigned_to_nat(1u);
v___x_3716_ = lean_nat_add(v_val_3710_, v___x_3715_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3716_);
v___x_3718_ = v___x_3712_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3720_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3718_);
v___x_3720_ = v___x_3708_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_upperBound_3706_);
v___x_3720_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_array_push(v_b_3704_, v_val_3710_);
v_a_3703_ = v___x_3720_;
v_b_3704_ = v___x_3721_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3728_, lean_object* v_f_3729_, lean_object* v_xs_3730_, lean_object* v_k_3731_, lean_object* v_acc_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_nat_dec_lt(v_k_3731_, v_n_3728_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_dec(v_k_3731_);
lean_dec_ref(v_f_3729_);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v_acc_3732_);
lean_ctor_set(v___x_3737_, 1, v___y_3733_);
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
return v___x_3738_;
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_array_fget_borrowed(v_xs_3730_, v_k_3731_);
lean_inc_ref(v_f_3729_);
lean_inc_ref(v___y_3734_);
lean_inc(v___x_3739_);
v___x_3740_ = lean_apply_4(v_f_3729_, v___x_3739_, v___y_3733_, v___y_3734_, lean_box(0));
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v_fst_3742_; lean_object* v_snd_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v_fst_3742_ = lean_ctor_get(v_a_3741_, 0);
lean_inc(v_fst_3742_);
v_snd_3743_ = lean_ctor_get(v_a_3741_, 1);
lean_inc(v_snd_3743_);
lean_dec(v_a_3741_);
v___x_3744_ = lean_unsigned_to_nat(1u);
v___x_3745_ = lean_nat_add(v_k_3731_, v___x_3744_);
lean_dec(v_k_3731_);
v___x_3746_ = lean_array_push(v_acc_3732_, v_fst_3742_);
v_k_3731_ = v___x_3745_;
v_acc_3732_ = v___x_3746_;
v___y_3733_ = v_snd_3743_;
goto _start;
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec_ref(v_acc_3732_);
lean_dec(v_k_3731_);
lean_dec_ref(v_f_3729_);
v_a_3748_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3740_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3740_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_3756_, lean_object* v_f_3757_, lean_object* v_xs_3758_, lean_object* v_k_3759_, lean_object* v_acc_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_3756_, v_f_3757_, v_xs_3758_, v_k_3759_, v_acc_3760_, v___y_3761_, v___y_3762_);
lean_dec_ref(v___y_3762_);
lean_dec_ref(v_xs_3758_);
lean_dec(v_n_3756_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_3765_, lean_object* v_fst_3766_, lean_object* v___x_3767_, lean_object* v_leanOpts_3768_, lean_object* v_a_3769_, lean_object* v_b_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
uint8_t v___x_3777_; 
v___x_3777_ = lean_nat_dec_lt(v_a_3769_, v_upperBound_3765_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_dec(v_a_3769_);
lean_dec_ref(v_leanOpts_3768_);
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v_b_3770_);
lean_ctor_set(v___x_3778_, 1, v___y_3771_);
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
return v___x_3779_;
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = lean_array_fget_borrowed(v_fst_3766_, v_a_3769_);
lean_inc(v___x_3780_);
v___x_3781_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_3780_, v___y_3771_, v___y_3772_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3856_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3856_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3856_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v_snd_3786_; lean_object* v___x_3787_; lean_object* v_opts_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_snd_3786_ = lean_ctor_get(v_a_3782_, 1);
lean_inc(v_snd_3786_);
lean_dec(v_a_3782_);
v___x_3787_ = lean_array_fget_borrowed(v___x_3767_, v_a_3769_);
v_opts_3788_ = lean_ctor_get(v___x_3787_, 4);
v___x_3789_ = lean_unsigned_to_nat(0u);
v___x_3790_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3768_);
lean_inc(v_opts_3788_);
lean_inc(v___x_3780_);
v___x_3791_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_3770_, v___x_3780_, v_opts_3788_, v_leanOpts_3768_, v___x_3777_, v___x_3790_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v_a_3793_; lean_object* v_snd_3795_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
lean_del_object(v___x_3784_);
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
v_a_3793_ = lean_ctor_get(v___x_3791_, 1);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3791_, 2);
v___x_3799_ = lean_array_get_size(v_a_3793_);
v___x_3800_ = lean_nat_dec_lt(v___x_3789_, v___x_3799_);
if (v___x_3800_ == 0)
{
lean_dec(v_a_3793_);
v_snd_3795_ = v_snd_3786_;
goto v___jp_3794_;
}
else
{
lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3801_ = lean_box(0);
v___x_3802_ = lean_nat_dec_le(v___x_3799_, v___x_3799_);
if (v___x_3802_ == 0)
{
if (v___x_3800_ == 0)
{
lean_dec(v_a_3793_);
v_snd_3795_ = v_snd_3786_;
goto v___jp_3794_;
}
else
{
size_t v___x_3803_; size_t v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = ((size_t)0ULL);
v___x_3804_ = lean_usize_of_nat(v___x_3799_);
v___x_3805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3793_, v___x_3803_, v___x_3804_, v___x_3801_, v___y_3772_);
lean_dec(v_a_3793_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_dec_ref_known(v___x_3805_, 1);
v_snd_3795_ = v_snd_3786_;
goto v___jp_3794_;
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_a_3792_);
lean_dec(v_snd_3786_);
lean_dec(v_a_3769_);
lean_dec_ref(v_leanOpts_3768_);
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
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
else
{
size_t v___x_3814_; size_t v___x_3815_; lean_object* v___x_3816_; 
v___x_3814_ = ((size_t)0ULL);
v___x_3815_ = lean_usize_of_nat(v___x_3799_);
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3793_, v___x_3814_, v___x_3815_, v___x_3801_, v___y_3772_);
lean_dec(v_a_3793_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_dec_ref_known(v___x_3816_, 1);
v_snd_3795_ = v_snd_3786_;
goto v___jp_3794_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec(v_a_3792_);
lean_dec(v_snd_3786_);
lean_dec(v_a_3769_);
lean_dec_ref(v_leanOpts_3768_);
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
v___jp_3794_:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = lean_unsigned_to_nat(1u);
v___x_3797_ = lean_nat_add(v_a_3769_, v___x_3796_);
lean_dec(v_a_3769_);
v_a_3769_ = v___x_3797_;
v_b_3770_ = v_a_3792_;
v___y_3771_ = v_snd_3795_;
goto _start;
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
lean_dec(v_snd_3786_);
lean_dec(v_a_3769_);
lean_dec_ref(v_leanOpts_3768_);
v_a_3825_ = lean_ctor_get(v___x_3791_, 1);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3791_, 2);
v___x_3826_ = lean_array_get_size(v_a_3825_);
v___x_3827_ = lean_nat_dec_lt(v___x_3789_, v___x_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
lean_dec(v_a_3825_);
v___x_3828_ = lean_box(0);
if (v_isShared_3785_ == 0)
{
lean_ctor_set_tag(v___x_3784_, 1);
lean_ctor_set(v___x_3784_, 0, v___x_3828_);
v___x_3830_ = v___x_3784_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
else
{
lean_object* v___x_3832_; uint8_t v___x_3833_; 
lean_del_object(v___x_3784_);
v___x_3832_ = lean_box(0);
v___x_3833_ = lean_nat_dec_le(v___x_3826_, v___x_3826_);
if (v___x_3833_ == 0)
{
if (v___x_3827_ == 0)
{
lean_dec(v_a_3825_);
goto v___jp_3774_;
}
else
{
size_t v___x_3834_; size_t v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = ((size_t)0ULL);
v___x_3835_ = lean_usize_of_nat(v___x_3826_);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3825_, v___x_3834_, v___x_3835_, v___x_3832_, v___y_3772_);
lean_dec(v_a_3825_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_dec_ref_known(v___x_3836_, 1);
goto v___jp_3774_;
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
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
else
{
size_t v___x_3845_; size_t v___x_3846_; lean_object* v___x_3847_; 
v___x_3845_ = ((size_t)0ULL);
v___x_3846_ = lean_usize_of_nat(v___x_3826_);
v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3825_, v___x_3845_, v___x_3846_, v___x_3832_, v___y_3772_);
lean_dec(v_a_3825_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_dec_ref_known(v___x_3847_, 1);
goto v___jp_3774_;
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3847_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
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
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec_ref(v_b_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_leanOpts_3768_);
v_a_3857_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3781_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3781_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
v___jp_3774_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = lean_box(0);
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
return v___x_3776_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_3865_, lean_object* v_fst_3866_, lean_object* v___x_3867_, lean_object* v_leanOpts_3868_, lean_object* v_a_3869_, lean_object* v_b_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_3865_, v_fst_3866_, v___x_3867_, v_leanOpts_3868_, v_a_3869_, v_b_3870_, v___y_3871_, v___y_3872_);
lean_dec_ref(v___y_3872_);
lean_dec_ref(v___x_3867_);
lean_dec_ref(v_fst_3866_);
lean_dec(v_upperBound_3865_);
return v_res_3874_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(lean_object* v___x_3875_, lean_object* v_x_3876_){
_start:
{
lean_object* v_baseName_3877_; lean_object* v_name_3878_; uint8_t v___x_3879_; 
v_baseName_3877_ = lean_ctor_get(v_x_3876_, 1);
v_name_3878_ = lean_ctor_get(v___x_3875_, 0);
v___x_3879_ = lean_name_eq(v_baseName_3877_, v_name_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed(lean_object* v___x_3880_, lean_object* v_x_3881_){
_start:
{
uint8_t v_res_3882_; lean_object* v_r_3883_; 
v_res_3882_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0(v___x_3880_, v_x_3881_);
lean_dec_ref(v_x_3881_);
lean_dec_ref(v___x_3880_);
v_r_3883_ = lean_box(v_res_3882_);
return v_r_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(lean_object* v_pkg_3884_, lean_object* v_leanOpts_3885_, uint8_t v_reconfigure_3886_, lean_object* v_as_3887_, size_t v_i_3888_, size_t v_stop_3889_, lean_object* v_b_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v___x_3897_; 
v___x_3897_ = lean_usize_dec_eq(v_i_3888_, v_stop_3889_);
if (v___x_3897_ == 0)
{
lean_object* v_ws_3898_; lean_object* v_depIdxs_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_4014_; 
v_ws_3898_ = lean_ctor_get(v_b_3890_, 0);
v_depIdxs_3899_ = lean_ctor_get(v_b_3890_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v_b_3890_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_3901_ = v_b_3890_;
v_isShared_3902_ = v_isSharedCheck_4014_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_depIdxs_3899_);
lean_inc(v_ws_3898_);
lean_dec(v_b_3890_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_4014_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_packages_3903_; size_t v___x_3904_; size_t v___x_3905_; lean_object* v___x_3906_; lean_object* v___f_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_packages_3903_ = lean_ctor_get(v_ws_3898_, 4);
v___x_3904_ = ((size_t)1ULL);
v___x_3905_ = lean_usize_sub(v_i_3888_, v___x_3904_);
v___x_3906_ = lean_array_uget_borrowed(v_as_3887_, v___x_3905_);
lean_inc(v___x_3906_);
v___f_3907_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3907_, 0, v___x_3906_);
v___x_3908_ = lean_unsigned_to_nat(0u);
v___x_3909_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3907_, v_packages_3903_, v___x_3908_);
if (lean_obj_tag(v___x_3909_) == 1)
{
lean_object* v_val_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v_val_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_val_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = lean_array_push(v_depIdxs_3899_, v_val_3910_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v___x_3911_);
v___x_3913_ = v___x_3901_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_ws_3898_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
v_i_3888_ = v___x_3905_;
v_b_3890_ = v___x_3913_;
goto _start;
}
}
else
{
lean_object* v_baseName_3916_; lean_object* v_name_3917_; lean_object* v_opts_3918_; uint8_t v___x_3919_; 
lean_inc_ref(v_packages_3903_);
lean_dec(v___x_3909_);
v_baseName_3916_ = lean_ctor_get(v_pkg_3884_, 1);
v_name_3917_ = lean_ctor_get(v___x_3906_, 0);
v_opts_3918_ = lean_ctor_get(v___x_3906_, 4);
v___x_3919_ = lean_name_eq(v_baseName_3916_, v_name_3917_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; 
lean_inc_ref(v___y_3892_);
lean_inc_ref(v_ws_3898_);
lean_inc(v___x_3906_);
lean_inc_ref(v_pkg_3884_);
v___x_3920_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_3884_, v___x_3906_, v_ws_3898_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3997_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3997_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3997_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v_fst_3925_; lean_object* v_snd_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_fst_3925_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_fst_3925_);
v_snd_3926_ = lean_ctor_get(v_a_3921_, 1);
lean_inc(v_snd_3926_);
lean_dec(v_a_3921_);
v___x_3927_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3885_);
lean_inc(v_opts_3918_);
v___x_3928_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_3898_, v_fst_3925_, v_opts_3918_, v_leanOpts_3885_, v_reconfigure_3886_, v___x_3927_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v_a_3930_; lean_object* v_wsIdx_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_del_object(v___x_3923_);
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
v_a_3930_ = lean_ctor_get(v___x_3928_, 1);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3928_, 2);
v_wsIdx_3931_ = lean_array_get_size(v_packages_3903_);
lean_dec_ref(v_packages_3903_);
v___x_3932_ = lean_array_push(v_depIdxs_3899_, v_wsIdx_3931_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 1, v___x_3932_);
lean_ctor_set(v___x_3901_, 0, v_a_3929_);
v___x_3934_ = v___x_3901_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3929_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = lean_array_get_size(v_a_3930_);
v___x_3936_ = lean_nat_dec_lt(v___x_3908_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_dec(v_a_3930_);
v_i_3888_ = v___x_3905_;
v_b_3890_ = v___x_3934_;
v___y_3891_ = v_snd_3926_;
goto _start;
}
else
{
lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3938_ = lean_box(0);
v___x_3939_ = lean_nat_dec_le(v___x_3935_, v___x_3935_);
if (v___x_3939_ == 0)
{
if (v___x_3936_ == 0)
{
lean_dec(v_a_3930_);
v_i_3888_ = v___x_3905_;
v_b_3890_ = v___x_3934_;
v___y_3891_ = v_snd_3926_;
goto _start;
}
else
{
size_t v___x_3941_; size_t v___x_3942_; lean_object* v___x_3943_; 
v___x_3941_ = ((size_t)0ULL);
v___x_3942_ = lean_usize_of_nat(v___x_3935_);
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3930_, v___x_3941_, v___x_3942_, v___x_3938_, v___y_3892_);
lean_dec(v_a_3930_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_dec_ref_known(v___x_3943_, 1);
v_i_3888_ = v___x_3905_;
v_b_3890_ = v___x_3934_;
v___y_3891_ = v_snd_3926_;
goto _start;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v___x_3934_);
lean_dec(v_snd_3926_);
lean_dec_ref(v_leanOpts_3885_);
lean_dec_ref(v_pkg_3884_);
v_a_3945_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3943_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3943_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
else
{
size_t v___x_3953_; size_t v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = ((size_t)0ULL);
v___x_3954_ = lean_usize_of_nat(v___x_3935_);
v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3930_, v___x_3953_, v___x_3954_, v___x_3938_, v___y_3892_);
lean_dec(v_a_3930_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_dec_ref_known(v___x_3955_, 1);
v_i_3888_ = v___x_3905_;
v_b_3890_ = v___x_3934_;
v___y_3891_ = v_snd_3926_;
goto _start;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v___x_3934_);
lean_dec(v_snd_3926_);
lean_dec_ref(v_leanOpts_3885_);
lean_dec_ref(v_pkg_3884_);
v_a_3957_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3955_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3955_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
lean_dec(v_snd_3926_);
lean_dec_ref(v_packages_3903_);
lean_del_object(v___x_3901_);
lean_dec_ref(v_depIdxs_3899_);
lean_dec_ref(v_leanOpts_3885_);
lean_dec_ref(v_pkg_3884_);
v_a_3966_ = lean_ctor_get(v___x_3928_, 1);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3928_, 2);
v___x_3967_ = lean_array_get_size(v_a_3966_);
v___x_3968_ = lean_nat_dec_lt(v___x_3908_, v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3971_; 
lean_dec(v_a_3966_);
v___x_3969_ = lean_box(0);
if (v_isShared_3924_ == 0)
{
lean_ctor_set_tag(v___x_3923_, 1);
lean_ctor_set(v___x_3923_, 0, v___x_3969_);
v___x_3971_ = v___x_3923_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3969_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
else
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
lean_del_object(v___x_3923_);
v___x_3973_ = lean_box(0);
v___x_3974_ = lean_nat_dec_le(v___x_3967_, v___x_3967_);
if (v___x_3974_ == 0)
{
if (v___x_3968_ == 0)
{
lean_dec(v_a_3966_);
goto v___jp_3894_;
}
else
{
size_t v___x_3975_; size_t v___x_3976_; lean_object* v___x_3977_; 
v___x_3975_ = ((size_t)0ULL);
v___x_3976_ = lean_usize_of_nat(v___x_3967_);
v___x_3977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3966_, v___x_3975_, v___x_3976_, v___x_3973_, v___y_3892_);
lean_dec(v_a_3966_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_dec_ref_known(v___x_3977_, 1);
goto v___jp_3894_;
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3977_);
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
}
else
{
size_t v___x_3986_; size_t v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = ((size_t)0ULL);
v___x_3987_ = lean_usize_of_nat(v___x_3967_);
v___x_3988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3966_, v___x_3986_, v___x_3987_, v___x_3973_, v___y_3892_);
lean_dec(v_a_3966_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_dec_ref_known(v___x_3988_, 1);
goto v___jp_3894_;
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3988_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3988_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
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
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec_ref(v_packages_3903_);
lean_del_object(v___x_3901_);
lean_dec_ref(v_depIdxs_3899_);
lean_dec_ref(v_ws_3898_);
lean_dec_ref(v_leanOpts_3885_);
lean_dec_ref(v_pkg_3884_);
v_a_3998_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3920_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3920_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_inc(v_baseName_3916_);
lean_dec_ref(v_packages_3903_);
lean_del_object(v___x_3901_);
lean_dec_ref(v_depIdxs_3899_);
lean_dec_ref(v_ws_3898_);
lean_dec(v___y_3891_);
lean_dec_ref(v_leanOpts_3885_);
lean_dec_ref(v_pkg_3884_);
v___x_4006_ = l_Lean_Name_toString(v_baseName_3916_, v___x_3897_);
v___x_4007_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_4008_ = lean_string_append(v___x_4006_, v___x_4007_);
v___x_4009_ = 3;
v___x_4010_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4010_, 0, v___x_4008_);
lean_ctor_set_uint8(v___x_4010_, sizeof(void*)*1, v___x_4009_);
lean_inc_ref(v___y_3892_);
v___x_4011_ = lean_apply_2(v___y_3892_, v___x_4010_, lean_box(0));
v___x_4012_ = lean_box(0);
v___x_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
return v___x_4013_;
}
}
}
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec_ref(v_leanOpts_3885_);
lean_dec_ref(v_pkg_3884_);
v___x_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4015_, 0, v_b_3890_);
lean_ctor_set(v___x_4015_, 1, v___y_3891_);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
v___jp_3894_:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = lean_box(0);
v___x_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
return v___x_3896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___boxed(lean_object* v_pkg_4017_, lean_object* v_leanOpts_4018_, lean_object* v_reconfigure_4019_, lean_object* v_as_4020_, lean_object* v_i_4021_, lean_object* v_stop_4022_, lean_object* v_b_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
uint8_t v_reconfigure_boxed_4027_; size_t v_i_boxed_4028_; size_t v_stop_boxed_4029_; lean_object* v_res_4030_; 
v_reconfigure_boxed_4027_ = lean_unbox(v_reconfigure_4019_);
v_i_boxed_4028_ = lean_unbox_usize(v_i_4021_);
lean_dec(v_i_4021_);
v_stop_boxed_4029_ = lean_unbox_usize(v_stop_4022_);
lean_dec(v_stop_4022_);
v_res_4030_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4017_, v_leanOpts_4018_, v_reconfigure_boxed_4027_, v_as_4020_, v_i_boxed_4028_, v_stop_boxed_4029_, v_b_4023_, v___y_4024_, v___y_4025_);
lean_dec_ref(v___y_4025_);
lean_dec_ref(v_as_4020_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_4031_, uint8_t v_reconfigure_4032_, lean_object* v_ws_4033_, lean_object* v_i_4034_, lean_object* v_next_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_packages_4039_; lean_object* v_pkg_4040_; lean_object* v_ws_4042_; lean_object* v_depIdxs_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v_____x_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v_depConfigs_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v_s_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_packages_4039_ = lean_ctor_get(v_ws_4033_, 4);
v_pkg_4040_ = lean_array_fget(v_packages_4039_, v_i_4034_);
lean_dec(v_i_4034_);
v_depConfigs_4061_ = lean_ctor_get(v_pkg_4040_, 12);
v___x_4062_ = lean_array_get_size(v_depConfigs_4061_);
v___x_4063_ = lean_mk_empty_array_with_capacity(v___x_4062_);
lean_inc_ref(v___x_4063_);
lean_inc_ref(v_ws_4033_);
v_s_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_4064_, 0, v_ws_4033_);
lean_ctor_set(v_s_4064_, 1, v___x_4063_);
v___x_4065_ = lean_unsigned_to_nat(0u);
v___x_4066_ = lean_nat_dec_le(v___x_4062_, v___x_4062_);
if (v___x_4066_ == 0)
{
uint8_t v___x_4067_; 
v___x_4067_ = lean_nat_dec_lt(v___x_4065_, v___x_4062_);
if (v___x_4067_ == 0)
{
lean_object* v_ws_4068_; lean_object* v_packages_4069_; lean_object* v___x_4070_; uint8_t v___x_4071_; 
lean_dec_ref_known(v_s_4064_, 2);
v_ws_4068_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4033_, v_pkg_4040_, v___x_4063_);
v_packages_4069_ = lean_ctor_get(v_ws_4068_, 4);
lean_inc_ref(v_packages_4069_);
v___x_4070_ = lean_array_get_size(v_packages_4069_);
lean_dec_ref(v_packages_4069_);
v___x_4071_ = lean_nat_dec_lt(v_next_4035_, v___x_4070_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec(v_next_4035_);
lean_dec_ref(v_leanOpts_4031_);
v___x_4072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4072_, 0, v_ws_4068_);
lean_ctor_set(v___x_4072_, 1, v___y_4036_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = lean_unsigned_to_nat(1u);
v___x_4075_ = lean_nat_add(v_next_4035_, v___x_4074_);
v_ws_4033_ = v_ws_4068_;
v_i_4034_ = v_next_4035_;
v_next_4035_ = v___x_4075_;
goto _start;
}
}
else
{
size_t v___x_4077_; size_t v___x_4078_; lean_object* v___x_4079_; 
lean_dec_ref(v___x_4063_);
lean_dec_ref(v_ws_4033_);
v___x_4077_ = lean_usize_of_nat(v___x_4062_);
v___x_4078_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4031_);
lean_inc(v_pkg_4040_);
v___x_4079_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4040_, v_leanOpts_4031_, v_reconfigure_4032_, v_depConfigs_4061_, v___x_4077_, v___x_4078_, v_s_4064_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v_fst_4081_; lean_object* v_snd_4082_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v_fst_4081_ = lean_ctor_get(v_a_4080_, 0);
lean_inc(v_fst_4081_);
v_snd_4082_ = lean_ctor_get(v_a_4080_, 1);
lean_inc(v_snd_4082_);
lean_dec(v_a_4080_);
v_____x_4056_ = v_fst_4081_;
v___y_4057_ = v_snd_4082_;
v___y_4058_ = v___y_4037_;
goto v___jp_4055_;
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec(v_pkg_4040_);
lean_dec(v_next_4035_);
lean_dec_ref(v_leanOpts_4031_);
v_a_4083_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4079_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4079_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
else
{
uint8_t v___x_4091_; 
v___x_4091_ = lean_nat_dec_lt(v___x_4065_, v___x_4062_);
if (v___x_4091_ == 0)
{
lean_dec_ref_known(v_s_4064_, 2);
v_ws_4042_ = v_ws_4033_;
v_depIdxs_4043_ = v___x_4063_;
v___y_4044_ = v___y_4036_;
v___y_4045_ = v___y_4037_;
goto v___jp_4041_;
}
else
{
size_t v___x_4092_; size_t v___x_4093_; lean_object* v___x_4094_; 
lean_dec_ref(v___x_4063_);
lean_dec_ref(v_ws_4033_);
v___x_4092_ = lean_usize_of_nat(v___x_4062_);
v___x_4093_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_4031_);
lean_inc(v_pkg_4040_);
v___x_4094_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4040_, v_leanOpts_4031_, v_reconfigure_4032_, v_depConfigs_4061_, v___x_4092_, v___x_4093_, v_s_4064_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v_fst_4096_; lean_object* v_snd_4097_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v_fst_4096_ = lean_ctor_get(v_a_4095_, 0);
lean_inc(v_fst_4096_);
v_snd_4097_ = lean_ctor_get(v_a_4095_, 1);
lean_inc(v_snd_4097_);
lean_dec(v_a_4095_);
v_____x_4056_ = v_fst_4096_;
v___y_4057_ = v_snd_4097_;
v___y_4058_ = v___y_4037_;
goto v___jp_4055_;
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_pkg_4040_);
lean_dec(v_next_4035_);
lean_dec_ref(v_leanOpts_4031_);
v_a_4098_ = lean_ctor_get(v___x_4094_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4094_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4094_);
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
}
v___jp_4041_:
{
lean_object* v_ws_4046_; lean_object* v_packages_4047_; lean_object* v___x_4048_; uint8_t v___x_4049_; 
v_ws_4046_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_4042_, v_pkg_4040_, v_depIdxs_4043_);
v_packages_4047_ = lean_ctor_get(v_ws_4046_, 4);
lean_inc_ref(v_packages_4047_);
v___x_4048_ = lean_array_get_size(v_packages_4047_);
lean_dec_ref(v_packages_4047_);
v___x_4049_ = lean_nat_dec_lt(v_next_4035_, v___x_4048_);
if (v___x_4049_ == 0)
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
lean_dec(v_next_4035_);
lean_dec_ref(v_leanOpts_4031_);
v___x_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4050_, 0, v_ws_4046_);
lean_ctor_set(v___x_4050_, 1, v___y_4044_);
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
return v___x_4051_;
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_unsigned_to_nat(1u);
v___x_4053_ = lean_nat_add(v_next_4035_, v___x_4052_);
v_ws_4033_ = v_ws_4046_;
v_i_4034_ = v_next_4035_;
v_next_4035_ = v___x_4053_;
v___y_4036_ = v___y_4044_;
v___y_4037_ = v___y_4045_;
goto _start;
}
}
v___jp_4055_:
{
lean_object* v_ws_4059_; lean_object* v_depIdxs_4060_; 
v_ws_4059_ = lean_ctor_get(v_____x_4056_, 0);
lean_inc_ref(v_ws_4059_);
v_depIdxs_4060_ = lean_ctor_get(v_____x_4056_, 1);
lean_inc_ref(v_depIdxs_4060_);
lean_dec_ref(v_____x_4056_);
v_ws_4042_ = v_ws_4059_;
v_depIdxs_4043_ = v_depIdxs_4060_;
v___y_4044_ = v___y_4057_;
v___y_4045_ = v___y_4058_;
goto v___jp_4041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_4106_, lean_object* v_reconfigure_4107_, lean_object* v_ws_4108_, lean_object* v_i_4109_, lean_object* v_next_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
uint8_t v_reconfigure_boxed_4114_; lean_object* v_res_4115_; 
v_reconfigure_boxed_4114_ = lean_unbox(v_reconfigure_4107_);
v_res_4115_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4106_, v_reconfigure_boxed_4114_, v_ws_4108_, v_i_4109_, v_next_4110_, v___y_4111_, v___y_4112_);
lean_dec_ref(v___y_4112_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4118_, lean_object* v_toUpdate_4119_, lean_object* v_leanOpts_4120_, uint8_t v_updateToolchain_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = lean_box(1);
v___x_4125_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4122_, v_ws_4118_, v_toUpdate_4119_, v___x_4124_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v_snd_4127_; uint8_t v___x_4128_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v_snd_4127_ = lean_ctor_get(v_a_4126_, 1);
lean_inc(v_snd_4127_);
lean_dec(v_a_4126_);
v___x_4128_ = 1;
if (v_updateToolchain_4121_ == 0)
{
lean_object* v_packages_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v_wsIdx_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_packages_4129_ = lean_ctor_get(v_ws_4118_, 4);
v___x_4130_ = lean_unsigned_to_nat(0u);
v___x_4131_ = lean_array_fget_borrowed(v_packages_4129_, v___x_4130_);
v_wsIdx_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_wsIdx_4132_);
v___x_4133_ = lean_array_get_size(v_packages_4129_);
v___x_4134_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4120_, v___x_4128_, v_ws_4118_, v_wsIdx_4132_, v___x_4133_, v_snd_4127_, v_a_4122_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4152_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4152_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4152_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v_fst_4139_; lean_object* v_snd_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4151_; 
v_fst_4139_ = lean_ctor_get(v_a_4135_, 0);
v_snd_4140_ = lean_ctor_get(v_a_4135_, 1);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_a_4135_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4142_ = v_a_4135_;
v_isShared_4143_ = v_isSharedCheck_4151_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_snd_4140_);
lean_inc(v_fst_4139_);
lean_dec(v_a_4135_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4151_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4144_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4139_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 0, v___x_4144_);
v___x_4146_ = v___x_4142_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4144_);
lean_ctor_set(v_reuseFailAlloc_4150_, 1, v_snd_4140_);
v___x_4146_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4148_; 
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v___x_4146_);
v___x_4148_ = v___x_4137_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
else
{
return v___x_4134_;
}
}
else
{
lean_object* v_packages_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v_depConfigs_4156_; lean_object* v___x_4157_; lean_object* v___f_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_packages_4153_ = lean_ctor_get(v_ws_4118_, 4);
lean_inc_ref(v_packages_4153_);
v___x_4154_ = lean_unsigned_to_nat(0u);
v___x_4155_ = lean_array_fget_borrowed(v_packages_4153_, v___x_4154_);
v_depConfigs_4156_ = lean_ctor_get(v___x_4155_, 12);
v___x_4157_ = lean_box(v_updateToolchain_4121_);
lean_inc_ref(v_ws_4118_);
lean_inc(v___x_4155_);
v___f_4158_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4158_, 0, v___x_4155_);
lean_closure_set(v___f_4158_, 1, v___x_4157_);
lean_closure_set(v___f_4158_, 2, v_ws_4118_);
v___x_4159_ = lean_array_get_size(v_depConfigs_4156_);
lean_inc_ref(v_depConfigs_4156_);
v___x_4160_ = l_Array_reverse___redArg(v_depConfigs_4156_);
v___x_4161_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4162_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4159_, v___f_4158_, v___x_4160_, v___x_4154_, v___x_4161_, v_snd_4127_, v_a_4122_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v_fst_4164_; lean_object* v_snd_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4237_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v_fst_4164_ = lean_ctor_get(v_a_4163_, 0);
v_snd_4165_ = lean_ctor_get(v_a_4163_, 1);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_a_4163_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4167_ = v_a_4163_;
v_isShared_4168_ = v_isSharedCheck_4237_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_snd_4165_);
lean_inc(v_fst_4164_);
lean_dec(v_a_4163_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4237_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; 
lean_inc_ref(v_ws_4118_);
v___x_4169_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4122_, v_ws_4118_, v_fst_4164_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v___x_4170_; 
lean_dec_ref_known(v___x_4169_, 1);
lean_inc_ref(v_leanOpts_4120_);
v___x_4170_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4159_, v_fst_4164_, v___x_4160_, v_leanOpts_4120_, v___x_4154_, v_ws_4118_, v_snd_4165_, v_a_4122_);
lean_dec_ref(v___x_4160_);
lean_dec(v_fst_4164_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4220_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4220_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4220_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v_fst_4175_; lean_object* v_snd_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4219_; 
v_fst_4175_ = lean_ctor_get(v_a_4171_, 0);
v_snd_4176_ = lean_ctor_get(v_a_4171_, 1);
v_isSharedCheck_4219_ = !lean_is_exclusive(v_a_4171_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4178_ = v_a_4171_;
v_isShared_4179_ = v_isSharedCheck_4219_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_snd_4176_);
lean_inc(v_fst_4175_);
lean_dec(v_a_4171_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4219_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v_packages_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
v_packages_4180_ = lean_ctor_get(v_fst_4175_, 4);
v___x_4181_ = lean_array_get_size(v_packages_4153_);
lean_dec_ref(v_packages_4153_);
v___x_4182_ = lean_array_get_size(v_packages_4180_);
v___x_4183_ = lean_array_fget(v_packages_4180_, v___x_4154_);
v___x_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4181_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 1, v___x_4182_);
lean_ctor_set(v___x_4167_, 0, v___x_4184_);
v___x_4186_ = v___x_4167_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4184_);
lean_ctor_set(v_reuseFailAlloc_4218_, 1, v___x_4182_);
v___x_4186_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4187_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4186_, v___x_4161_);
v___x_4188_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4175_, v___x_4183_, v___x_4187_);
v___x_4189_ = lean_nat_dec_eq(v___x_4181_, v___x_4182_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_del_object(v___x_4178_);
lean_del_object(v___x_4173_);
v___x_4190_ = lean_unsigned_to_nat(1u);
v___x_4191_ = lean_nat_add(v___x_4181_, v___x_4190_);
v___x_4192_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4120_, v___x_4128_, v___x_4188_, v___x_4181_, v___x_4191_, v_snd_4176_, v_a_4122_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4210_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4195_ = v___x_4192_;
v_isShared_4196_ = v_isSharedCheck_4210_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4210_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v_fst_4197_; lean_object* v_snd_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4209_; 
v_fst_4197_ = lean_ctor_get(v_a_4193_, 0);
v_snd_4198_ = lean_ctor_get(v_a_4193_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_a_4193_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4200_ = v_a_4193_;
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_snd_4198_);
lean_inc(v_fst_4197_);
lean_dec(v_a_4193_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4204_; 
v___x_4202_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4197_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4202_);
v___x_4204_ = v___x_4200_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4202_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_snd_4198_);
v___x_4204_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
lean_object* v___x_4206_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v___x_4204_);
v___x_4206_ = v___x_4195_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4204_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
else
{
return v___x_4192_;
}
}
else
{
lean_object* v___x_4211_; lean_object* v___x_4213_; 
lean_dec_ref(v_leanOpts_4120_);
v___x_4211_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4188_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4211_);
v___x_4213_ = v___x_4178_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4211_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_snd_4176_);
v___x_4213_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4215_; 
if (v_isShared_4174_ == 0)
{
lean_ctor_set(v___x_4173_, 0, v___x_4213_);
v___x_4215_ = v___x_4173_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_del_object(v___x_4167_);
lean_dec_ref(v_packages_4153_);
lean_dec_ref(v_leanOpts_4120_);
v_a_4221_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4170_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4170_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_del_object(v___x_4167_);
lean_dec(v_snd_4165_);
lean_dec(v_fst_4164_);
lean_dec_ref(v___x_4160_);
lean_dec_ref(v_packages_4153_);
lean_dec_ref(v_leanOpts_4120_);
lean_dec_ref(v_ws_4118_);
v_a_4229_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4169_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4169_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec_ref(v___x_4160_);
lean_dec_ref(v_packages_4153_);
lean_dec_ref(v_leanOpts_4120_);
lean_dec_ref(v_ws_4118_);
v_a_4238_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4162_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4162_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v_leanOpts_4120_);
lean_dec_ref(v_ws_4118_);
v_a_4246_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4125_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4125_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4254_, lean_object* v_toUpdate_4255_, lean_object* v_leanOpts_4256_, lean_object* v_updateToolchain_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
uint8_t v_updateToolchain_boxed_4260_; lean_object* v_res_4261_; 
v_updateToolchain_boxed_4260_ = lean_unbox(v_updateToolchain_4257_);
v_res_4261_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4254_, v_toUpdate_4255_, v_leanOpts_4256_, v_updateToolchain_boxed_4260_, v_a_4258_);
lean_dec_ref(v_a_4258_);
lean_dec(v_toUpdate_4255_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4262_, uint8_t v_reconfigure_4263_, lean_object* v_ws_4264_, lean_object* v_i_4265_, lean_object* v_i__lt_4266_, lean_object* v_next_4267_, lean_object* v_lt__next_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; 
v___x_4272_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4262_, v_reconfigure_4263_, v_ws_4264_, v_i_4265_, v_next_4267_, v___y_4269_, v___y_4270_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4273_, lean_object* v_reconfigure_4274_, lean_object* v_ws_4275_, lean_object* v_i_4276_, lean_object* v_i__lt_4277_, lean_object* v_next_4278_, lean_object* v_lt__next_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
uint8_t v_reconfigure_boxed_4283_; lean_object* v_res_4284_; 
v_reconfigure_boxed_4283_ = lean_unbox(v_reconfigure_4274_);
v_res_4284_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4273_, v_reconfigure_boxed_4283_, v_ws_4275_, v_i_4276_, v_i__lt_4277_, v_next_4278_, v_lt__next_4279_, v___y_4280_, v___y_4281_);
lean_dec_ref(v___y_4281_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4285_, lean_object* v_00_u03b2_4286_, lean_object* v_n_4287_, lean_object* v_f_4288_, lean_object* v_xs_4289_, lean_object* v_k_4290_, lean_object* v_h_4291_, lean_object* v_acc_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4287_, v_f_4288_, v_xs_4289_, v_k_4290_, v_acc_4292_, v___y_4293_, v___y_4294_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4297_, lean_object* v_00_u03b2_4298_, lean_object* v_n_4299_, lean_object* v_f_4300_, lean_object* v_xs_4301_, lean_object* v_k_4302_, lean_object* v_h_4303_, lean_object* v_acc_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4297_, v_00_u03b2_4298_, v_n_4299_, v_f_4300_, v_xs_4301_, v_k_4302_, v_h_4303_, v_acc_4304_, v___y_4305_, v___y_4306_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v_xs_4301_);
lean_dec(v_n_4299_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_inst_4309_, lean_object* v_R_4310_, lean_object* v_a_4311_, lean_object* v_b_4312_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_a_4311_, v_b_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4314_, lean_object* v_fst_4315_, lean_object* v___x_4316_, lean_object* v_leanOpts_4317_, lean_object* v_inst_4318_, lean_object* v_R_4319_, lean_object* v_a_4320_, lean_object* v_b_4321_, lean_object* v_c_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4314_, v_fst_4315_, v___x_4316_, v_leanOpts_4317_, v_a_4320_, v_b_4321_, v___y_4323_, v___y_4324_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4327_, lean_object* v_fst_4328_, lean_object* v___x_4329_, lean_object* v_leanOpts_4330_, lean_object* v_inst_4331_, lean_object* v_R_4332_, lean_object* v_a_4333_, lean_object* v_b_4334_, lean_object* v_c_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4327_, v_fst_4328_, v___x_4329_, v_leanOpts_4330_, v_inst_4331_, v_R_4332_, v_a_4333_, v_b_4334_, v_c_4335_, v___y_4336_, v___y_4337_);
lean_dec_ref(v___y_4337_);
lean_dec_ref(v___x_4329_);
lean_dec_ref(v_fst_4328_);
lean_dec(v_upperBound_4327_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_start_4340_, lean_object* v_pkg_4341_, lean_object* v_leanOpts_4342_, uint8_t v_reconfigure_4343_, lean_object* v_as_4344_, size_t v_i_4345_, size_t v_stop_4346_, lean_object* v_b_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg(v_pkg_4341_, v_leanOpts_4342_, v_reconfigure_4343_, v_as_4344_, v_i_4345_, v_stop_4346_, v_b_4347_, v___y_4348_, v___y_4349_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_start_4352_, lean_object* v_pkg_4353_, lean_object* v_leanOpts_4354_, lean_object* v_reconfigure_4355_, lean_object* v_as_4356_, lean_object* v_i_4357_, lean_object* v_stop_4358_, lean_object* v_b_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
uint8_t v_reconfigure_boxed_4363_; size_t v_i_boxed_4364_; size_t v_stop_boxed_4365_; lean_object* v_res_4366_; 
v_reconfigure_boxed_4363_ = lean_unbox(v_reconfigure_4355_);
v_i_boxed_4364_ = lean_unbox_usize(v_i_4357_);
lean_dec(v_i_4357_);
v_stop_boxed_4365_ = lean_unbox_usize(v_stop_4358_);
lean_dec(v_stop_4358_);
v_res_4366_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_start_4352_, v_pkg_4353_, v_leanOpts_4354_, v_reconfigure_boxed_4363_, v_as_4356_, v_i_boxed_4364_, v_stop_boxed_4365_, v_b_4359_, v___y_4360_, v___y_4361_);
lean_dec_ref(v___y_4361_);
lean_dec_ref(v_as_4356_);
lean_dec(v_start_4352_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_4367_, lean_object* v_msg_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6_spec__8___redArg(v_msg_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v_00_u03b2_4370_, lean_object* v_k_4371_, lean_object* v_v_4372_, lean_object* v_t_4373_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___redArg(v_k_4371_, v_v_4372_, v_t_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_init_4375_, lean_object* v_t_4376_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7_spec__10(v_init_4375_, v_t_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4378_, lean_object* v_as_4379_, size_t v_i_4380_, size_t v_stop_4381_, lean_object* v_b_4382_){
_start:
{
lean_object* v___y_4384_; uint8_t v___x_4388_; 
v___x_4388_ = lean_usize_dec_eq(v_i_4380_, v_stop_4381_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; lean_object* v_baseName_4390_; lean_object* v_relConfigFile_4391_; lean_object* v_relManifestFile_4392_; lean_object* v___x_4393_; 
v___x_4389_ = lean_array_uget_borrowed(v_as_4379_, v_i_4380_);
v_baseName_4390_ = lean_ctor_get(v___x_4389_, 1);
v_relConfigFile_4391_ = lean_ctor_get(v___x_4389_, 8);
v_relManifestFile_4392_ = lean_ctor_get(v___x_4389_, 9);
v___x_4393_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4378_, v_baseName_4390_);
if (lean_obj_tag(v___x_4393_) == 0)
{
v___y_4384_ = v_b_4382_;
goto v___jp_4383_;
}
else
{
lean_object* v_val_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4415_; 
v_val_4394_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4396_ = v___x_4393_;
v_isShared_4397_ = v_isSharedCheck_4415_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_val_4394_);
lean_dec(v___x_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4415_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v_name_4398_; lean_object* v_scope_4399_; uint8_t v_inherited_4400_; lean_object* v_src_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4412_; 
v_name_4398_ = lean_ctor_get(v_val_4394_, 0);
v_scope_4399_ = lean_ctor_get(v_val_4394_, 1);
v_inherited_4400_ = lean_ctor_get_uint8(v_val_4394_, sizeof(void*)*5);
v_src_4401_ = lean_ctor_get(v_val_4394_, 4);
v_isSharedCheck_4412_ = !lean_is_exclusive(v_val_4394_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; lean_object* v_unused_4414_; 
v_unused_4413_ = lean_ctor_get(v_val_4394_, 3);
lean_dec(v_unused_4413_);
v_unused_4414_ = lean_ctor_get(v_val_4394_, 2);
lean_dec(v_unused_4414_);
v___x_4403_ = v_val_4394_;
v_isShared_4404_ = v_isSharedCheck_4412_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_src_4401_);
lean_inc(v_scope_4399_);
lean_inc(v_name_4398_);
lean_dec(v_val_4394_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4412_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
lean_inc_ref(v_relManifestFile_4392_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v_relManifestFile_4392_);
v___x_4406_ = v___x_4396_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v_relManifestFile_4392_);
v___x_4406_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4408_; 
lean_inc_ref(v_relConfigFile_4391_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 3, v___x_4406_);
lean_ctor_set(v___x_4403_, 2, v_relConfigFile_4391_);
v___x_4408_ = v___x_4403_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_name_4398_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_scope_4399_);
lean_ctor_set(v_reuseFailAlloc_4410_, 2, v_relConfigFile_4391_);
lean_ctor_set(v_reuseFailAlloc_4410_, 3, v___x_4406_);
lean_ctor_set(v_reuseFailAlloc_4410_, 4, v_src_4401_);
lean_ctor_set_uint8(v_reuseFailAlloc_4410_, sizeof(void*)*5, v_inherited_4400_);
v___x_4408_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_array_push(v_b_4382_, v___x_4408_);
v___y_4384_ = v___x_4409_;
goto v___jp_4383_;
}
}
}
}
}
}
else
{
return v_b_4382_;
}
v___jp_4383_:
{
size_t v___x_4385_; size_t v___x_4386_; 
v___x_4385_ = ((size_t)1ULL);
v___x_4386_ = lean_usize_add(v_i_4380_, v___x_4385_);
v_i_4380_ = v___x_4386_;
v_b_4382_ = v___y_4384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4416_, lean_object* v_as_4417_, lean_object* v_i_4418_, lean_object* v_stop_4419_, lean_object* v_b_4420_){
_start:
{
size_t v_i_boxed_4421_; size_t v_stop_boxed_4422_; lean_object* v_res_4423_; 
v_i_boxed_4421_ = lean_unbox_usize(v_i_4418_);
lean_dec(v_i_4418_);
v_stop_boxed_4422_ = lean_unbox_usize(v_stop_4419_);
lean_dec(v_stop_4419_);
v_res_4423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4416_, v_as_4417_, v_i_boxed_4421_, v_stop_boxed_4422_, v_b_4420_);
lean_dec_ref(v_as_4417_);
lean_dec(v_entries_4416_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4424_, lean_object* v_entries_4425_){
_start:
{
lean_object* v_packages_4427_; lean_object* v___y_4429_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; uint8_t v___x_4447_; 
v_packages_4427_ = lean_ctor_get(v_ws_4424_, 4);
v___x_4444_ = lean_unsigned_to_nat(0u);
v___x_4445_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4446_ = lean_array_get_size(v_packages_4427_);
v___x_4447_ = lean_nat_dec_lt(v___x_4444_, v___x_4446_);
if (v___x_4447_ == 0)
{
v___y_4429_ = v___x_4445_;
goto v___jp_4428_;
}
else
{
uint8_t v___x_4448_; 
v___x_4448_ = lean_nat_dec_le(v___x_4446_, v___x_4446_);
if (v___x_4448_ == 0)
{
if (v___x_4447_ == 0)
{
v___y_4429_ = v___x_4445_;
goto v___jp_4428_;
}
else
{
size_t v___x_4449_; size_t v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = ((size_t)0ULL);
v___x_4450_ = lean_usize_of_nat(v___x_4446_);
v___x_4451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4425_, v_packages_4427_, v___x_4449_, v___x_4450_, v___x_4445_);
v___y_4429_ = v___x_4451_;
goto v___jp_4428_;
}
}
else
{
size_t v___x_4452_; size_t v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = ((size_t)0ULL);
v___x_4453_ = lean_usize_of_nat(v___x_4446_);
v___x_4454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4425_, v_packages_4427_, v___x_4452_, v___x_4453_, v___x_4445_);
v___y_4429_ = v___x_4454_;
goto v___jp_4428_;
}
}
v___jp_4428_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v_config_4432_; lean_object* v_baseName_4433_; lean_object* v_dir_4434_; lean_object* v_relManifestFile_4435_; lean_object* v_toWorkspaceConfig_4436_; uint8_t v_fixedToolchain_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v_manifest_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4430_ = lean_unsigned_to_nat(0u);
v___x_4431_ = lean_array_fget_borrowed(v_packages_4427_, v___x_4430_);
v_config_4432_ = lean_ctor_get(v___x_4431_, 6);
v_baseName_4433_ = lean_ctor_get(v___x_4431_, 1);
v_dir_4434_ = lean_ctor_get(v___x_4431_, 4);
v_relManifestFile_4435_ = lean_ctor_get(v___x_4431_, 9);
v_toWorkspaceConfig_4436_ = lean_ctor_get(v_config_4432_, 0);
v_fixedToolchain_4437_ = lean_ctor_get_uint8(v_config_4432_, sizeof(void*)*27 + 6);
v___x_4438_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4436_);
v___x_4439_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4436_);
v___x_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
lean_inc(v_baseName_4433_);
v_manifest_4441_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4441_, 0, v_baseName_4433_);
lean_ctor_set(v_manifest_4441_, 1, v___x_4438_);
lean_ctor_set(v_manifest_4441_, 2, v___x_4440_);
lean_ctor_set(v_manifest_4441_, 3, v___y_4429_);
lean_ctor_set_uint8(v_manifest_4441_, sizeof(void*)*4, v_fixedToolchain_4437_);
lean_inc_ref(v_relManifestFile_4435_);
lean_inc_ref(v_dir_4434_);
v___x_4442_ = l_Lake_joinRelative(v_dir_4434_, v_relManifestFile_4435_);
v___x_4443_ = l_Lake_Manifest_save(v_manifest_4441_, v___x_4442_);
lean_dec_ref(v___x_4442_);
return v___x_4443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4455_, lean_object* v_entries_4456_, lean_object* v_a_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4455_, v_entries_4456_);
lean_dec(v_entries_4456_);
lean_dec_ref(v_ws_4455_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4459_, lean_object* v_as_4460_, size_t v_i_4461_, size_t v_stop_4462_, lean_object* v_b_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v_a_4468_; lean_object* v___y_4473_; uint8_t v___x_4478_; 
v___x_4478_ = lean_usize_dec_eq(v_i_4461_, v_stop_4462_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_9317__overap_4481_; lean_object* v___x_4482_; 
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_9317__overap_4481_ = lean_array_uget_borrowed(v_as_4460_, v_i_4461_);
lean_inc(v___x_9317__overap_4481_);
lean_inc(v___y_4464_);
lean_inc_ref(v_pkg_4459_);
v___x_4482_ = lean_apply_4(v___x_9317__overap_4481_, v_pkg_4459_, v___y_4464_, v___x_4480_, lean_box(0));
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v_a_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
v_a_4484_ = lean_ctor_get(v___x_4482_, 1);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4482_, 2);
v___x_4485_ = lean_array_get_size(v_a_4484_);
v___x_4486_ = lean_nat_dec_lt(v___x_4479_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_dec(v_a_4484_);
v_a_4468_ = v_a_4483_;
goto v___jp_4467_;
}
else
{
lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4487_ = lean_box(0);
v___x_4488_ = lean_nat_dec_le(v___x_4485_, v___x_4485_);
if (v___x_4488_ == 0)
{
if (v___x_4486_ == 0)
{
lean_dec(v_a_4484_);
v_a_4468_ = v_a_4483_;
goto v___jp_4467_;
}
else
{
size_t v___x_4489_; size_t v___x_4490_; lean_object* v___x_4491_; 
v___x_4489_ = ((size_t)0ULL);
v___x_4490_ = lean_usize_of_nat(v___x_4485_);
v___x_4491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4484_, v___x_4489_, v___x_4490_, v___x_4487_, v___y_4465_);
lean_dec(v_a_4484_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_dec_ref_known(v___x_4491_, 1);
v_a_4468_ = v_a_4483_;
goto v___jp_4467_;
}
else
{
lean_dec(v_a_4483_);
v___y_4473_ = v___x_4491_;
goto v___jp_4472_;
}
}
}
else
{
size_t v___x_4492_; size_t v___x_4493_; lean_object* v___x_4494_; 
v___x_4492_ = ((size_t)0ULL);
v___x_4493_ = lean_usize_of_nat(v___x_4485_);
v___x_4494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4484_, v___x_4492_, v___x_4493_, v___x_4487_, v___y_4465_);
lean_dec(v_a_4484_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_dec_ref_known(v___x_4494_, 1);
v_a_4468_ = v_a_4483_;
goto v___jp_4467_;
}
else
{
lean_dec(v_a_4483_);
v___y_4473_ = v___x_4494_;
goto v___jp_4472_;
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4496_; uint8_t v___x_4497_; 
v_a_4495_ = lean_ctor_get(v___x_4482_, 1);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4482_, 2);
v___x_4496_ = lean_array_get_size(v_a_4495_);
v___x_4497_ = lean_nat_dec_lt(v___x_4479_, v___x_4496_);
if (v___x_4497_ == 0)
{
lean_object* v___x_4498_; lean_object* v___x_4499_; 
lean_dec(v_a_4495_);
lean_dec_ref(v_pkg_4459_);
v___x_4498_ = lean_box(0);
v___x_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
else
{
lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4500_ = lean_box(0);
v___x_4501_ = lean_nat_dec_le(v___x_4496_, v___x_4496_);
if (v___x_4501_ == 0)
{
if (v___x_4497_ == 0)
{
lean_dec(v_a_4495_);
lean_dec_ref(v_pkg_4459_);
goto v___jp_4475_;
}
else
{
size_t v___x_4502_; size_t v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = ((size_t)0ULL);
v___x_4503_ = lean_usize_of_nat(v___x_4496_);
v___x_4504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4495_, v___x_4502_, v___x_4503_, v___x_4500_, v___y_4465_);
lean_dec(v_a_4495_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_dec_ref_known(v___x_4504_, 1);
lean_dec_ref(v_pkg_4459_);
goto v___jp_4475_;
}
else
{
v___y_4473_ = v___x_4504_;
goto v___jp_4472_;
}
}
}
else
{
size_t v___x_4505_; size_t v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = ((size_t)0ULL);
v___x_4506_ = lean_usize_of_nat(v___x_4496_);
v___x_4507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4495_, v___x_4505_, v___x_4506_, v___x_4500_, v___y_4465_);
lean_dec(v_a_4495_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_dec_ref_known(v___x_4507_, 1);
lean_dec_ref(v_pkg_4459_);
goto v___jp_4475_;
}
else
{
v___y_4473_ = v___x_4507_;
goto v___jp_4472_;
}
}
}
}
}
else
{
lean_object* v___x_4508_; 
lean_dec_ref(v_pkg_4459_);
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v_b_4463_);
return v___x_4508_;
}
v___jp_4467_:
{
size_t v___x_4469_; size_t v___x_4470_; 
v___x_4469_ = ((size_t)1ULL);
v___x_4470_ = lean_usize_add(v_i_4461_, v___x_4469_);
v_i_4461_ = v___x_4470_;
v_b_4463_ = v_a_4468_;
goto _start;
}
v___jp_4472_:
{
if (lean_obj_tag(v___y_4473_) == 0)
{
lean_object* v_a_4474_; 
v_a_4474_ = lean_ctor_get(v___y_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___y_4473_, 1);
v_a_4468_ = v_a_4474_;
goto v___jp_4467_;
}
else
{
lean_dec_ref(v_pkg_4459_);
return v___y_4473_;
}
}
v___jp_4475_:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_box(0);
v___x_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4509_, lean_object* v_as_4510_, lean_object* v_i_4511_, lean_object* v_stop_4512_, lean_object* v_b_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
size_t v_i_boxed_4517_; size_t v_stop_boxed_4518_; lean_object* v_res_4519_; 
v_i_boxed_4517_ = lean_unbox_usize(v_i_4511_);
lean_dec(v_i_4511_);
v_stop_boxed_4518_ = lean_unbox_usize(v_stop_4512_);
lean_dec(v_stop_4512_);
v_res_4519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4509_, v_as_4510_, v_i_boxed_4517_, v_stop_boxed_4518_, v_b_4513_, v___y_4514_, v___y_4515_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v_as_4510_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v_baseName_4525_; lean_object* v_postUpdateHooks_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v_baseName_4525_ = lean_ctor_get(v_pkg_4521_, 1);
v_postUpdateHooks_4526_ = lean_ctor_get(v_pkg_4521_, 20);
lean_inc_ref(v_postUpdateHooks_4526_);
v___x_4527_ = lean_array_get_size(v_postUpdateHooks_4526_);
v___x_4528_ = lean_unsigned_to_nat(0u);
v___x_4529_ = lean_nat_dec_eq(v___x_4527_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; uint8_t v___x_4537_; 
lean_inc(v_baseName_4525_);
v___x_4530_ = l_Lean_Name_toString(v_baseName_4525_, v___x_4529_);
v___x_4531_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4532_ = lean_string_append(v___x_4530_, v___x_4531_);
v___x_4533_ = 1;
v___x_4534_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4534_, 0, v___x_4532_);
lean_ctor_set_uint8(v___x_4534_, sizeof(void*)*1, v___x_4533_);
lean_inc_ref(v_a_4523_);
v___x_4535_ = lean_apply_2(v_a_4523_, v___x_4534_, lean_box(0));
v___x_4536_ = lean_box(0);
v___x_4537_ = lean_nat_dec_lt(v___x_4528_, v___x_4527_);
if (v___x_4537_ == 0)
{
lean_object* v___x_4538_; 
lean_dec_ref(v_postUpdateHooks_4526_);
lean_dec_ref(v_pkg_4521_);
v___x_4538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4536_);
return v___x_4538_;
}
else
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_nat_dec_le(v___x_4527_, v___x_4527_);
if (v___x_4539_ == 0)
{
if (v___x_4537_ == 0)
{
lean_object* v___x_4540_; 
lean_dec_ref(v_postUpdateHooks_4526_);
lean_dec_ref(v_pkg_4521_);
v___x_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4536_);
return v___x_4540_;
}
else
{
size_t v___x_4541_; size_t v___x_4542_; lean_object* v___x_4543_; 
v___x_4541_ = ((size_t)0ULL);
v___x_4542_ = lean_usize_of_nat(v___x_4527_);
v___x_4543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4521_, v_postUpdateHooks_4526_, v___x_4541_, v___x_4542_, v___x_4536_, v_a_4522_, v_a_4523_);
lean_dec_ref(v_postUpdateHooks_4526_);
return v___x_4543_;
}
}
else
{
size_t v___x_4544_; size_t v___x_4545_; lean_object* v___x_4546_; 
v___x_4544_ = ((size_t)0ULL);
v___x_4545_ = lean_usize_of_nat(v___x_4527_);
v___x_4546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4521_, v_postUpdateHooks_4526_, v___x_4544_, v___x_4545_, v___x_4536_, v_a_4522_, v_a_4523_);
lean_dec_ref(v_postUpdateHooks_4526_);
return v___x_4546_;
}
}
}
else
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
lean_dec_ref(v_postUpdateHooks_4526_);
lean_dec_ref(v_pkg_4521_);
v___x_4547_ = lean_box(0);
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
return v___x_4548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4549_, v_a_4550_, v_a_4551_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4554_, lean_object* v_ws_4555_, lean_object* v_toUpdate_4556_, lean_object* v_leanOpts_4557_, uint8_t v_updateToolchain_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4560_ = lean_box(1);
v___x_4561_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4554_, v_ws_4555_, v_toUpdate_4556_, v___x_4560_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v_snd_4563_; uint8_t v___x_4564_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref_known(v___x_4561_, 1);
v_snd_4563_ = lean_ctor_get(v_a_4562_, 1);
lean_inc(v_snd_4563_);
lean_dec(v_a_4562_);
v___x_4564_ = 1;
if (v_updateToolchain_4558_ == 0)
{
lean_object* v_packages_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v_wsIdx_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v_packages_4565_ = lean_ctor_get(v_ws_4555_, 4);
v___x_4566_ = lean_unsigned_to_nat(0u);
v___x_4567_ = lean_array_fget_borrowed(v_packages_4565_, v___x_4566_);
v_wsIdx_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_wsIdx_4568_);
v___x_4569_ = lean_array_get_size(v_packages_4565_);
v___x_4570_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4557_, v___x_4564_, v_ws_4555_, v_wsIdx_4568_, v___x_4569_, v_snd_4563_, v_a_4554_);
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
lean_object* v_packages_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v_depConfigs_4592_; lean_object* v___x_4593_; lean_object* v___f_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v_packages_4589_ = lean_ctor_get(v_ws_4555_, 4);
lean_inc_ref(v_packages_4589_);
v___x_4590_ = lean_unsigned_to_nat(0u);
v___x_4591_ = lean_array_fget_borrowed(v_packages_4589_, v___x_4590_);
v_depConfigs_4592_ = lean_ctor_get(v___x_4591_, 12);
v___x_4593_ = lean_box(v_updateToolchain_4558_);
lean_inc_ref(v_ws_4555_);
lean_inc(v___x_4591_);
v___f_4594_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4594_, 0, v___x_4591_);
lean_closure_set(v___f_4594_, 1, v___x_4593_);
lean_closure_set(v___f_4594_, 2, v_ws_4555_);
v___x_4595_ = lean_array_get_size(v_depConfigs_4592_);
lean_inc_ref(v_depConfigs_4592_);
v___x_4596_ = l_Array_reverse___redArg(v_depConfigs_4592_);
v___x_4597_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4598_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4595_, v___f_4594_, v___x_4596_, v___x_4590_, v___x_4597_, v_snd_4563_, v_a_4554_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v_fst_4600_; lean_object* v_snd_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4673_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
v_fst_4600_ = lean_ctor_get(v_a_4599_, 0);
v_snd_4601_ = lean_ctor_get(v_a_4599_, 1);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_a_4599_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4603_ = v_a_4599_;
v_isShared_4604_ = v_isSharedCheck_4673_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_snd_4601_);
lean_inc(v_fst_4600_);
lean_dec(v_a_4599_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4673_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4605_; 
lean_inc_ref(v_ws_4555_);
v___x_4605_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4554_, v_ws_4555_, v_fst_4600_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v___x_4606_; 
lean_dec_ref_known(v___x_4605_, 1);
lean_inc_ref(v_leanOpts_4557_);
v___x_4606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4595_, v_fst_4600_, v___x_4596_, v_leanOpts_4557_, v___x_4590_, v_ws_4555_, v_snd_4601_, v_a_4554_);
lean_dec_ref(v___x_4596_);
lean_dec(v_fst_4600_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4656_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4609_ = v___x_4606_;
v_isShared_4610_ = v_isSharedCheck_4656_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4656_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v_fst_4611_; lean_object* v_snd_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4655_; 
v_fst_4611_ = lean_ctor_get(v_a_4607_, 0);
v_snd_4612_ = lean_ctor_get(v_a_4607_, 1);
v_isSharedCheck_4655_ = !lean_is_exclusive(v_a_4607_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4614_ = v_a_4607_;
v_isShared_4615_ = v_isSharedCheck_4655_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_snd_4612_);
lean_inc(v_fst_4611_);
lean_dec(v_a_4607_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4655_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v_packages_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v_packages_4616_ = lean_ctor_get(v_fst_4611_, 4);
v___x_4617_ = lean_array_get_size(v_packages_4589_);
lean_dec_ref(v_packages_4589_);
v___x_4618_ = lean_array_get_size(v_packages_4616_);
v___x_4619_ = lean_array_fget(v_packages_4616_, v___x_4590_);
v___x_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4617_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 1, v___x_4618_);
lean_ctor_set(v___x_4603_, 0, v___x_4620_);
v___x_4622_ = v___x_4603_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v___x_4620_);
lean_ctor_set(v_reuseFailAlloc_4654_, 1, v___x_4618_);
v___x_4622_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v___x_4623_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4622_, v___x_4597_);
v___x_4624_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_fst_4611_, v___x_4619_, v___x_4623_);
v___x_4625_ = lean_nat_dec_eq(v___x_4617_, v___x_4618_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
lean_del_object(v___x_4614_);
lean_del_object(v___x_4609_);
v___x_4626_ = lean_unsigned_to_nat(1u);
v___x_4627_ = lean_nat_add(v___x_4617_, v___x_4626_);
v___x_4628_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4557_, v___x_4564_, v___x_4624_, v___x_4617_, v___x_4627_, v_snd_4612_, v_a_4554_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4646_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4631_ = v___x_4628_;
v_isShared_4632_ = v_isSharedCheck_4646_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v___x_4628_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4646_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v_fst_4633_; lean_object* v_snd_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4645_; 
v_fst_4633_ = lean_ctor_get(v_a_4629_, 0);
v_snd_4634_ = lean_ctor_get(v_a_4629_, 1);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_a_4629_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4636_ = v_a_4629_;
v_isShared_4637_ = v_isSharedCheck_4645_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_snd_4634_);
lean_inc(v_fst_4633_);
lean_dec(v_a_4629_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4645_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4638_; lean_object* v___x_4640_; 
v___x_4638_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_fst_4633_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v___x_4638_);
v___x_4640_ = v___x_4636_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v_snd_4634_);
v___x_4640_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
lean_object* v___x_4642_; 
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v___x_4640_);
v___x_4642_ = v___x_4631_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v___x_4640_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
else
{
return v___x_4628_;
}
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4649_; 
lean_dec_ref(v_leanOpts_4557_);
v___x_4647_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v___x_4624_);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4647_);
v___x_4649_ = v___x_4614_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v_snd_4612_);
v___x_4649_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
lean_object* v___x_4651_; 
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v___x_4649_);
v___x_4651_ = v___x_4609_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4664_; 
lean_del_object(v___x_4603_);
lean_dec_ref(v_packages_4589_);
lean_dec_ref(v_leanOpts_4557_);
v_a_4657_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4659_ = v___x_4606_;
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v___x_4606_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
if (v_isShared_4660_ == 0)
{
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
lean_del_object(v___x_4603_);
lean_dec(v_snd_4601_);
lean_dec(v_fst_4600_);
lean_dec_ref(v___x_4596_);
lean_dec_ref(v_packages_4589_);
lean_dec_ref(v_leanOpts_4557_);
lean_dec_ref(v_ws_4555_);
v_a_4665_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4605_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4605_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_dec_ref(v___x_4596_);
lean_dec_ref(v_packages_4589_);
lean_dec_ref(v_leanOpts_4557_);
lean_dec_ref(v_ws_4555_);
v_a_4674_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4598_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4598_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_dec_ref(v_leanOpts_4557_);
lean_dec_ref(v_ws_4555_);
v_a_4682_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4561_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4561_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4690_, lean_object* v_ws_4691_, lean_object* v_toUpdate_4692_, lean_object* v_leanOpts_4693_, lean_object* v_updateToolchain_4694_, lean_object* v_a_4695_){
_start:
{
uint8_t v_updateToolchain_boxed_4696_; lean_object* v_res_4697_; 
v_updateToolchain_boxed_4696_ = lean_unbox(v_updateToolchain_4694_);
v_res_4697_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4690_, v_ws_4691_, v_toUpdate_4692_, v_leanOpts_4693_, v_updateToolchain_boxed_4696_);
lean_dec(v_toUpdate_4692_);
lean_dec_ref(v_a_4690_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4698_, size_t v_i_4699_, size_t v_stop_4700_, lean_object* v_b_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_){
_start:
{
uint8_t v___x_4705_; 
v___x_4705_ = lean_usize_dec_eq(v_i_4699_, v_stop_4700_);
if (v___x_4705_ == 0)
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = lean_array_uget_borrowed(v_as_4698_, v_i_4699_);
lean_inc(v___x_4706_);
v___x_4707_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4706_, v___y_4702_, v___y_4703_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; size_t v___x_4709_; size_t v___x_4710_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref_known(v___x_4707_, 1);
v___x_4709_ = ((size_t)1ULL);
v___x_4710_ = lean_usize_add(v_i_4699_, v___x_4709_);
v_i_4699_ = v___x_4710_;
v_b_4701_ = v_a_4708_;
goto _start;
}
else
{
return v___x_4707_;
}
}
else
{
lean_object* v___x_4712_; 
v___x_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4712_, 0, v_b_4701_);
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4713_, lean_object* v_i_4714_, lean_object* v_stop_4715_, lean_object* v_b_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
size_t v_i_boxed_4720_; size_t v_stop_boxed_4721_; lean_object* v_res_4722_; 
v_i_boxed_4720_ = lean_unbox_usize(v_i_4714_);
lean_dec(v_i_4714_);
v_stop_boxed_4721_ = lean_unbox_usize(v_stop_4715_);
lean_dec(v_stop_4715_);
v_res_4722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4713_, v_i_boxed_4720_, v_stop_boxed_4721_, v_b_4716_, v___y_4717_, v___y_4718_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v_as_4713_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4723_, lean_object* v_toUpdate_4724_, lean_object* v_leanOpts_4725_, uint8_t v_updateToolchain_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4727_, v_ws_4723_, v_toUpdate_4724_, v_leanOpts_4725_, v_updateToolchain_4726_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v_fst_4731_; lean_object* v_snd_4732_; lean_object* v___y_4734_; lean_object* v___x_4751_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4729_, 1);
v_fst_4731_ = lean_ctor_get(v_a_4730_, 0);
lean_inc(v_fst_4731_);
v_snd_4732_ = lean_ctor_get(v_a_4730_, 1);
lean_inc(v_snd_4732_);
lean_dec(v_a_4730_);
v___x_4751_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4731_, v_snd_4732_);
lean_dec(v_snd_4732_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4773_; 
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4773_ == 0)
{
lean_object* v_unused_4774_; 
v_unused_4774_ = lean_ctor_get(v___x_4751_, 0);
lean_dec(v_unused_4774_);
v___x_4753_ = v___x_4751_;
v_isShared_4754_ = v_isSharedCheck_4773_;
goto v_resetjp_4752_;
}
else
{
lean_dec(v___x_4751_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4773_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v_packages_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v_packages_4755_ = lean_ctor_get(v_fst_4731_, 4);
v___x_4756_ = lean_unsigned_to_nat(0u);
v___x_4757_ = lean_array_get_size(v_packages_4755_);
v___x_4758_ = lean_nat_dec_lt(v___x_4756_, v___x_4757_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4760_; 
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 0, v_fst_4731_);
v___x_4760_ = v___x_4753_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_fst_4731_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
else
{
lean_object* v___x_4762_; uint8_t v___x_4763_; 
v___x_4762_ = lean_box(0);
v___x_4763_ = lean_nat_dec_le(v___x_4757_, v___x_4757_);
if (v___x_4763_ == 0)
{
if (v___x_4758_ == 0)
{
lean_object* v___x_4765_; 
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 0, v_fst_4731_);
v___x_4765_ = v___x_4753_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_fst_4731_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
else
{
size_t v___x_4767_; size_t v___x_4768_; lean_object* v___x_4769_; 
lean_del_object(v___x_4753_);
v___x_4767_ = ((size_t)0ULL);
v___x_4768_ = lean_usize_of_nat(v___x_4757_);
v___x_4769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4755_, v___x_4767_, v___x_4768_, v___x_4762_, v_fst_4731_, v_a_4727_);
v___y_4734_ = v___x_4769_;
goto v___jp_4733_;
}
}
else
{
size_t v___x_4770_; size_t v___x_4771_; lean_object* v___x_4772_; 
lean_del_object(v___x_4753_);
v___x_4770_ = ((size_t)0ULL);
v___x_4771_ = lean_usize_of_nat(v___x_4757_);
v___x_4772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4755_, v___x_4770_, v___x_4771_, v___x_4762_, v_fst_4731_, v_a_4727_);
v___y_4734_ = v___x_4772_;
goto v___jp_4733_;
}
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4787_; 
lean_dec(v_fst_4731_);
v_a_4775_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4777_ = v___x_4751_;
v_isShared_4778_ = v_isSharedCheck_4787_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4751_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4787_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4779_; uint8_t v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4779_ = lean_io_error_to_string(v_a_4775_);
v___x_4780_ = 3;
v___x_4781_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4781_, 0, v___x_4779_);
lean_ctor_set_uint8(v___x_4781_, sizeof(void*)*1, v___x_4780_);
lean_inc_ref(v_a_4727_);
v___x_4782_ = lean_apply_2(v_a_4727_, v___x_4781_, lean_box(0));
v___x_4783_ = lean_box(0);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4783_);
v___x_4785_ = v___x_4777_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
v___jp_4733_:
{
if (lean_obj_tag(v___y_4734_) == 0)
{
lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
v_isSharedCheck_4741_ = !lean_is_exclusive(v___y_4734_);
if (v_isSharedCheck_4741_ == 0)
{
lean_object* v_unused_4742_; 
v_unused_4742_ = lean_ctor_get(v___y_4734_, 0);
lean_dec(v_unused_4742_);
v___x_4736_ = v___y_4734_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_dec(v___y_4734_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 0, v_fst_4731_);
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_fst_4731_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
lean_dec(v_fst_4731_);
v_a_4743_ = lean_ctor_get(v___y_4734_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___y_4734_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___y_4734_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___y_4734_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
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
else
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4795_; 
v_a_4788_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4790_ = v___x_4729_;
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4729_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4793_; 
if (v_isShared_4791_ == 0)
{
v___x_4793_ = v___x_4790_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4788_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4796_, lean_object* v_toUpdate_4797_, lean_object* v_leanOpts_4798_, lean_object* v_updateToolchain_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
uint8_t v_updateToolchain_boxed_4802_; lean_object* v_res_4803_; 
v_updateToolchain_boxed_4802_ = lean_unbox(v_updateToolchain_4799_);
v_res_4803_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4796_, v_toUpdate_4797_, v_leanOpts_4798_, v_updateToolchain_boxed_4802_, v_a_4800_);
lean_dec_ref(v_a_4800_);
lean_dec(v_toUpdate_4797_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4808_, lean_object* v_what_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_name_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; 
v_name_4812_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_name_4812_);
lean_dec_ref(v___x_4808_);
v___x_4813_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4814_ = lean_string_append(v___x_4813_, v_what_4809_);
v___x_4815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4816_ = lean_string_append(v___x_4814_, v___x_4815_);
v___x_4817_ = 1;
v___x_4818_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4812_, v___x_4817_);
v___x_4819_ = lean_string_append(v___x_4816_, v___x_4818_);
v___x_4820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4821_ = lean_string_append(v___x_4819_, v___x_4820_);
v___x_4822_ = lean_string_append(v___x_4821_, v___x_4818_);
lean_dec_ref(v___x_4818_);
v___x_4823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4824_ = lean_string_append(v___x_4822_, v___x_4823_);
v___x_4825_ = 2;
v___x_4826_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4826_, 0, v___x_4824_);
lean_ctor_set_uint8(v___x_4826_, sizeof(void*)*1, v___x_4825_);
lean_inc_ref(v___y_4810_);
v___x_4827_ = lean_apply_2(v___y_4810_, v___x_4826_, lean_box(0));
v___x_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4827_);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4829_, lean_object* v_what_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4829_, v_what_4830_, v___y_4831_);
lean_dec_ref(v___y_4831_);
lean_dec_ref(v_what_4830_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4837_, lean_object* v_as_4838_, size_t v_i_4839_, size_t v_stop_4840_, lean_object* v_b_4841_, lean_object* v___y_4842_){
_start:
{
lean_object* v_a_4845_; lean_object* v___y_4850_; uint8_t v___x_4852_; 
v___x_4852_ = lean_usize_dec_eq(v_i_4839_, v_stop_4840_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; lean_object* v_src_x3f_4854_; 
v___x_4853_ = lean_array_uget_borrowed(v_as_4838_, v_i_4839_);
v_src_x3f_4854_ = lean_ctor_get(v___x_4853_, 3);
if (lean_obj_tag(v_src_x3f_4854_) == 1)
{
lean_object* v_name_4855_; lean_object* v_val_4856_; lean_object* v___x_4857_; 
v_name_4855_ = lean_ctor_get(v___x_4853_, 0);
v_val_4856_ = lean_ctor_get(v_src_x3f_4854_, 0);
v___x_4857_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4837_, v_name_4855_);
if (lean_obj_tag(v___x_4857_) == 1)
{
lean_object* v_val_4858_; lean_object* v___y_4860_; lean_object* v___y_4864_; 
v_val_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_val_4858_);
lean_dec_ref_known(v___x_4857_, 1);
if (lean_obj_tag(v_val_4856_) == 0)
{
lean_object* v_src_4867_; 
v_src_4867_ = lean_ctor_get(v_val_4858_, 4);
lean_inc_ref(v_src_4867_);
lean_dec(v_val_4858_);
if (lean_obj_tag(v_src_4867_) == 0)
{
lean_object* v___x_4868_; 
lean_dec_ref_known(v_src_4867_, 1);
v___x_4868_ = lean_box(0);
v_a_4845_ = v___x_4868_;
goto v___jp_4844_;
}
else
{
lean_dec_ref(v_src_4867_);
v___y_4864_ = v___y_4842_;
goto v___jp_4863_;
}
}
else
{
lean_object* v_src_4869_; 
v_src_4869_ = lean_ctor_get(v_val_4858_, 4);
lean_inc_ref(v_src_4869_);
lean_dec(v_val_4858_);
if (lean_obj_tag(v_src_4869_) == 1)
{
lean_object* v_url_4870_; lean_object* v_rev_4871_; lean_object* v_url_4872_; lean_object* v_inputRev_x3f_4873_; lean_object* v___y_4875_; uint8_t v___x_4882_; 
v_url_4870_ = lean_ctor_get(v_val_4856_, 0);
v_rev_4871_ = lean_ctor_get(v_val_4856_, 1);
v_url_4872_ = lean_ctor_get(v_src_4869_, 0);
lean_inc_ref(v_url_4872_);
v_inputRev_x3f_4873_ = lean_ctor_get(v_src_4869_, 2);
lean_inc(v_inputRev_x3f_4873_);
lean_dec_ref_known(v_src_4869_, 4);
v___x_4882_ = lean_string_dec_eq(v_url_4870_, v_url_4872_);
lean_dec_ref(v_url_4872_);
if (v___x_4882_ == 0)
{
goto v___jp_4879_;
}
else
{
if (v___x_4852_ == 0)
{
v___y_4875_ = v___y_4842_;
goto v___jp_4874_;
}
else
{
goto v___jp_4879_;
}
}
v___jp_4874_:
{
lean_object* v___x_4876_; uint8_t v___x_4877_; 
v___x_4876_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4871_);
v___x_4877_ = l_Option_instDecidableEq___redArg(v___x_4876_, v_rev_4871_, v_inputRev_x3f_4873_);
if (v___x_4877_ == 0)
{
v___y_4860_ = v___y_4875_;
goto v___jp_4859_;
}
else
{
if (v___x_4852_ == 0)
{
lean_object* v___x_4878_; 
v___x_4878_ = lean_box(0);
v_a_4845_ = v___x_4878_;
goto v___jp_4844_;
}
else
{
v___y_4860_ = v___y_4875_;
goto v___jp_4859_;
}
}
}
v___jp_4879_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_4853_);
v___x_4881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4853_, v___x_4880_, v___y_4842_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_dec_ref_known(v___x_4881_, 1);
v___y_4875_ = v___y_4842_;
goto v___jp_4874_;
}
else
{
lean_dec(v_inputRev_x3f_4873_);
return v___x_4881_;
}
}
}
else
{
lean_dec_ref(v_src_4869_);
v___y_4864_ = v___y_4842_;
goto v___jp_4863_;
}
}
v___jp_4859_:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_4853_);
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4853_, v___x_4861_, v___y_4860_);
v___y_4850_ = v___x_4862_;
goto v___jp_4849_;
}
v___jp_4863_:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_4853_);
v___x_4866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4853_, v___x_4865_, v___y_4864_);
v___y_4850_ = v___x_4866_;
goto v___jp_4849_;
}
}
else
{
lean_object* v___x_4883_; 
lean_dec(v___x_4857_);
v___x_4883_ = lean_box(0);
v_a_4845_ = v___x_4883_;
goto v___jp_4844_;
}
}
else
{
lean_object* v___x_4884_; 
v___x_4884_ = lean_box(0);
v_a_4845_ = v___x_4884_;
goto v___jp_4844_;
}
}
else
{
lean_object* v___x_4885_; 
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_b_4841_);
return v___x_4885_;
}
v___jp_4844_:
{
size_t v___x_4846_; size_t v___x_4847_; 
v___x_4846_ = ((size_t)1ULL);
v___x_4847_ = lean_usize_add(v_i_4839_, v___x_4846_);
v_i_4839_ = v___x_4847_;
v_b_4841_ = v_a_4845_;
goto _start;
}
v___jp_4849_:
{
if (lean_obj_tag(v___y_4850_) == 0)
{
lean_object* v_a_4851_; 
v_a_4851_ = lean_ctor_get(v___y_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref_known(v___y_4850_, 1);
v_a_4845_ = v_a_4851_;
goto v___jp_4844_;
}
else
{
return v___y_4850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4886_, lean_object* v_as_4887_, lean_object* v_i_4888_, lean_object* v_stop_4889_, lean_object* v_b_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_){
_start:
{
size_t v_i_boxed_4893_; size_t v_stop_boxed_4894_; lean_object* v_res_4895_; 
v_i_boxed_4893_ = lean_unbox_usize(v_i_4888_);
lean_dec(v_i_4888_);
v_stop_boxed_4894_ = lean_unbox_usize(v_stop_4889_);
lean_dec(v_stop_4889_);
v_res_4895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4886_, v_as_4887_, v_i_boxed_4893_, v_stop_boxed_4894_, v_b_4890_, v___y_4891_);
lean_dec_ref(v___y_4891_);
lean_dec_ref(v_as_4887_);
lean_dec(v_pkgEntries_4886_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4896_, lean_object* v_deps_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; uint8_t v___x_4903_; 
v___x_4900_ = lean_unsigned_to_nat(0u);
v___x_4901_ = lean_array_get_size(v_deps_4897_);
v___x_4902_ = lean_box(0);
v___x_4903_ = lean_nat_dec_lt(v___x_4900_, v___x_4901_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; 
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4902_);
return v___x_4904_;
}
else
{
uint8_t v___x_4905_; 
v___x_4905_ = lean_nat_dec_le(v___x_4901_, v___x_4901_);
if (v___x_4905_ == 0)
{
if (v___x_4903_ == 0)
{
lean_object* v___x_4906_; 
v___x_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4902_);
return v___x_4906_;
}
else
{
size_t v___x_4907_; size_t v___x_4908_; lean_object* v___x_4909_; 
v___x_4907_ = ((size_t)0ULL);
v___x_4908_ = lean_usize_of_nat(v___x_4901_);
v___x_4909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4896_, v_deps_4897_, v___x_4907_, v___x_4908_, v___x_4902_, v_a_4898_);
return v___x_4909_;
}
}
else
{
size_t v___x_4910_; size_t v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = ((size_t)0ULL);
v___x_4911_ = lean_usize_of_nat(v___x_4901_);
v___x_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4896_, v_deps_4897_, v___x_4910_, v___x_4911_, v___x_4902_, v_a_4898_);
return v___x_4912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_4913_, lean_object* v_deps_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_4913_, v_deps_4914_, v_a_4915_);
lean_dec_ref(v_a_4915_);
lean_dec_ref(v_deps_4914_);
lean_dec(v_pkgEntries_4913_);
return v_res_4917_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_4918_, lean_object* v_x_4919_){
_start:
{
if (lean_obj_tag(v_x_4918_) == 0)
{
if (lean_obj_tag(v_x_4919_) == 0)
{
uint8_t v___x_4920_; 
v___x_4920_ = 1;
return v___x_4920_;
}
else
{
uint8_t v___x_4921_; 
v___x_4921_ = 0;
return v___x_4921_;
}
}
else
{
if (lean_obj_tag(v_x_4919_) == 0)
{
uint8_t v___x_4922_; 
v___x_4922_ = 0;
return v___x_4922_;
}
else
{
lean_object* v_val_4923_; lean_object* v_val_4924_; uint8_t v___x_4925_; 
v_val_4923_ = lean_ctor_get(v_x_4918_, 0);
v_val_4924_ = lean_ctor_get(v_x_4919_, 0);
v___x_4925_ = lean_string_dec_eq(v_val_4923_, v_val_4924_);
return v___x_4925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_4926_, lean_object* v_x_4927_){
_start:
{
uint8_t v_res_4928_; lean_object* v_r_4929_; 
v_res_4928_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_4926_, v_x_4927_);
lean_dec(v_x_4927_);
lean_dec(v_x_4926_);
v_r_4929_ = lean_box(v_res_4928_);
return v_r_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_pkg_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v_leanOpts_4938_, uint8_t v_reconfigure_4939_, lean_object* v_as_4940_, size_t v_i_4941_, size_t v_stop_4942_, lean_object* v_b_4943_, lean_object* v___y_4944_){
_start:
{
uint8_t v___x_4949_; 
v___x_4949_ = lean_usize_dec_eq(v_i_4941_, v_stop_4942_);
if (v___x_4949_ == 0)
{
lean_object* v_ws_4950_; lean_object* v_depIdxs_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_5099_; 
v_ws_4950_ = lean_ctor_get(v_b_4943_, 0);
v_depIdxs_4951_ = lean_ctor_get(v_b_4943_, 1);
v_isSharedCheck_5099_ = !lean_is_exclusive(v_b_4943_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_4953_ = v_b_4943_;
v_isShared_4954_ = v_isSharedCheck_5099_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_depIdxs_4951_);
lean_inc(v_ws_4950_);
lean_dec(v_b_4943_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_5099_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v_lakeEnv_4955_; lean_object* v_packages_4956_; size_t v___x_4957_; size_t v___x_4958_; lean_object* v___x_4959_; lean_object* v___f_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v_lakeEnv_4955_ = lean_ctor_get(v_ws_4950_, 0);
v_packages_4956_ = lean_ctor_get(v_ws_4950_, 4);
v___x_4957_ = ((size_t)1ULL);
v___x_4958_ = lean_usize_sub(v_i_4941_, v___x_4957_);
v___x_4959_ = lean_array_uget_borrowed(v_as_4940_, v___x_4958_);
lean_inc(v___x_4959_);
v___f_4960_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4960_, 0, v___x_4959_);
v___x_4961_ = lean_unsigned_to_nat(0u);
v___x_4962_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4960_, v_packages_4956_, v___x_4961_);
if (lean_obj_tag(v___x_4962_) == 1)
{
lean_object* v_val_4963_; lean_object* v___x_4964_; lean_object* v___x_4966_; 
v_val_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc(v_val_4963_);
lean_dec_ref_known(v___x_4962_, 1);
v___x_4964_ = lean_array_push(v_depIdxs_4951_, v_val_4963_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_4964_);
v___x_4966_ = v___x_4953_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_ws_4950_);
lean_ctor_set(v_reuseFailAlloc_4968_, 1, v___x_4964_);
v___x_4966_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
v_i_4941_ = v___x_4958_;
v_b_4943_ = v___x_4966_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_4969_; lean_object* v_baseName_4970_; lean_object* v_name_4971_; lean_object* v_opts_4972_; uint8_t v___x_4973_; 
lean_inc_ref(v_packages_4956_);
lean_dec(v___x_4962_);
v_wsIdx_4969_ = lean_ctor_get(v_pkg_4935_, 0);
v_baseName_4970_ = lean_ctor_get(v_pkg_4935_, 1);
v_name_4971_ = lean_ctor_get(v___x_4959_, 0);
v_opts_4972_ = lean_ctor_get(v___x_4959_, 4);
v___x_4973_ = lean_name_eq(v_baseName_4970_, v_name_4971_);
if (v___x_4973_ == 0)
{
lean_object* v___x_4974_; 
v___x_4974_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_4936_, v_name_4971_);
if (lean_obj_tag(v___x_4974_) == 1)
{
lean_object* v_val_4975_; lean_object* v___x_4976_; lean_object* v_dir_4977_; lean_object* v___x_4978_; 
v_val_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_val_4975_);
lean_dec_ref_known(v___x_4974_, 1);
v___x_4976_ = lean_array_fget_borrowed(v_packages_4956_, v___x_4961_);
v_dir_4977_ = lean_ctor_get(v___x_4976_, 4);
lean_inc_ref(v___y_4937_);
lean_inc_ref(v_dir_4977_);
v___x_4978_ = l_Lake_PackageEntry_materialize(v_val_4975_, v_lakeEnv_4955_, v_dir_4977_, v___y_4937_, v___y_4944_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5053_; 
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_4981_ = v___x_4978_;
v_isShared_4982_ = v_isSharedCheck_5053_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4978_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5053_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4983_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4938_);
lean_inc(v_opts_4972_);
v___x_4984_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4950_, v_a_4979_, v_opts_4972_, v_leanOpts_4938_, v_reconfigure_4939_, v___x_4983_);
if (lean_obj_tag(v___x_4984_) == 0)
{
lean_object* v_a_4985_; lean_object* v_a_4986_; lean_object* v_wsIdx_4987_; lean_object* v___x_4988_; lean_object* v___x_4990_; 
lean_del_object(v___x_4981_);
v_a_4985_ = lean_ctor_get(v___x_4984_, 0);
lean_inc(v_a_4985_);
v_a_4986_ = lean_ctor_get(v___x_4984_, 1);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___x_4984_, 2);
v_wsIdx_4987_ = lean_array_get_size(v_packages_4956_);
lean_dec_ref(v_packages_4956_);
v___x_4988_ = lean_array_push(v_depIdxs_4951_, v_wsIdx_4987_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 1, v___x_4988_);
lean_ctor_set(v___x_4953_, 0, v_a_4985_);
v___x_4990_ = v___x_4953_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_4985_);
lean_ctor_set(v_reuseFailAlloc_5021_, 1, v___x_4988_);
v___x_4990_ = v_reuseFailAlloc_5021_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
lean_object* v___x_4991_; uint8_t v___x_4992_; 
v___x_4991_ = lean_array_get_size(v_a_4986_);
v___x_4992_ = lean_nat_dec_lt(v___x_4961_, v___x_4991_);
if (v___x_4992_ == 0)
{
lean_dec(v_a_4986_);
v_i_4941_ = v___x_4958_;
v_b_4943_ = v___x_4990_;
goto _start;
}
else
{
lean_object* v___x_4994_; uint8_t v___x_4995_; 
v___x_4994_ = lean_box(0);
v___x_4995_ = lean_nat_dec_le(v___x_4991_, v___x_4991_);
if (v___x_4995_ == 0)
{
if (v___x_4992_ == 0)
{
lean_dec(v_a_4986_);
v_i_4941_ = v___x_4958_;
v_b_4943_ = v___x_4990_;
goto _start;
}
else
{
size_t v___x_4997_; size_t v___x_4998_; lean_object* v___x_4999_; 
v___x_4997_ = ((size_t)0ULL);
v___x_4998_ = lean_usize_of_nat(v___x_4991_);
v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4986_, v___x_4997_, v___x_4998_, v___x_4994_, v___y_4944_);
lean_dec(v_a_4986_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_dec_ref_known(v___x_4999_, 1);
v_i_4941_ = v___x_4958_;
v_b_4943_ = v___x_4990_;
goto _start;
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
lean_dec_ref(v___x_4990_);
lean_dec_ref(v_leanOpts_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_pkg_4935_);
v_a_5001_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___x_4999_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_4999_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
}
else
{
size_t v___x_5009_; size_t v___x_5010_; lean_object* v___x_5011_; 
v___x_5009_ = ((size_t)0ULL);
v___x_5010_ = lean_usize_of_nat(v___x_4991_);
v___x_5011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4986_, v___x_5009_, v___x_5010_, v___x_4994_, v___y_4944_);
lean_dec(v_a_4986_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_dec_ref_known(v___x_5011_, 1);
v_i_4941_ = v___x_4958_;
v_b_4943_ = v___x_4990_;
goto _start;
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec_ref(v___x_4990_);
lean_dec_ref(v_leanOpts_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_pkg_4935_);
v_a_5013_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_5011_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5011_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5023_; uint8_t v___x_5024_; 
lean_dec_ref(v_packages_4956_);
lean_del_object(v___x_4953_);
lean_dec_ref(v_depIdxs_4951_);
lean_dec_ref(v_leanOpts_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_pkg_4935_);
v_a_5022_ = lean_ctor_get(v___x_4984_, 1);
lean_inc(v_a_5022_);
lean_dec_ref_known(v___x_4984_, 2);
v___x_5023_ = lean_array_get_size(v_a_5022_);
v___x_5024_ = lean_nat_dec_lt(v___x_4961_, v___x_5023_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5025_; lean_object* v___x_5027_; 
lean_dec(v_a_5022_);
v___x_5025_ = lean_box(0);
if (v_isShared_4982_ == 0)
{
lean_ctor_set_tag(v___x_4981_, 1);
lean_ctor_set(v___x_4981_, 0, v___x_5025_);
v___x_5027_ = v___x_4981_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
else
{
lean_object* v___x_5029_; uint8_t v___x_5030_; 
lean_del_object(v___x_4981_);
v___x_5029_ = lean_box(0);
v___x_5030_ = lean_nat_dec_le(v___x_5023_, v___x_5023_);
if (v___x_5030_ == 0)
{
if (v___x_5024_ == 0)
{
lean_dec(v_a_5022_);
goto v___jp_4946_;
}
else
{
size_t v___x_5031_; size_t v___x_5032_; lean_object* v___x_5033_; 
v___x_5031_ = ((size_t)0ULL);
v___x_5032_ = lean_usize_of_nat(v___x_5023_);
v___x_5033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5022_, v___x_5031_, v___x_5032_, v___x_5029_, v___y_4944_);
lean_dec(v_a_5022_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_dec_ref_known(v___x_5033_, 1);
goto v___jp_4946_;
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_5033_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_5033_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
}
else
{
size_t v___x_5042_; size_t v___x_5043_; lean_object* v___x_5044_; 
v___x_5042_ = ((size_t)0ULL);
v___x_5043_ = lean_usize_of_nat(v___x_5023_);
v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5022_, v___x_5042_, v___x_5043_, v___x_5029_, v___y_4944_);
lean_dec(v_a_5022_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_dec_ref_known(v___x_5044_, 1);
goto v___jp_4946_;
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5044_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
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
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5061_; 
lean_dec_ref(v_packages_4956_);
lean_del_object(v___x_4953_);
lean_dec_ref(v_depIdxs_4951_);
lean_dec_ref(v_ws_4950_);
lean_dec_ref(v_leanOpts_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_pkg_4935_);
v_a_5054_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_5061_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_5061_ == 0)
{
v___x_5056_ = v___x_4978_;
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v___x_4978_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5061_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
}
}
else
{
uint8_t v___x_5062_; 
lean_inc(v_baseName_4970_);
lean_inc(v_wsIdx_4969_);
lean_dec(v___x_4974_);
lean_dec_ref(v_packages_4956_);
lean_del_object(v___x_4953_);
lean_dec_ref(v_depIdxs_4951_);
lean_dec_ref(v_ws_4950_);
lean_dec_ref(v_leanOpts_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_pkg_4935_);
v___x_5062_ = lean_nat_dec_eq(v_wsIdx_4969_, v___x_4961_);
lean_dec(v_wsIdx_4969_);
if (v___x_5062_ == 0)
{
lean_object* v___x_5063_; uint8_t v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; uint8_t v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5064_ = 1;
lean_inc(v_name_4971_);
v___x_5065_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4971_, v___x_5064_);
v___x_5066_ = lean_string_append(v___x_5063_, v___x_5065_);
lean_dec_ref(v___x_5065_);
v___x_5067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5068_ = lean_string_append(v___x_5066_, v___x_5067_);
v___x_5069_ = l_Lean_Name_toString(v_baseName_4970_, v___x_5062_);
v___x_5070_ = lean_string_append(v___x_5068_, v___x_5069_);
lean_dec_ref(v___x_5069_);
v___x_5071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5072_ = lean_string_append(v___x_5070_, v___x_5071_);
v___x_5073_ = 3;
v___x_5074_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5074_, 0, v___x_5072_);
lean_ctor_set_uint8(v___x_5074_, sizeof(void*)*1, v___x_5073_);
lean_inc_ref(v___y_4944_);
v___x_5075_ = lean_apply_2(v___y_4944_, v___x_5074_, lean_box(0));
v___x_5076_ = lean_box(0);
v___x_5077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
return v___x_5077_;
}
else
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; uint8_t v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; 
lean_dec(v_baseName_4970_);
v___x_5078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_4971_);
v___x_5079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4971_, v___x_5062_);
v___x_5080_ = lean_string_append(v___x_5078_, v___x_5079_);
v___x_5081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5082_ = lean_string_append(v___x_5080_, v___x_5081_);
v___x_5083_ = lean_string_append(v___x_5082_, v___x_5079_);
lean_dec_ref(v___x_5079_);
v___x_5084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5085_ = lean_string_append(v___x_5083_, v___x_5084_);
v___x_5086_ = 3;
v___x_5087_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5087_, 0, v___x_5085_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*1, v___x_5086_);
lean_inc_ref(v___y_4944_);
v___x_5088_ = lean_apply_2(v___y_4944_, v___x_5087_, lean_box(0));
v___x_5089_ = lean_box(0);
v___x_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5089_);
return v___x_5090_;
}
}
}
else
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; uint8_t v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
lean_inc(v_baseName_4970_);
lean_dec_ref(v_packages_4956_);
lean_del_object(v___x_4953_);
lean_dec_ref(v_depIdxs_4951_);
lean_dec_ref(v_ws_4950_);
lean_dec_ref(v_leanOpts_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_pkg_4935_);
v___x_5091_ = l_Lean_Name_toString(v_baseName_4970_, v___x_4949_);
v___x_5092_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5093_ = lean_string_append(v___x_5091_, v___x_5092_);
v___x_5094_ = 3;
v___x_5095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5095_, 0, v___x_5093_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*1, v___x_5094_);
lean_inc_ref(v___y_4944_);
v___x_5096_ = lean_apply_2(v___y_4944_, v___x_5095_, lean_box(0));
v___x_5097_ = lean_box(0);
v___x_5098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5098_, 0, v___x_5097_);
return v___x_5098_;
}
}
}
}
else
{
lean_object* v___x_5100_; 
lean_dec_ref(v_leanOpts_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_pkg_4935_);
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v_b_4943_);
return v___x_5100_;
}
v___jp_4946_:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4947_ = lean_box(0);
v___x_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4947_);
return v___x_4948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_pkg_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v_leanOpts_5104_, lean_object* v_reconfigure_5105_, lean_object* v_as_5106_, lean_object* v_i_5107_, lean_object* v_stop_5108_, lean_object* v_b_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
uint8_t v_reconfigure_boxed_5112_; size_t v_i_boxed_5113_; size_t v_stop_boxed_5114_; lean_object* v_res_5115_; 
v_reconfigure_boxed_5112_ = lean_unbox(v_reconfigure_5105_);
v_i_boxed_5113_ = lean_unbox_usize(v_i_5107_);
lean_dec(v_i_5107_);
v_stop_boxed_5114_ = lean_unbox_usize(v_stop_5108_);
lean_dec(v_stop_5108_);
v_res_5115_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5101_, v___y_5102_, v___y_5103_, v_leanOpts_5104_, v_reconfigure_boxed_5112_, v_as_5106_, v_i_boxed_5113_, v_stop_boxed_5114_, v_b_5109_, v___y_5110_);
lean_dec_ref(v___y_5110_);
lean_dec_ref(v_as_5106_);
lean_dec(v___y_5102_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_start_5116_, lean_object* v_pkg_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v_leanOpts_5120_, uint8_t v_reconfigure_5121_, lean_object* v_as_5122_, size_t v_i_5123_, size_t v_stop_5124_, lean_object* v_b_5125_, lean_object* v___y_5126_){
_start:
{
uint8_t v___x_5131_; 
v___x_5131_ = lean_usize_dec_eq(v_i_5123_, v_stop_5124_);
if (v___x_5131_ == 0)
{
lean_object* v_ws_5132_; lean_object* v_depIdxs_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5281_; 
v_ws_5132_ = lean_ctor_get(v_b_5125_, 0);
v_depIdxs_5133_ = lean_ctor_get(v_b_5125_, 1);
v_isSharedCheck_5281_ = !lean_is_exclusive(v_b_5125_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5135_ = v_b_5125_;
v_isShared_5136_ = v_isSharedCheck_5281_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_depIdxs_5133_);
lean_inc(v_ws_5132_);
lean_dec(v_b_5125_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5281_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v_lakeEnv_5137_; lean_object* v_packages_5138_; size_t v___x_5139_; size_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___f_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v_lakeEnv_5137_ = lean_ctor_get(v_ws_5132_, 0);
v_packages_5138_ = lean_ctor_get(v_ws_5132_, 4);
v___x_5139_ = ((size_t)1ULL);
v___x_5140_ = lean_usize_sub(v_i_5123_, v___x_5139_);
v___x_5141_ = lean_array_uget_borrowed(v_as_5122_, v___x_5140_);
lean_inc(v___x_5141_);
v___f_5142_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5142_, 0, v___x_5141_);
v___x_5143_ = lean_unsigned_to_nat(0u);
v___x_5144_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5142_, v_packages_5138_, v___x_5143_);
if (lean_obj_tag(v___x_5144_) == 1)
{
lean_object* v_val_5145_; lean_object* v___x_5146_; lean_object* v___x_5148_; 
v_val_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_val_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5146_ = lean_array_push(v_depIdxs_5133_, v_val_5145_);
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 1, v___x_5146_);
v___x_5148_ = v___x_5135_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_ws_5132_);
lean_ctor_set(v_reuseFailAlloc_5150_, 1, v___x_5146_);
v___x_5148_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5117_, v___y_5118_, v___y_5119_, v_leanOpts_5120_, v_reconfigure_5121_, v_as_5122_, v___x_5140_, v_stop_5124_, v___x_5148_, v___y_5126_);
return v___x_5149_;
}
}
else
{
lean_object* v_wsIdx_5151_; lean_object* v_baseName_5152_; lean_object* v_name_5153_; lean_object* v_opts_5154_; uint8_t v___x_5155_; 
lean_inc_ref(v_packages_5138_);
lean_dec(v___x_5144_);
v_wsIdx_5151_ = lean_ctor_get(v_pkg_5117_, 0);
v_baseName_5152_ = lean_ctor_get(v_pkg_5117_, 1);
v_name_5153_ = lean_ctor_get(v___x_5141_, 0);
v_opts_5154_ = lean_ctor_get(v___x_5141_, 4);
v___x_5155_ = lean_name_eq(v_baseName_5152_, v_name_5153_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5156_; 
v___x_5156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5118_, v_name_5153_);
if (lean_obj_tag(v___x_5156_) == 1)
{
lean_object* v_val_5157_; lean_object* v___x_5158_; lean_object* v_dir_5159_; lean_object* v___x_5160_; 
v_val_5157_ = lean_ctor_get(v___x_5156_, 0);
lean_inc(v_val_5157_);
lean_dec_ref_known(v___x_5156_, 1);
v___x_5158_ = lean_array_fget_borrowed(v_packages_5138_, v___x_5143_);
v_dir_5159_ = lean_ctor_get(v___x_5158_, 4);
lean_inc_ref(v___y_5119_);
lean_inc_ref(v_dir_5159_);
v___x_5160_ = l_Lake_PackageEntry_materialize(v_val_5157_, v_lakeEnv_5137_, v_dir_5159_, v___y_5119_, v___y_5126_);
if (lean_obj_tag(v___x_5160_) == 0)
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5235_; 
v_a_5161_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5163_ = v___x_5160_;
v_isShared_5164_ = v_isSharedCheck_5235_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5160_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5235_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5120_);
lean_inc(v_opts_5154_);
v___x_5166_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5132_, v_a_5161_, v_opts_5154_, v_leanOpts_5120_, v_reconfigure_5121_, v___x_5165_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v_a_5168_; lean_object* v_wsIdx_5169_; lean_object* v___x_5170_; lean_object* v___x_5172_; 
lean_del_object(v___x_5163_);
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
v_a_5168_ = lean_ctor_get(v___x_5166_, 1);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5166_, 2);
v_wsIdx_5169_ = lean_array_get_size(v_packages_5138_);
lean_dec_ref(v_packages_5138_);
v___x_5170_ = lean_array_push(v_depIdxs_5133_, v_wsIdx_5169_);
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 1, v___x_5170_);
lean_ctor_set(v___x_5135_, 0, v_a_5167_);
v___x_5172_ = v___x_5135_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5167_);
lean_ctor_set(v_reuseFailAlloc_5203_, 1, v___x_5170_);
v___x_5172_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
lean_object* v___x_5173_; uint8_t v___x_5174_; 
v___x_5173_ = lean_array_get_size(v_a_5168_);
v___x_5174_ = lean_nat_dec_lt(v___x_5143_, v___x_5173_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; 
lean_dec(v_a_5168_);
v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5117_, v___y_5118_, v___y_5119_, v_leanOpts_5120_, v_reconfigure_5121_, v_as_5122_, v___x_5140_, v_stop_5124_, v___x_5172_, v___y_5126_);
return v___x_5175_;
}
else
{
lean_object* v___x_5176_; uint8_t v___x_5177_; 
v___x_5176_ = lean_box(0);
v___x_5177_ = lean_nat_dec_le(v___x_5173_, v___x_5173_);
if (v___x_5177_ == 0)
{
if (v___x_5174_ == 0)
{
lean_object* v___x_5178_; 
lean_dec(v_a_5168_);
v___x_5178_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5117_, v___y_5118_, v___y_5119_, v_leanOpts_5120_, v_reconfigure_5121_, v_as_5122_, v___x_5140_, v_stop_5124_, v___x_5172_, v___y_5126_);
return v___x_5178_;
}
else
{
size_t v___x_5179_; size_t v___x_5180_; lean_object* v___x_5181_; 
v___x_5179_ = ((size_t)0ULL);
v___x_5180_ = lean_usize_of_nat(v___x_5173_);
v___x_5181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5168_, v___x_5179_, v___x_5180_, v___x_5176_, v___y_5126_);
lean_dec(v_a_5168_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v___x_5182_; 
lean_dec_ref_known(v___x_5181_, 1);
v___x_5182_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5117_, v___y_5118_, v___y_5119_, v_leanOpts_5120_, v_reconfigure_5121_, v_as_5122_, v___x_5140_, v_stop_5124_, v___x_5172_, v___y_5126_);
return v___x_5182_;
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec_ref(v___x_5172_);
lean_dec_ref(v_leanOpts_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_pkg_5117_);
v_a_5183_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5181_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5181_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
}
else
{
size_t v___x_5191_; size_t v___x_5192_; lean_object* v___x_5193_; 
v___x_5191_ = ((size_t)0ULL);
v___x_5192_ = lean_usize_of_nat(v___x_5173_);
v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5168_, v___x_5191_, v___x_5192_, v___x_5176_, v___y_5126_);
lean_dec(v_a_5168_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v___x_5194_; 
lean_dec_ref_known(v___x_5193_, 1);
v___x_5194_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5117_, v___y_5118_, v___y_5119_, v_leanOpts_5120_, v_reconfigure_5121_, v_as_5122_, v___x_5140_, v_stop_5124_, v___x_5172_, v___y_5126_);
return v___x_5194_;
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec_ref(v___x_5172_);
lean_dec_ref(v_leanOpts_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_pkg_5117_);
v_a_5195_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5193_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5193_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5204_; lean_object* v___x_5205_; uint8_t v___x_5206_; 
lean_dec_ref(v_packages_5138_);
lean_del_object(v___x_5135_);
lean_dec_ref(v_depIdxs_5133_);
lean_dec_ref(v_leanOpts_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_pkg_5117_);
v_a_5204_ = lean_ctor_get(v___x_5166_, 1);
lean_inc(v_a_5204_);
lean_dec_ref_known(v___x_5166_, 2);
v___x_5205_ = lean_array_get_size(v_a_5204_);
v___x_5206_ = lean_nat_dec_lt(v___x_5143_, v___x_5205_);
if (v___x_5206_ == 0)
{
lean_object* v___x_5207_; lean_object* v___x_5209_; 
lean_dec(v_a_5204_);
v___x_5207_ = lean_box(0);
if (v_isShared_5164_ == 0)
{
lean_ctor_set_tag(v___x_5163_, 1);
lean_ctor_set(v___x_5163_, 0, v___x_5207_);
v___x_5209_ = v___x_5163_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5210_; 
v_reuseFailAlloc_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5207_);
v___x_5209_ = v_reuseFailAlloc_5210_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
return v___x_5209_;
}
}
else
{
lean_object* v___x_5211_; uint8_t v___x_5212_; 
lean_del_object(v___x_5163_);
v___x_5211_ = lean_box(0);
v___x_5212_ = lean_nat_dec_le(v___x_5205_, v___x_5205_);
if (v___x_5212_ == 0)
{
if (v___x_5206_ == 0)
{
lean_dec(v_a_5204_);
goto v___jp_5128_;
}
else
{
size_t v___x_5213_; size_t v___x_5214_; lean_object* v___x_5215_; 
v___x_5213_ = ((size_t)0ULL);
v___x_5214_ = lean_usize_of_nat(v___x_5205_);
v___x_5215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5204_, v___x_5213_, v___x_5214_, v___x_5211_, v___y_5126_);
lean_dec(v_a_5204_);
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_dec_ref_known(v___x_5215_, 1);
goto v___jp_5128_;
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5223_; 
v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5223_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5223_ == 0)
{
v___x_5218_ = v___x_5215_;
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v___x_5215_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5223_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
}
}
}
else
{
size_t v___x_5224_; size_t v___x_5225_; lean_object* v___x_5226_; 
v___x_5224_ = ((size_t)0ULL);
v___x_5225_ = lean_usize_of_nat(v___x_5205_);
v___x_5226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5204_, v___x_5224_, v___x_5225_, v___x_5211_, v___y_5126_);
lean_dec(v_a_5204_);
if (lean_obj_tag(v___x_5226_) == 0)
{
lean_dec_ref_known(v___x_5226_, 1);
goto v___jp_5128_;
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5234_; 
v_a_5227_ = lean_ctor_get(v___x_5226_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5226_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5229_ = v___x_5226_;
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_a_5227_);
lean_dec(v___x_5226_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5232_; 
if (v_isShared_5230_ == 0)
{
v___x_5232_ = v___x_5229_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_a_5227_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
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
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
lean_dec_ref(v_packages_5138_);
lean_del_object(v___x_5135_);
lean_dec_ref(v_depIdxs_5133_);
lean_dec_ref(v_ws_5132_);
lean_dec_ref(v_leanOpts_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_pkg_5117_);
v_a_5236_ = lean_ctor_get(v___x_5160_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5160_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5160_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5160_);
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
else
{
uint8_t v___x_5244_; 
lean_inc(v_baseName_5152_);
lean_inc(v_wsIdx_5151_);
lean_dec(v___x_5156_);
lean_dec_ref(v_packages_5138_);
lean_del_object(v___x_5135_);
lean_dec_ref(v_depIdxs_5133_);
lean_dec_ref(v_ws_5132_);
lean_dec_ref(v_leanOpts_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_pkg_5117_);
v___x_5244_ = lean_nat_dec_eq(v_wsIdx_5151_, v___x_5143_);
lean_dec(v_wsIdx_5151_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; uint8_t v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; uint8_t v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; 
v___x_5245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_5246_ = 1;
lean_inc(v_name_5153_);
v___x_5247_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5153_, v___x_5246_);
v___x_5248_ = lean_string_append(v___x_5245_, v___x_5247_);
lean_dec_ref(v___x_5247_);
v___x_5249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_5250_ = lean_string_append(v___x_5248_, v___x_5249_);
v___x_5251_ = l_Lean_Name_toString(v_baseName_5152_, v___x_5244_);
v___x_5252_ = lean_string_append(v___x_5250_, v___x_5251_);
lean_dec_ref(v___x_5251_);
v___x_5253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_5254_ = lean_string_append(v___x_5252_, v___x_5253_);
v___x_5255_ = 3;
v___x_5256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5256_, 0, v___x_5254_);
lean_ctor_set_uint8(v___x_5256_, sizeof(void*)*1, v___x_5255_);
lean_inc_ref(v___y_5126_);
v___x_5257_ = lean_apply_2(v___y_5126_, v___x_5256_, lean_box(0));
v___x_5258_ = lean_box(0);
v___x_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5259_, 0, v___x_5258_);
return v___x_5259_;
}
else
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; uint8_t v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; 
lean_dec(v_baseName_5152_);
v___x_5260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc(v_name_5153_);
v___x_5261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5153_, v___x_5244_);
v___x_5262_ = lean_string_append(v___x_5260_, v___x_5261_);
v___x_5263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__3));
v___x_5264_ = lean_string_append(v___x_5262_, v___x_5263_);
v___x_5265_ = lean_string_append(v___x_5264_, v___x_5261_);
lean_dec_ref(v___x_5261_);
v___x_5266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg___closed__4));
v___x_5267_ = lean_string_append(v___x_5265_, v___x_5266_);
v___x_5268_ = 3;
v___x_5269_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5269_, 0, v___x_5267_);
lean_ctor_set_uint8(v___x_5269_, sizeof(void*)*1, v___x_5268_);
lean_inc_ref(v___y_5126_);
v___x_5270_ = lean_apply_2(v___y_5126_, v___x_5269_, lean_box(0));
v___x_5271_ = lean_box(0);
v___x_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5271_);
return v___x_5272_;
}
}
}
else
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; uint8_t v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
lean_inc(v_baseName_5152_);
lean_dec_ref(v_packages_5138_);
lean_del_object(v___x_5135_);
lean_dec_ref(v_depIdxs_5133_);
lean_dec_ref(v_ws_5132_);
lean_dec_ref(v_leanOpts_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_pkg_5117_);
v___x_5273_ = l_Lean_Name_toString(v_baseName_5152_, v___x_5131_);
v___x_5274_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___closed__0));
v___x_5275_ = lean_string_append(v___x_5273_, v___x_5274_);
v___x_5276_ = 3;
v___x_5277_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5277_, 0, v___x_5275_);
lean_ctor_set_uint8(v___x_5277_, sizeof(void*)*1, v___x_5276_);
lean_inc_ref(v___y_5126_);
v___x_5278_ = lean_apply_2(v___y_5126_, v___x_5277_, lean_box(0));
v___x_5279_ = lean_box(0);
v___x_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5279_);
return v___x_5280_;
}
}
}
}
else
{
lean_object* v___x_5282_; 
lean_dec_ref(v_leanOpts_5120_);
lean_dec_ref(v___y_5119_);
lean_dec_ref(v_pkg_5117_);
v___x_5282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5282_, 0, v_b_5125_);
return v___x_5282_;
}
v___jp_5128_:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = lean_box(0);
v___x_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5129_);
return v___x_5130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_start_5283_, lean_object* v_pkg_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v_leanOpts_5287_, lean_object* v_reconfigure_5288_, lean_object* v_as_5289_, lean_object* v_i_5290_, lean_object* v_stop_5291_, lean_object* v_b_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
uint8_t v_reconfigure_boxed_5295_; size_t v_i_boxed_5296_; size_t v_stop_boxed_5297_; lean_object* v_res_5298_; 
v_reconfigure_boxed_5295_ = lean_unbox(v_reconfigure_5288_);
v_i_boxed_5296_ = lean_unbox_usize(v_i_5290_);
lean_dec(v_i_5290_);
v_stop_boxed_5297_ = lean_unbox_usize(v_stop_5291_);
lean_dec(v_stop_5291_);
v_res_5298_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5283_, v_pkg_5284_, v___y_5285_, v___y_5286_, v_leanOpts_5287_, v_reconfigure_boxed_5295_, v_as_5289_, v_i_boxed_5296_, v_stop_boxed_5297_, v_b_5292_, v___y_5293_);
lean_dec_ref(v___y_5293_);
lean_dec_ref(v_as_5289_);
lean_dec(v___y_5285_);
lean_dec(v_start_5283_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v_leanOpts_5301_, uint8_t v_reconfigure_5302_, lean_object* v_ws_5303_, lean_object* v_i_5304_, lean_object* v_next_5305_, lean_object* v___y_5306_){
_start:
{
lean_object* v_packages_5308_; lean_object* v_pkg_5309_; lean_object* v_ws_5311_; lean_object* v_depIdxs_5312_; lean_object* v___y_5313_; lean_object* v_____x_5323_; lean_object* v___y_5324_; lean_object* v_depConfigs_5327_; lean_object* v_start_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v_s_5331_; lean_object* v___x_5332_; uint8_t v___x_5333_; 
v_packages_5308_ = lean_ctor_get(v_ws_5303_, 4);
v_pkg_5309_ = lean_array_fget(v_packages_5308_, v_i_5304_);
lean_dec(v_i_5304_);
v_depConfigs_5327_ = lean_ctor_get(v_pkg_5309_, 12);
v_start_5328_ = lean_array_get_size(v_packages_5308_);
v___x_5329_ = lean_array_get_size(v_depConfigs_5327_);
v___x_5330_ = lean_mk_empty_array_with_capacity(v___x_5329_);
lean_inc_ref(v___x_5330_);
lean_inc_ref(v_ws_5303_);
v_s_5331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5331_, 0, v_ws_5303_);
lean_ctor_set(v_s_5331_, 1, v___x_5330_);
v___x_5332_ = lean_unsigned_to_nat(0u);
v___x_5333_ = lean_nat_dec_le(v___x_5329_, v___x_5329_);
if (v___x_5333_ == 0)
{
uint8_t v___x_5334_; 
v___x_5334_ = lean_nat_dec_lt(v___x_5332_, v___x_5329_);
if (v___x_5334_ == 0)
{
lean_object* v_ws_5335_; lean_object* v_packages_5336_; lean_object* v___x_5337_; uint8_t v___x_5338_; 
lean_dec_ref_known(v_s_5331_, 2);
v_ws_5335_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5303_, v_pkg_5309_, v___x_5330_);
v_packages_5336_ = lean_ctor_get(v_ws_5335_, 4);
lean_inc_ref(v_packages_5336_);
v___x_5337_ = lean_array_get_size(v_packages_5336_);
lean_dec_ref(v_packages_5336_);
v___x_5338_ = lean_nat_dec_lt(v_next_5305_, v___x_5337_);
if (v___x_5338_ == 0)
{
lean_object* v___x_5339_; 
lean_dec(v_next_5305_);
lean_dec_ref(v_leanOpts_5301_);
lean_dec_ref(v___y_5300_);
v___x_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5339_, 0, v_ws_5335_);
return v___x_5339_;
}
else
{
lean_object* v___x_5340_; lean_object* v___x_5341_; 
v___x_5340_ = lean_unsigned_to_nat(1u);
v___x_5341_ = lean_nat_add(v_next_5305_, v___x_5340_);
v_ws_5303_ = v_ws_5335_;
v_i_5304_ = v_next_5305_;
v_next_5305_ = v___x_5341_;
goto _start;
}
}
else
{
size_t v___x_5343_; size_t v___x_5344_; lean_object* v___x_5345_; 
lean_dec_ref(v___x_5330_);
lean_dec_ref(v_ws_5303_);
v___x_5343_ = lean_usize_of_nat(v___x_5329_);
v___x_5344_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5301_);
lean_inc_ref(v___y_5300_);
lean_inc(v_pkg_5309_);
v___x_5345_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5328_, v_pkg_5309_, v___y_5299_, v___y_5300_, v_leanOpts_5301_, v_reconfigure_5302_, v_depConfigs_5327_, v___x_5343_, v___x_5344_, v_s_5331_, v___y_5306_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
lean_inc(v_a_5346_);
lean_dec_ref_known(v___x_5345_, 1);
v_____x_5323_ = v_a_5346_;
v___y_5324_ = v___y_5306_;
goto v___jp_5322_;
}
else
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
lean_dec(v_pkg_5309_);
lean_dec(v_next_5305_);
lean_dec_ref(v_leanOpts_5301_);
lean_dec_ref(v___y_5300_);
v_a_5347_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5349_ = v___x_5345_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v___x_5345_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
}
else
{
uint8_t v___x_5355_; 
v___x_5355_ = lean_nat_dec_lt(v___x_5332_, v___x_5329_);
if (v___x_5355_ == 0)
{
lean_dec_ref_known(v_s_5331_, 2);
v_ws_5311_ = v_ws_5303_;
v_depIdxs_5312_ = v___x_5330_;
v___y_5313_ = v___y_5306_;
goto v___jp_5310_;
}
else
{
size_t v___x_5356_; size_t v___x_5357_; lean_object* v___x_5358_; 
lean_dec_ref(v___x_5330_);
lean_dec_ref(v_ws_5303_);
v___x_5356_ = lean_usize_of_nat(v___x_5329_);
v___x_5357_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5301_);
lean_inc_ref(v___y_5300_);
lean_inc(v_pkg_5309_);
v___x_5358_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_start_5328_, v_pkg_5309_, v___y_5299_, v___y_5300_, v_leanOpts_5301_, v_reconfigure_5302_, v_depConfigs_5327_, v___x_5356_, v___x_5357_, v_s_5331_, v___y_5306_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
lean_dec_ref_known(v___x_5358_, 1);
v_____x_5323_ = v_a_5359_;
v___y_5324_ = v___y_5306_;
goto v___jp_5322_;
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec(v_pkg_5309_);
lean_dec(v_next_5305_);
lean_dec_ref(v_leanOpts_5301_);
lean_dec_ref(v___y_5300_);
v_a_5360_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5358_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5358_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
v___jp_5310_:
{
lean_object* v_ws_5314_; lean_object* v_packages_5315_; lean_object* v___x_5316_; uint8_t v___x_5317_; 
v_ws_5314_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepIdxs___redArg(v_ws_5311_, v_pkg_5309_, v_depIdxs_5312_);
v_packages_5315_ = lean_ctor_get(v_ws_5314_, 4);
lean_inc_ref(v_packages_5315_);
v___x_5316_ = lean_array_get_size(v_packages_5315_);
lean_dec_ref(v_packages_5315_);
v___x_5317_ = lean_nat_dec_lt(v_next_5305_, v___x_5316_);
if (v___x_5317_ == 0)
{
lean_object* v___x_5318_; 
lean_dec(v_next_5305_);
lean_dec_ref(v_leanOpts_5301_);
lean_dec_ref(v___y_5300_);
v___x_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5318_, 0, v_ws_5314_);
return v___x_5318_;
}
else
{
lean_object* v___x_5319_; lean_object* v___x_5320_; 
v___x_5319_ = lean_unsigned_to_nat(1u);
v___x_5320_ = lean_nat_add(v_next_5305_, v___x_5319_);
v_ws_5303_ = v_ws_5314_;
v_i_5304_ = v_next_5305_;
v_next_5305_ = v___x_5320_;
v___y_5306_ = v___y_5313_;
goto _start;
}
}
v___jp_5322_:
{
lean_object* v_ws_5325_; lean_object* v_depIdxs_5326_; 
v_ws_5325_ = lean_ctor_get(v_____x_5323_, 0);
lean_inc_ref(v_ws_5325_);
v_depIdxs_5326_ = lean_ctor_get(v_____x_5323_, 1);
lean_inc_ref(v_depIdxs_5326_);
lean_dec_ref(v_____x_5323_);
v_ws_5311_ = v_ws_5325_;
v_depIdxs_5312_ = v_depIdxs_5326_;
v___y_5313_ = v___y_5324_;
goto v___jp_5310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v_leanOpts_5370_, lean_object* v_reconfigure_5371_, lean_object* v_ws_5372_, lean_object* v_i_5373_, lean_object* v_next_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
uint8_t v_reconfigure_boxed_5377_; lean_object* v_res_5378_; 
v_reconfigure_boxed_5377_ = lean_unbox(v_reconfigure_5371_);
v_res_5378_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5368_, v___y_5369_, v_leanOpts_5370_, v_reconfigure_boxed_5377_, v_ws_5372_, v_i_5373_, v_next_5374_, v___y_5375_);
lean_dec_ref(v___y_5375_);
lean_dec(v___y_5368_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(lean_object* v_as_5379_, size_t v_i_5380_, size_t v_stop_5381_, lean_object* v_b_5382_){
_start:
{
uint8_t v___x_5383_; 
v___x_5383_ = lean_usize_dec_eq(v_i_5380_, v_stop_5381_);
if (v___x_5383_ == 0)
{
lean_object* v___x_5384_; lean_object* v_name_5385_; lean_object* v___x_5386_; size_t v___x_5387_; size_t v___x_5388_; 
v___x_5384_ = lean_array_uget_borrowed(v_as_5379_, v_i_5380_);
v_name_5385_ = lean_ctor_get(v___x_5384_, 0);
lean_inc(v___x_5384_);
lean_inc(v_name_5385_);
v___x_5386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5385_, v___x_5384_, v_b_5382_);
v___x_5387_ = ((size_t)1ULL);
v___x_5388_ = lean_usize_add(v_i_5380_, v___x_5387_);
v_i_5380_ = v___x_5388_;
v_b_5382_ = v___x_5386_;
goto _start;
}
else
{
return v_b_5382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2___boxed(lean_object* v_as_5390_, lean_object* v_i_5391_, lean_object* v_stop_5392_, lean_object* v_b_5393_){
_start:
{
size_t v_i_boxed_5394_; size_t v_stop_boxed_5395_; lean_object* v_res_5396_; 
v_i_boxed_5394_ = lean_unbox_usize(v_i_5391_);
lean_dec(v_i_5391_);
v_stop_boxed_5395_ = lean_unbox_usize(v_stop_5392_);
lean_dec(v_stop_5392_);
v_res_5396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5390_, v_i_boxed_5394_, v_stop_boxed_5395_, v_b_5393_);
lean_dec_ref(v_as_5390_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5397_, size_t v_i_5398_, size_t v_stop_5399_, lean_object* v_b_5400_){
_start:
{
uint8_t v___x_5401_; 
v___x_5401_ = lean_usize_dec_eq(v_i_5398_, v_stop_5399_);
if (v___x_5401_ == 0)
{
lean_object* v___x_5402_; lean_object* v_name_5403_; lean_object* v___x_5404_; size_t v___x_5405_; size_t v___x_5406_; lean_object* v___x_5407_; 
v___x_5402_ = lean_array_uget_borrowed(v_as_5397_, v_i_5398_);
v_name_5403_ = lean_ctor_get(v___x_5402_, 0);
lean_inc(v___x_5402_);
lean_inc(v_name_5403_);
v___x_5404_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5403_, v___x_5402_, v_b_5400_);
v___x_5405_ = ((size_t)1ULL);
v___x_5406_ = lean_usize_add(v_i_5398_, v___x_5405_);
v___x_5407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__2(v_as_5397_, v___x_5406_, v_stop_5399_, v___x_5404_);
return v___x_5407_;
}
else
{
return v_b_5400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5408_, lean_object* v_i_5409_, lean_object* v_stop_5410_, lean_object* v_b_5411_){
_start:
{
size_t v_i_boxed_5412_; size_t v_stop_boxed_5413_; lean_object* v_res_5414_; 
v_i_boxed_5412_ = lean_unbox_usize(v_i_5409_);
lean_dec(v_i_5409_);
v_stop_boxed_5413_ = lean_unbox_usize(v_stop_5410_);
lean_dec(v_stop_5410_);
v_res_5414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5408_, v_i_boxed_5412_, v_stop_boxed_5413_, v_b_5411_);
lean_dec_ref(v_as_5408_);
return v_res_5414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5424_, lean_object* v_manifest_5425_, lean_object* v_leanOpts_5426_, uint8_t v_reconfigure_5427_, lean_object* v_overrides_5428_, lean_object* v_a_5429_){
_start:
{
lean_object* v___y_5432_; lean_object* v___y_5433_; lean_object* v___y_5434_; lean_object* v___y_5435_; lean_object* v___y_5436_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5463_; lean_object* v___y_5464_; lean_object* v___y_5465_; lean_object* v___y_5466_; lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___y_5482_; lean_object* v___y_5483_; lean_object* v_packagesDir_x3f_5526_; lean_object* v_packages_5527_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5543_; lean_object* v___x_5551_; lean_object* v___x_5552_; uint8_t v___x_5553_; 
v_packagesDir_x3f_5526_ = lean_ctor_get(v_manifest_5425_, 2);
lean_inc(v_packagesDir_x3f_5526_);
v_packages_5527_ = lean_ctor_get(v_manifest_5425_, 3);
lean_inc_ref(v_packages_5527_);
lean_dec_ref(v_manifest_5425_);
v___x_5551_ = lean_array_get_size(v_packages_5527_);
v___x_5552_ = lean_unsigned_to_nat(0u);
v___x_5553_ = lean_nat_dec_eq(v___x_5551_, v___x_5552_);
if (v___x_5553_ == 0)
{
lean_object* v_packages_5554_; lean_object* v___x_5555_; lean_object* v_config_5556_; lean_object* v_toWorkspaceConfig_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; uint8_t v___x_5561_; 
v_packages_5554_ = lean_ctor_get(v_ws_5424_, 4);
v___x_5555_ = lean_array_fget_borrowed(v_packages_5554_, v___x_5552_);
v_config_5556_ = lean_ctor_get(v___x_5555_, 6);
v_toWorkspaceConfig_5557_ = lean_ctor_get(v_config_5556_, 0);
lean_inc_ref(v_toWorkspaceConfig_5557_);
v___x_5558_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5557_);
v___x_5559_ = l_Lake_mkRelPathString(v___x_5558_);
v___x_5560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5560_, 0, v___x_5559_);
v___x_5561_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5526_, v___x_5560_);
lean_dec_ref_known(v___x_5560_, 1);
if (v___x_5561_ == 0)
{
lean_object* v___x_5562_; lean_object* v___x_5563_; 
v___x_5562_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5429_);
v___x_5563_ = lean_apply_2(v_a_5429_, v___x_5562_, lean_box(0));
v___y_5543_ = v_a_5429_;
goto v___jp_5542_;
}
else
{
v___y_5543_ = v_a_5429_;
goto v___jp_5542_;
}
}
else
{
v___y_5543_ = v_a_5429_;
goto v___jp_5542_;
}
v___jp_5431_:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5437_ = lean_array_get_size(v___y_5434_);
lean_dec_ref(v___y_5434_);
v___x_5438_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5436_, v___y_5435_, v_leanOpts_5426_, v_reconfigure_5427_, v_ws_5424_, v___y_5433_, v___x_5437_, v___y_5432_);
lean_dec(v___y_5436_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5447_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5447_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5447_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5443_; lean_object* v___x_5445_; 
v___x_5443_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateDepPkgs(v_a_5439_);
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 0, v___x_5443_);
v___x_5445_ = v___x_5441_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5443_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
else
{
return v___x_5438_;
}
}
v___jp_5448_:
{
if (lean_obj_tag(v___y_5455_) == 0)
{
lean_dec_ref(v___y_5451_);
v___y_5432_ = v___y_5450_;
v___y_5433_ = v___y_5453_;
v___y_5434_ = v___y_5452_;
v___y_5435_ = v___y_5454_;
v___y_5436_ = v___y_5455_;
goto v___jp_5431_;
}
else
{
lean_object* v___x_5456_; uint8_t v___x_5457_; 
v___x_5456_ = lean_array_get_size(v___y_5451_);
lean_dec_ref(v___y_5451_);
v___x_5457_ = lean_nat_dec_eq(v___x_5456_, v___y_5449_);
if (v___x_5457_ == 0)
{
lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
lean_dec_ref(v___y_5454_);
lean_dec(v___y_5453_);
lean_dec_ref(v___y_5452_);
lean_dec_ref(v_leanOpts_5426_);
lean_dec_ref(v_ws_5424_);
v___x_5458_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5450_);
v___x_5459_ = lean_apply_2(v___y_5450_, v___x_5458_, lean_box(0));
v___x_5460_ = lean_box(0);
v___x_5461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5461_, 0, v___x_5460_);
return v___x_5461_;
}
else
{
v___y_5432_ = v___y_5450_;
v___y_5433_ = v___y_5453_;
v___y_5434_ = v___y_5452_;
v___y_5435_ = v___y_5454_;
v___y_5436_ = v___y_5455_;
goto v___jp_5431_;
}
}
}
v___jp_5462_:
{
lean_object* v___x_5470_; uint8_t v___x_5471_; 
v___x_5470_ = lean_array_get_size(v_overrides_5428_);
v___x_5471_ = lean_nat_dec_lt(v___y_5463_, v___x_5470_);
if (v___x_5471_ == 0)
{
v___y_5449_ = v___y_5463_;
v___y_5450_ = v___y_5464_;
v___y_5451_ = v___y_5465_;
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5466_;
v___y_5454_ = v___y_5468_;
v___y_5455_ = v___y_5469_;
goto v___jp_5448_;
}
else
{
uint8_t v___x_5472_; 
v___x_5472_ = lean_nat_dec_le(v___x_5470_, v___x_5470_);
if (v___x_5472_ == 0)
{
if (v___x_5471_ == 0)
{
v___y_5449_ = v___y_5463_;
v___y_5450_ = v___y_5464_;
v___y_5451_ = v___y_5465_;
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5466_;
v___y_5454_ = v___y_5468_;
v___y_5455_ = v___y_5469_;
goto v___jp_5448_;
}
else
{
size_t v___x_5473_; size_t v___x_5474_; lean_object* v___x_5475_; 
v___x_5473_ = ((size_t)0ULL);
v___x_5474_ = lean_usize_of_nat(v___x_5470_);
v___x_5475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5428_, v___x_5473_, v___x_5474_, v___y_5469_);
v___y_5449_ = v___y_5463_;
v___y_5450_ = v___y_5464_;
v___y_5451_ = v___y_5465_;
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5466_;
v___y_5454_ = v___y_5468_;
v___y_5455_ = v___x_5475_;
goto v___jp_5448_;
}
}
else
{
size_t v___x_5476_; size_t v___x_5477_; lean_object* v___x_5478_; 
v___x_5476_ = ((size_t)0ULL);
v___x_5477_ = lean_usize_of_nat(v___x_5470_);
v___x_5478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5428_, v___x_5476_, v___x_5477_, v___y_5469_);
v___y_5449_ = v___y_5463_;
v___y_5450_ = v___y_5464_;
v___y_5451_ = v___y_5465_;
v___y_5452_ = v___y_5467_;
v___y_5453_ = v___y_5466_;
v___y_5454_ = v___y_5468_;
v___y_5455_ = v___x_5478_;
goto v___jp_5448_;
}
}
}
v___jp_5479_:
{
lean_object* v_packages_5484_; lean_object* v___x_5485_; lean_object* v_wsIdx_5486_; lean_object* v_dir_5487_; lean_object* v_depConfigs_5488_; lean_object* v___x_5489_; 
v_packages_5484_ = lean_ctor_get(v_ws_5424_, 4);
v___x_5485_ = lean_array_fget_borrowed(v_packages_5484_, v___y_5480_);
v_wsIdx_5486_ = lean_ctor_get(v___x_5485_, 0);
v_dir_5487_ = lean_ctor_get(v___x_5485_, 4);
v_depConfigs_5488_ = lean_ctor_get(v___x_5485_, 12);
v___x_5489_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5483_, v_depConfigs_5488_, v___y_5481_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
lean_dec_ref_known(v___x_5489_, 1);
v___x_5490_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5487_);
v___x_5491_ = l_Lake_joinRelative(v_dir_5487_, v___x_5490_);
v___x_5492_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5493_ = l_Lake_joinRelative(v___x_5491_, v___x_5492_);
v___x_5494_ = l_Lake_Manifest_tryLoadEntries(v___x_5493_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5496_; uint8_t v___x_5497_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref_known(v___x_5494_, 1);
v___x_5496_ = lean_array_get_size(v_a_5495_);
v___x_5497_ = lean_nat_dec_lt(v___y_5480_, v___x_5496_);
if (v___x_5497_ == 0)
{
lean_dec(v_a_5495_);
lean_inc_ref(v_packages_5484_);
lean_inc(v_wsIdx_5486_);
lean_inc_ref(v_depConfigs_5488_);
v___y_5463_ = v___y_5480_;
v___y_5464_ = v___y_5481_;
v___y_5465_ = v_depConfigs_5488_;
v___y_5466_ = v_wsIdx_5486_;
v___y_5467_ = v_packages_5484_;
v___y_5468_ = v___y_5482_;
v___y_5469_ = v___y_5483_;
goto v___jp_5462_;
}
else
{
uint8_t v___x_5498_; 
v___x_5498_ = lean_nat_dec_le(v___x_5496_, v___x_5496_);
if (v___x_5498_ == 0)
{
if (v___x_5497_ == 0)
{
lean_dec(v_a_5495_);
lean_inc_ref(v_packages_5484_);
lean_inc(v_wsIdx_5486_);
lean_inc_ref(v_depConfigs_5488_);
v___y_5463_ = v___y_5480_;
v___y_5464_ = v___y_5481_;
v___y_5465_ = v_depConfigs_5488_;
v___y_5466_ = v_wsIdx_5486_;
v___y_5467_ = v_packages_5484_;
v___y_5468_ = v___y_5482_;
v___y_5469_ = v___y_5483_;
goto v___jp_5462_;
}
else
{
size_t v___x_5499_; size_t v___x_5500_; lean_object* v___x_5501_; 
v___x_5499_ = ((size_t)0ULL);
v___x_5500_ = lean_usize_of_nat(v___x_5496_);
v___x_5501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5495_, v___x_5499_, v___x_5500_, v___y_5483_);
lean_dec(v_a_5495_);
lean_inc_ref(v_packages_5484_);
lean_inc(v_wsIdx_5486_);
lean_inc_ref(v_depConfigs_5488_);
v___y_5463_ = v___y_5480_;
v___y_5464_ = v___y_5481_;
v___y_5465_ = v_depConfigs_5488_;
v___y_5466_ = v_wsIdx_5486_;
v___y_5467_ = v_packages_5484_;
v___y_5468_ = v___y_5482_;
v___y_5469_ = v___x_5501_;
goto v___jp_5462_;
}
}
else
{
size_t v___x_5502_; size_t v___x_5503_; lean_object* v___x_5504_; 
v___x_5502_ = ((size_t)0ULL);
v___x_5503_ = lean_usize_of_nat(v___x_5496_);
v___x_5504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5495_, v___x_5502_, v___x_5503_, v___y_5483_);
lean_dec(v_a_5495_);
lean_inc_ref(v_packages_5484_);
lean_inc(v_wsIdx_5486_);
lean_inc_ref(v_depConfigs_5488_);
v___y_5463_ = v___y_5480_;
v___y_5464_ = v___y_5481_;
v___y_5465_ = v_depConfigs_5488_;
v___y_5466_ = v_wsIdx_5486_;
v___y_5467_ = v_packages_5484_;
v___y_5468_ = v___y_5482_;
v___y_5469_ = v___x_5504_;
goto v___jp_5462_;
}
}
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5517_; 
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
lean_dec_ref(v_leanOpts_5426_);
lean_dec_ref(v_ws_5424_);
v_a_5505_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5507_ = v___x_5494_;
v_isShared_5508_ = v_isSharedCheck_5517_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5494_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5517_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5509_; uint8_t v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5515_; 
v___x_5509_ = lean_io_error_to_string(v_a_5505_);
v___x_5510_ = 3;
v___x_5511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5511_, 0, v___x_5509_);
lean_ctor_set_uint8(v___x_5511_, sizeof(void*)*1, v___x_5510_);
lean_inc_ref(v___y_5481_);
v___x_5512_ = lean_apply_2(v___y_5481_, v___x_5511_, lean_box(0));
v___x_5513_ = lean_box(0);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 0, v___x_5513_);
v___x_5515_ = v___x_5507_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5513_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
lean_dec_ref(v_leanOpts_5426_);
lean_dec_ref(v_ws_5424_);
v_a_5518_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5489_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5489_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
v___jp_5528_:
{
lean_object* v_pkgEntries_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; uint8_t v___x_5534_; 
v_pkgEntries_5531_ = lean_box(1);
v___x_5532_ = lean_unsigned_to_nat(0u);
v___x_5533_ = lean_array_get_size(v_packages_5527_);
v___x_5534_ = lean_nat_dec_lt(v___x_5532_, v___x_5533_);
if (v___x_5534_ == 0)
{
lean_dec_ref(v_packages_5527_);
v___y_5480_ = v___x_5532_;
v___y_5481_ = v___y_5529_;
v___y_5482_ = v___y_5530_;
v___y_5483_ = v_pkgEntries_5531_;
goto v___jp_5479_;
}
else
{
uint8_t v___x_5535_; 
v___x_5535_ = lean_nat_dec_le(v___x_5533_, v___x_5533_);
if (v___x_5535_ == 0)
{
if (v___x_5534_ == 0)
{
lean_dec_ref(v_packages_5527_);
v___y_5480_ = v___x_5532_;
v___y_5481_ = v___y_5529_;
v___y_5482_ = v___y_5530_;
v___y_5483_ = v_pkgEntries_5531_;
goto v___jp_5479_;
}
else
{
size_t v___x_5536_; size_t v___x_5537_; lean_object* v___x_5538_; 
v___x_5536_ = ((size_t)0ULL);
v___x_5537_ = lean_usize_of_nat(v___x_5533_);
v___x_5538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5527_, v___x_5536_, v___x_5537_, v_pkgEntries_5531_);
lean_dec_ref(v_packages_5527_);
v___y_5480_ = v___x_5532_;
v___y_5481_ = v___y_5529_;
v___y_5482_ = v___y_5530_;
v___y_5483_ = v___x_5538_;
goto v___jp_5479_;
}
}
else
{
size_t v___x_5539_; size_t v___x_5540_; lean_object* v___x_5541_; 
v___x_5539_ = ((size_t)0ULL);
v___x_5540_ = lean_usize_of_nat(v___x_5533_);
v___x_5541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5527_, v___x_5539_, v___x_5540_, v_pkgEntries_5531_);
lean_dec_ref(v_packages_5527_);
v___y_5480_ = v___x_5532_;
v___y_5481_ = v___y_5529_;
v___y_5482_ = v___y_5530_;
v___y_5483_ = v___x_5541_;
goto v___jp_5479_;
}
}
}
v___jp_5542_:
{
if (lean_obj_tag(v_packagesDir_x3f_5526_) == 0)
{
lean_object* v_packages_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v_config_5547_; lean_object* v_toWorkspaceConfig_5548_; lean_object* v___x_5549_; 
v_packages_5544_ = lean_ctor_get(v_ws_5424_, 4);
v___x_5545_ = lean_unsigned_to_nat(0u);
v___x_5546_ = lean_array_fget_borrowed(v_packages_5544_, v___x_5545_);
v_config_5547_ = lean_ctor_get(v___x_5546_, 6);
v_toWorkspaceConfig_5548_ = lean_ctor_get(v_config_5547_, 0);
lean_inc_ref(v_toWorkspaceConfig_5548_);
v___x_5549_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5548_);
v___y_5529_ = v___y_5543_;
v___y_5530_ = v___x_5549_;
goto v___jp_5528_;
}
else
{
lean_object* v_val_5550_; 
v_val_5550_ = lean_ctor_get(v_packagesDir_x3f_5526_, 0);
lean_inc(v_val_5550_);
lean_dec_ref_known(v_packagesDir_x3f_5526_, 1);
v___y_5529_ = v___y_5543_;
v___y_5530_ = v_val_5550_;
goto v___jp_5528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5564_, lean_object* v_manifest_5565_, lean_object* v_leanOpts_5566_, lean_object* v_reconfigure_5567_, lean_object* v_overrides_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_){
_start:
{
uint8_t v_reconfigure_boxed_5571_; lean_object* v_res_5572_; 
v_reconfigure_boxed_5571_ = lean_unbox(v_reconfigure_5567_);
v_res_5572_ = l_Lake_Workspace_materializeDeps(v_ws_5564_, v_manifest_5565_, v_leanOpts_5566_, v_reconfigure_boxed_5571_, v_overrides_5568_, v_a_5569_);
lean_dec_ref(v_a_5569_);
lean_dec_ref(v_overrides_5568_);
return v_res_5572_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v_leanOpts_5575_, uint8_t v_reconfigure_5576_, lean_object* v_ws_5577_, lean_object* v_i_5578_, lean_object* v_i__lt_5579_, lean_object* v_next_5580_, lean_object* v_lt__next_5581_, lean_object* v___y_5582_){
_start:
{
lean_object* v___x_5584_; 
v___x_5584_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5573_, v___y_5574_, v_leanOpts_5575_, v_reconfigure_5576_, v_ws_5577_, v_i_5578_, v_next_5580_, v___y_5582_);
return v___x_5584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v_leanOpts_5587_, lean_object* v_reconfigure_5588_, lean_object* v_ws_5589_, lean_object* v_i_5590_, lean_object* v_i__lt_5591_, lean_object* v_next_5592_, lean_object* v_lt__next_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_){
_start:
{
uint8_t v_reconfigure_boxed_5596_; lean_object* v_res_5597_; 
v_reconfigure_boxed_5596_ = lean_unbox(v_reconfigure_5588_);
v_res_5597_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5585_, v___y_5586_, v_leanOpts_5587_, v_reconfigure_boxed_5596_, v_ws_5589_, v_i_5590_, v_i__lt_5591_, v_next_5592_, v_lt__next_5593_, v___y_5594_);
lean_dec_ref(v___y_5594_);
lean_dec(v___y_5585_);
return v_res_5597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(lean_object* v_start_5598_, lean_object* v_pkg_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v_leanOpts_5602_, uint8_t v_reconfigure_5603_, lean_object* v_as_5604_, size_t v_i_5605_, size_t v_stop_5606_, lean_object* v_b_5607_, lean_object* v___y_5608_){
_start:
{
lean_object* v___x_5610_; 
v___x_5610_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___redArg(v_pkg_5599_, v___y_5600_, v___y_5601_, v_leanOpts_5602_, v_reconfigure_5603_, v_as_5604_, v_i_5605_, v_stop_5606_, v_b_5607_, v___y_5608_);
return v___x_5610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_start_5611_, lean_object* v_pkg_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v_leanOpts_5615_, lean_object* v_reconfigure_5616_, lean_object* v_as_5617_, lean_object* v_i_5618_, lean_object* v_stop_5619_, lean_object* v_b_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_){
_start:
{
uint8_t v_reconfigure_boxed_5623_; size_t v_i_boxed_5624_; size_t v_stop_boxed_5625_; lean_object* v_res_5626_; 
v_reconfigure_boxed_5623_ = lean_unbox(v_reconfigure_5616_);
v_i_boxed_5624_ = lean_unbox_usize(v_i_5618_);
lean_dec(v_i_5618_);
v_stop_boxed_5625_ = lean_unbox_usize(v_stop_5619_);
lean_dec(v_stop_5619_);
v_res_5626_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0_spec__2(v_start_5611_, v_pkg_5612_, v___y_5613_, v___y_5614_, v_leanOpts_5615_, v_reconfigure_boxed_5623_, v_as_5617_, v_i_boxed_5624_, v_stop_boxed_5625_, v_b_5620_, v___y_5621_);
lean_dec_ref(v___y_5621_);
lean_dec_ref(v_as_5617_);
lean_dec(v___y_5613_);
lean_dec(v_start_5611_);
return v_res_5626_;
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

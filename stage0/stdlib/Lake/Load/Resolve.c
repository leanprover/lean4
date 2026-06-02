// Lean compiler output
// Module: Lake.Load.Resolve
// Imports: public import Lake.Config.Workspace public import Lake.Load.Manifest import Lake.Util.IO import Lake.Util.StoreInsts import Lake.Config.Monad import Lake.Load.Materialize import Lake.Load.Lean.Eval import Lake.Load.Package import Init.Data.Range.Polymorphic.Iterators import Init.TacticsExtra import Lean.Runtime
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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_resolveConfigFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadConfigFile___redArg(lean_object*, lean_object*);
lean_object* l_Lake_mkPackage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__0_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__1_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__7_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__2_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__3_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__4_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__5_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__8_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__6_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = ": package requires itself (or a package with the same name)"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": updating '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' with "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9(lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dependency '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "' of '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "' not in manifest; this suggests that the manifest is corrupt; use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "' not in manifest; use `lake update "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` to add it"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_136_ = lean_nat_add(v___y_133_, v___y_135_);
lean_dec(v___y_135_);
lean_dec(v___y_133_);
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
lean_ctor_set(v___x_116_, 3, v___y_134_);
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
lean_ctor_set(v_reuseFailAlloc_141_, 3, v___y_134_);
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
v___y_133_ = v___x_149_;
v___y_134_ = v___x_148_;
v___y_135_ = v_size_150_;
goto v___jp_132_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___y_133_ = v___x_149_;
v___y_134_ = v___x_148_;
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(lean_object* v_self_473_, lean_object* v_pkg_474_, lean_object* v_depPkgs_475_){
_start:
{
lean_object* v_wsIdx_476_; lean_object* v_baseName_477_; lean_object* v_keyName_478_; lean_object* v_origName_479_; lean_object* v_dir_480_; lean_object* v_relDir_481_; lean_object* v_config_482_; lean_object* v_configFile_483_; lean_object* v_relConfigFile_484_; lean_object* v_relManifestFile_485_; lean_object* v_scope_486_; lean_object* v_remoteUrl_487_; lean_object* v_depConfigs_488_; lean_object* v_targetDecls_489_; lean_object* v_targetDeclMap_490_; lean_object* v_defaultTargets_491_; lean_object* v_scripts_492_; lean_object* v_defaultScripts_493_; lean_object* v_postUpdateHooks_494_; lean_object* v_buildArchive_495_; lean_object* v_testDriver_496_; lean_object* v_lintDriver_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_520_; 
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
v_targetDecls_489_ = lean_ctor_get(v_pkg_474_, 14);
v_targetDeclMap_490_ = lean_ctor_get(v_pkg_474_, 15);
v_defaultTargets_491_ = lean_ctor_get(v_pkg_474_, 16);
v_scripts_492_ = lean_ctor_get(v_pkg_474_, 17);
v_defaultScripts_493_ = lean_ctor_get(v_pkg_474_, 18);
v_postUpdateHooks_494_ = lean_ctor_get(v_pkg_474_, 19);
v_buildArchive_495_ = lean_ctor_get(v_pkg_474_, 20);
v_testDriver_496_ = lean_ctor_get(v_pkg_474_, 21);
v_lintDriver_497_ = lean_ctor_get(v_pkg_474_, 22);
v_isSharedCheck_520_ = !lean_is_exclusive(v_pkg_474_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_pkg_474_, 13);
lean_dec(v_unused_521_);
v___x_499_ = v_pkg_474_;
v_isShared_500_ = v_isSharedCheck_520_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_lintDriver_497_);
lean_inc(v_testDriver_496_);
lean_inc(v_buildArchive_495_);
lean_inc(v_postUpdateHooks_494_);
lean_inc(v_defaultScripts_493_);
lean_inc(v_scripts_492_);
lean_inc(v_defaultTargets_491_);
lean_inc(v_targetDeclMap_490_);
lean_inc(v_targetDecls_489_);
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
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_520_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_lakeEnv_501_; lean_object* v_lakeConfig_502_; lean_object* v_lakeCache_503_; lean_object* v_lakeArgs_x3f_504_; lean_object* v_packages_505_; lean_object* v_packageMap_506_; lean_object* v_facetConfigs_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_lakeEnv_501_ = lean_ctor_get(v_self_473_, 0);
v_lakeConfig_502_ = lean_ctor_get(v_self_473_, 1);
v_lakeCache_503_ = lean_ctor_get(v_self_473_, 2);
v_lakeArgs_x3f_504_ = lean_ctor_get(v_self_473_, 3);
v_packages_505_ = lean_ctor_get(v_self_473_, 4);
v_packageMap_506_ = lean_ctor_get(v_self_473_, 5);
v_facetConfigs_507_ = lean_ctor_get(v_self_473_, 6);
v_isSharedCheck_519_ = !lean_is_exclusive(v_self_473_);
if (v_isSharedCheck_519_ == 0)
{
v___x_509_ = v_self_473_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_facetConfigs_507_);
lean_inc(v_packageMap_506_);
lean_inc(v_packages_505_);
lean_inc(v_lakeArgs_x3f_504_);
lean_inc(v_lakeCache_503_);
lean_inc(v_lakeConfig_502_);
lean_inc(v_lakeEnv_501_);
lean_dec(v_self_473_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v_pkg_512_; 
lean_inc(v_keyName_478_);
lean_inc(v_wsIdx_476_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 13, v_depPkgs_475_);
v_pkg_512_ = v___x_499_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 23, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_wsIdx_476_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_baseName_477_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_keyName_478_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_origName_479_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_dir_480_);
lean_ctor_set(v_reuseFailAlloc_518_, 5, v_relDir_481_);
lean_ctor_set(v_reuseFailAlloc_518_, 6, v_config_482_);
lean_ctor_set(v_reuseFailAlloc_518_, 7, v_configFile_483_);
lean_ctor_set(v_reuseFailAlloc_518_, 8, v_relConfigFile_484_);
lean_ctor_set(v_reuseFailAlloc_518_, 9, v_relManifestFile_485_);
lean_ctor_set(v_reuseFailAlloc_518_, 10, v_scope_486_);
lean_ctor_set(v_reuseFailAlloc_518_, 11, v_remoteUrl_487_);
lean_ctor_set(v_reuseFailAlloc_518_, 12, v_depConfigs_488_);
lean_ctor_set(v_reuseFailAlloc_518_, 13, v_depPkgs_475_);
lean_ctor_set(v_reuseFailAlloc_518_, 14, v_targetDecls_489_);
lean_ctor_set(v_reuseFailAlloc_518_, 15, v_targetDeclMap_490_);
lean_ctor_set(v_reuseFailAlloc_518_, 16, v_defaultTargets_491_);
lean_ctor_set(v_reuseFailAlloc_518_, 17, v_scripts_492_);
lean_ctor_set(v_reuseFailAlloc_518_, 18, v_defaultScripts_493_);
lean_ctor_set(v_reuseFailAlloc_518_, 19, v_postUpdateHooks_494_);
lean_ctor_set(v_reuseFailAlloc_518_, 20, v_buildArchive_495_);
lean_ctor_set(v_reuseFailAlloc_518_, 21, v_testDriver_496_);
lean_ctor_set(v_reuseFailAlloc_518_, 22, v_lintDriver_497_);
v_pkg_512_ = v_reuseFailAlloc_518_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_inc_ref(v_pkg_512_);
v___x_513_ = lean_array_fset(v_packages_505_, v_wsIdx_476_, v_pkg_512_);
lean_dec(v_wsIdx_476_);
v___x_514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27_spec__0___redArg(v_keyName_478_, v_pkg_512_, v_packageMap_506_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 5, v___x_514_);
lean_ctor_set(v___x_509_, 4, v___x_513_);
v___x_516_ = v___x_509_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_lakeEnv_501_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_lakeConfig_502_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_lakeCache_503_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_lakeArgs_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_facetConfigs_507_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs(lean_object* v_self_522_, lean_object* v_pkg_523_, lean_object* v_depPkgs_524_, lean_object* v_h_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_self_522_, v_pkg_523_, v_depPkgs_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(lean_object* v_ws_527_, lean_object* v_size_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_mk_empty_array_with_capacity(v_size_528_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v_ws_527_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_init___boxed(lean_object* v_ws_531_, lean_object* v_size_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_init(v_ws_531_, v_size_532_);
lean_dec(v_size_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___redArg(lean_object* v_s_534_, lean_object* v_wsIdx_535_){
_start:
{
lean_object* v_ws_536_; lean_object* v_depIdxs_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
v_ws_536_ = lean_ctor_get(v_s_534_, 0);
v_depIdxs_537_ = lean_ctor_get(v_s_534_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_s_534_);
if (v_isSharedCheck_545_ == 0)
{
v___x_539_ = v_s_534_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_depIdxs_537_);
lean_inc(v_ws_536_);
lean_dec(v_s_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_array_push(v_depIdxs_537_, v_wsIdx_535_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_ws_536_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(lean_object* v_n_546_, lean_object* v_s_547_, lean_object* v_wsIdx_548_){
_start:
{
lean_object* v_ws_549_; lean_object* v_depIdxs_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_ws_549_ = lean_ctor_get(v_s_547_, 0);
v_depIdxs_550_ = lean_ctor_get(v_s_547_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_s_547_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v_s_547_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_depIdxs_550_);
lean_inc(v_ws_549_);
lean_dec(v_s_547_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_array_push(v_depIdxs_550_, v_wsIdx_548_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_ws_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep___boxed(lean_object* v_n_559_, lean_object* v_s_560_, lean_object* v_wsIdx_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_reuseDep(v_n_559_, v_s_560_, v_wsIdx_561_);
lean_dec(v_n_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(lean_object* v_s_563_, lean_object* v_dep_564_, lean_object* v_lakeOpts_565_, lean_object* v_leanOpts_566_, uint8_t v_reconfigure_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_ws_570_; lean_object* v_depIdxs_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_600_; 
v_ws_570_ = lean_ctor_get(v_s_563_, 0);
v_depIdxs_571_ = lean_ctor_get(v_s_563_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_s_563_);
if (v_isSharedCheck_600_ == 0)
{
v___x_573_ = v_s_563_;
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_depIdxs_571_);
lean_inc(v_ws_570_);
lean_dec(v_s_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_600_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; 
lean_inc_ref(v_ws_570_);
v___x_575_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_570_, v_dep_564_, v_lakeOpts_565_, v_leanOpts_566_, v_reconfigure_567_, v_a_568_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_590_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_a_577_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_590_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_590_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_packages_581_; lean_object* v_wsIdx_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v_packages_581_ = lean_ctor_get(v_ws_570_, 4);
lean_inc_ref(v_packages_581_);
lean_dec_ref(v_ws_570_);
v_wsIdx_582_ = lean_array_get_size(v_packages_581_);
lean_dec_ref(v_packages_581_);
v___x_583_ = lean_array_push(v_depIdxs_571_, v_wsIdx_582_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___x_583_);
lean_ctor_set(v___x_573_, 0, v_a_576_);
v___x_585_ = v___x_573_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_583_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_585_);
v___x_587_ = v___x_579_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_a_577_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_del_object(v___x_573_);
lean_dec_ref(v_depIdxs_571_);
lean_dec_ref(v_ws_570_);
v_a_591_ = lean_ctor_get(v___x_575_, 0);
v_a_592_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_575_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_inc(v_a_591_);
lean_dec(v___x_575_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg___boxed(lean_object* v_s_601_, lean_object* v_dep_602_, lean_object* v_lakeOpts_603_, lean_object* v_leanOpts_604_, lean_object* v_reconfigure_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
uint8_t v_reconfigure_boxed_608_; lean_object* v_res_609_; 
v_reconfigure_boxed_608_ = lean_unbox(v_reconfigure_605_);
v_res_609_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___redArg(v_s_601_, v_dep_602_, v_lakeOpts_603_, v_leanOpts_604_, v_reconfigure_boxed_608_, v_a_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(lean_object* v_n_610_, lean_object* v_s_611_, lean_object* v_dep_612_, lean_object* v_lakeOpts_613_, lean_object* v_leanOpts_614_, uint8_t v_reconfigure_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_ws_618_; lean_object* v_depIdxs_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_648_; 
v_ws_618_ = lean_ctor_get(v_s_611_, 0);
v_depIdxs_619_ = lean_ctor_get(v_s_611_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_s_611_);
if (v_isSharedCheck_648_ == 0)
{
v___x_621_ = v_s_611_;
v_isShared_622_ = v_isSharedCheck_648_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_depIdxs_619_);
lean_inc(v_ws_618_);
lean_dec(v_s_611_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_648_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; 
lean_inc_ref(v_ws_618_);
v___x_623_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_618_, v_dep_612_, v_lakeOpts_613_, v_leanOpts_614_, v_reconfigure_615_, v_a_616_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_638_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_a_625_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_638_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_638_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_packages_629_; lean_object* v_wsIdx_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v_packages_629_ = lean_ctor_get(v_ws_618_, 4);
lean_inc_ref(v_packages_629_);
lean_dec_ref(v_ws_618_);
v_wsIdx_630_ = lean_array_get_size(v_packages_629_);
lean_dec_ref(v_packages_629_);
v___x_631_ = lean_array_push(v_depIdxs_619_, v_wsIdx_630_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_631_);
lean_ctor_set(v___x_621_, 0, v_a_624_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_633_);
v___x_635_ = v___x_627_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_a_625_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_del_object(v___x_621_);
lean_dec_ref(v_depIdxs_619_);
lean_dec_ref(v_ws_618_);
v_a_639_ = lean_ctor_get(v___x_623_, 0);
v_a_640_ = lean_ctor_get(v___x_623_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_623_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v___x_623_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed(lean_object* v_n_649_, lean_object* v_s_650_, lean_object* v_dep_651_, lean_object* v_lakeOpts_652_, lean_object* v_leanOpts_653_, lean_object* v_reconfigure_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
uint8_t v_reconfigure_boxed_657_; lean_object* v_res_658_; 
v_reconfigure_boxed_657_ = lean_unbox(v_reconfigure_654_);
v_res_658_ = l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep(v_n_649_, v_s_650_, v_dep_651_, v_lakeOpts_652_, v_leanOpts_653_, v_reconfigure_boxed_657_, v_a_655_);
lean_dec(v_n_649_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___redArg(lean_object* v_inst_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_apply_2(v_inst_659_, lean_box(0), lean_box(0));
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(lean_object* v_m_661_, lean_object* v_00_u03b1_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_as_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_apply_2(v_inst_663_, lean_box(0), lean_box(0));
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl___boxed(lean_object* v_m_667_, lean_object* v_00_u03b1_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_as_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lake_Load_Resolve_0__Lake_guardBySizeImpl(v_m_667_, v_00_u03b1_668_, v_inst_669_, v_inst_670_, v_as_671_);
lean_dec_ref(v_as_671_);
lean_dec(v_inst_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_toPure_673_, lean_object* v_____do__lift_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = lean_apply_2(v_toPure_673_, lean_box(0), v_____do__lift_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_toPure_676_, lean_object* v_____s_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_apply_2(v_toPure_676_, lean_box(0), v_____s_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_toPure_679_, lean_object* v_____x_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_____x_680_);
v___x_682_ = lean_apply_2(v_toPure_679_, lean_box(0), v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_____x_683_, lean_object* v_x_684_){
_start:
{
lean_object* v_packages_685_; lean_object* v___x_686_; 
v_packages_685_ = lean_ctor_get(v_____x_683_, 4);
v___x_686_ = lean_array_fget_borrowed(v_packages_685_, v_x_684_);
lean_inc(v___x_686_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v_____x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v_____x_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec_ref(v_____x_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_depIdxs_709_, lean_object* v_pkg_710_, lean_object* v_toPure_711_, lean_object* v_____x_712_){
_start:
{
lean_object* v___f_713_; lean_object* v___x_714_; size_t v_sz_715_; size_t v___x_716_; lean_object* v_depPkgs_717_; lean_object* v_ws_718_; lean_object* v___x_719_; 
lean_inc_ref(v_____x_712_);
v___f_713_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 2, 1);
lean_closure_set(v___f_713_, 0, v_____x_712_);
v___x_714_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___closed__9));
v_sz_715_ = lean_array_size(v_depIdxs_709_);
v___x_716_ = ((size_t)0ULL);
v_depPkgs_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_714_, v___f_713_, v_sz_715_, v___x_716_, v_depIdxs_709_);
v_ws_718_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_____x_712_, v_pkg_710_, v_depPkgs_717_);
v___x_719_ = lean_apply_2(v_toPure_711_, lean_box(0), v_ws_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v_toPure_720_, lean_object* v_next_721_, lean_object* v_G_722_, lean_object* v_____do__lift_723_){
_start:
{
if (lean_obj_tag(v_____do__lift_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
lean_dec(v_G_722_);
v_a_724_ = lean_ctor_get(v_____do__lift_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v_____do__lift_723_, 1);
v___x_725_ = lean_apply_2(v_toPure_720_, lean_box(0), v_a_724_);
return v___x_725_;
}
else
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec(v_toPure_720_);
v_a_726_ = lean_ctor_get(v_____do__lift_723_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v_____do__lift_723_, 1);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_add(v_next_721_, v___x_727_);
v___x_729_ = lean_apply_4(v_G_722_, v___x_728_, v_a_726_, lean_box(0), lean_box(0));
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed(lean_object* v_toPure_730_, lean_object* v_next_731_, lean_object* v_G_732_, lean_object* v_____do__lift_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(v_toPure_730_, v_next_731_, v_G_732_, v_____do__lift_733_);
lean_dec(v_next_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object* v___f_735_, lean_object* v_start_736_, lean_object* v_ws_737_, lean_object* v_toBind_738_, lean_object* v___f_739_, lean_object* v___f_740_, lean_object* v_____x_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_735_, v_start_736_, v_ws_737_, lean_box(0));
lean_inc(v_toBind_738_);
v___x_743_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v___x_742_, v___f_739_);
v___x_744_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v___x_743_, v___f_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12(lean_object* v___f_745_, lean_object* v_____r_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_apply_1(v___f_745_, v_____r_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object* v_resolve_748_, lean_object* v_pkg_749_, lean_object* v_dep_750_, lean_object* v_ws_751_, lean_object* v_toBind_752_, lean_object* v___f_753_, lean_object* v_____r_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_apply_3(v_resolve_748_, v_pkg_749_, v_dep_750_, v_ws_751_);
v___x_756_ = lean_apply_4(v_toBind_752_, lean_box(0), lean_box(0), v___x_755_, v___f_753_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object* v_start_757_, lean_object* v_s_758_, lean_object* v_opts_759_, lean_object* v_leanOpts_760_, uint8_t v_reconfigure_761_, lean_object* v_inst_762_, lean_object* v_matDep_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_box(v_reconfigure_761_);
v___x_765_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_ResolveState_newDep___boxed), 8, 6);
lean_closure_set(v___x_765_, 0, v_start_757_);
lean_closure_set(v___x_765_, 1, v_s_758_);
lean_closure_set(v___x_765_, 2, v_matDep_763_);
lean_closure_set(v___x_765_, 3, v_opts_759_);
lean_closure_set(v___x_765_, 4, v_leanOpts_760_);
lean_closure_set(v___x_765_, 5, v___x_764_);
v___x_766_ = lean_apply_2(v_inst_762_, lean_box(0), v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object* v_start_767_, lean_object* v_s_768_, lean_object* v_opts_769_, lean_object* v_leanOpts_770_, lean_object* v_reconfigure_771_, lean_object* v_inst_772_, lean_object* v_matDep_773_){
_start:
{
uint8_t v_reconfigure_boxed_774_; lean_object* v_res_775_; 
v_reconfigure_boxed_774_ = lean_unbox(v_reconfigure_771_);
v_res_775_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(v_start_767_, v_s_768_, v_opts_769_, v_leanOpts_770_, v_reconfigure_boxed_774_, v_inst_772_, v_matDep_773_);
return v_res_775_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object* v_dep_776_, lean_object* v_x_777_){
_start:
{
lean_object* v_baseName_778_; lean_object* v_name_779_; uint8_t v___x_780_; 
v_baseName_778_ = lean_ctor_get(v_x_777_, 1);
v_name_779_ = lean_ctor_get(v_dep_776_, 0);
v___x_780_ = lean_name_eq(v_baseName_778_, v_name_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object* v_dep_781_, lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(v_dep_781_, v_x_782_);
lean_dec_ref(v_x_782_);
lean_dec_ref(v_dep_781_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object* v_toPure_786_, lean_object* v_start_787_, lean_object* v_leanOpts_788_, uint8_t v_reconfigure_789_, lean_object* v_inst_790_, lean_object* v_resolve_791_, lean_object* v_pkg_792_, lean_object* v_toBind_793_, lean_object* v_baseName_794_, lean_object* v_inst_795_, lean_object* v_dep_796_, lean_object* v_s_797_){
_start:
{
lean_object* v_ws_798_; lean_object* v_depIdxs_799_; lean_object* v_packages_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_ws_798_ = lean_ctor_get(v_s_797_, 0);
lean_inc_ref(v_ws_798_);
v_depIdxs_799_ = lean_ctor_get(v_s_797_, 1);
v_packages_800_ = lean_ctor_get(v_ws_798_, 4);
lean_inc_ref(v_dep_796_);
v___f_801_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed), 2, 1);
lean_closure_set(v___f_801_, 0, v_dep_796_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_801_, v_packages_800_, v___x_802_);
if (lean_obj_tag(v___x_803_) == 1)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
lean_inc_ref(v_depIdxs_799_);
lean_dec_ref(v_dep_796_);
lean_dec(v_inst_795_);
lean_dec(v_baseName_794_);
lean_dec(v_toBind_793_);
lean_dec_ref(v_pkg_792_);
lean_dec(v_resolve_791_);
lean_dec(v_inst_790_);
lean_dec_ref(v_leanOpts_788_);
lean_dec(v_start_787_);
v_isSharedCheck_813_ = !lean_is_exclusive(v_s_797_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; lean_object* v_unused_815_; 
v_unused_814_ = lean_ctor_get(v_s_797_, 1);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_s_797_, 0);
lean_dec(v_unused_815_);
v___x_805_ = v_s_797_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_s_797_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_val_807_; lean_object* v___x_808_; lean_object* v___x_810_; 
v_val_807_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_val_807_);
lean_dec_ref_known(v___x_803_, 1);
v___x_808_ = lean_array_push(v_depIdxs_799_, v_val_807_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_ws_798_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_808_);
v___x_810_ = v_reuseFailAlloc_812_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; 
v___x_811_ = lean_apply_2(v_toPure_786_, lean_box(0), v___x_810_);
return v___x_811_;
}
}
}
else
{
lean_object* v_name_816_; lean_object* v_opts_817_; lean_object* v___x_818_; lean_object* v___f_819_; lean_object* v___f_820_; uint8_t v___x_821_; 
lean_dec(v___x_803_);
lean_dec(v_toPure_786_);
v_name_816_ = lean_ctor_get(v_dep_796_, 0);
v_opts_817_ = lean_ctor_get(v_dep_796_, 4);
v___x_818_ = lean_box(v_reconfigure_789_);
lean_inc(v_opts_817_);
v___f_819_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed), 7, 6);
lean_closure_set(v___f_819_, 0, v_start_787_);
lean_closure_set(v___f_819_, 1, v_s_797_);
lean_closure_set(v___f_819_, 2, v_opts_817_);
lean_closure_set(v___f_819_, 3, v_leanOpts_788_);
lean_closure_set(v___f_819_, 4, v___x_818_);
lean_closure_set(v___f_819_, 5, v_inst_790_);
lean_inc_ref(v___f_819_);
lean_inc(v_toBind_793_);
lean_inc_ref(v_ws_798_);
lean_inc_ref(v_dep_796_);
lean_inc_ref(v_pkg_792_);
lean_inc(v_resolve_791_);
v___f_820_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11), 7, 6);
lean_closure_set(v___f_820_, 0, v_resolve_791_);
lean_closure_set(v___f_820_, 1, v_pkg_792_);
lean_closure_set(v___f_820_, 2, v_dep_796_);
lean_closure_set(v___f_820_, 3, v_ws_798_);
lean_closure_set(v___f_820_, 4, v_toBind_793_);
lean_closure_set(v___f_820_, 5, v___f_819_);
v___x_821_ = lean_name_eq(v_baseName_794_, v_name_816_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec_ref(v___f_820_);
lean_dec(v_inst_795_);
lean_dec(v_baseName_794_);
v___x_822_ = lean_box(0);
v___x_823_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(v_resolve_791_, v_pkg_792_, v_dep_796_, v_ws_798_, v_toBind_793_, v___f_819_, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v___f_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v___f_819_);
lean_dec_ref(v_ws_798_);
lean_dec_ref(v_dep_796_);
lean_dec_ref(v_pkg_792_);
lean_dec(v_resolve_791_);
v___f_824_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12), 2, 1);
lean_closure_set(v___f_824_, 0, v___f_820_);
v___x_825_ = 0;
v___x_826_ = l_Lean_Name_toString(v_baseName_794_, v___x_825_);
v___x_827_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_828_ = lean_string_append(v___x_826_, v___x_827_);
v___x_829_ = lean_apply_2(v_inst_795_, lean_box(0), v___x_828_);
v___x_830_ = lean_apply_4(v_toBind_793_, lean_box(0), lean_box(0), v___x_829_, v___f_824_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___boxed(lean_object* v_toPure_831_, lean_object* v_start_832_, lean_object* v_leanOpts_833_, lean_object* v_reconfigure_834_, lean_object* v_inst_835_, lean_object* v_resolve_836_, lean_object* v_pkg_837_, lean_object* v_toBind_838_, lean_object* v_baseName_839_, lean_object* v_inst_840_, lean_object* v_dep_841_, lean_object* v_s_842_){
_start:
{
uint8_t v_reconfigure_boxed_843_; lean_object* v_res_844_; 
v_reconfigure_boxed_843_ = lean_unbox(v_reconfigure_834_);
v_res_844_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(v_toPure_831_, v_start_832_, v_leanOpts_833_, v_reconfigure_boxed_843_, v_inst_835_, v_resolve_836_, v_pkg_837_, v_toBind_838_, v_baseName_839_, v_inst_840_, v_dep_841_, v_s_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object* v_stop_845_, lean_object* v_toPure_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_resolve_850_, lean_object* v_leanOpts_851_, lean_object* v_reconfigure_852_, lean_object* v_toBind_853_, lean_object* v___f_854_, lean_object* v___f_855_, lean_object* v_next_856_, lean_object* v_acc_857_, lean_object* v_h_858_, lean_object* v_G_859_){
_start:
{
uint8_t v_reconfigure_boxed_860_; lean_object* v_res_861_; 
v_reconfigure_boxed_860_ = lean_unbox(v_reconfigure_852_);
v_res_861_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_stop_845_, v_toPure_846_, v_inst_847_, v_inst_848_, v_inst_849_, v_resolve_850_, v_leanOpts_851_, v_reconfigure_boxed_860_, v_toBind_853_, v___f_854_, v___f_855_, v_next_856_, v_acc_857_, v_h_858_, v_G_859_);
lean_dec(v_stop_845_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object* v_pkg_862_, lean_object* v_toPure_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_resolve_867_, lean_object* v_leanOpts_868_, uint8_t v_reconfigure_869_, lean_object* v_toBind_870_, lean_object* v___f_871_, lean_object* v___f_872_, lean_object* v_start_873_, lean_object* v___f_874_, lean_object* v_____x_875_){
_start:
{
lean_object* v_ws_876_; lean_object* v_depIdxs_877_; lean_object* v_packages_878_; lean_object* v___f_879_; lean_object* v_stop_880_; lean_object* v___x_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_ws_876_ = lean_ctor_get(v_____x_875_, 0);
lean_inc_ref(v_ws_876_);
v_depIdxs_877_ = lean_ctor_get(v_____x_875_, 1);
lean_inc_ref(v_depIdxs_877_);
lean_dec_ref(v_____x_875_);
v_packages_878_ = lean_ctor_get(v_ws_876_, 4);
lean_inc_n(v_toPure_863_, 2);
v___f_879_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 4, 3);
lean_closure_set(v___f_879_, 0, v_depIdxs_877_);
lean_closure_set(v___f_879_, 1, v_pkg_862_);
lean_closure_set(v___f_879_, 2, v_toPure_863_);
v_stop_880_ = lean_array_get_size(v_packages_878_);
v___x_881_ = lean_box(v_reconfigure_869_);
lean_inc_n(v_toBind_870_, 2);
v___f_882_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 15, 11);
lean_closure_set(v___f_882_, 0, v_stop_880_);
lean_closure_set(v___f_882_, 1, v_toPure_863_);
lean_closure_set(v___f_882_, 2, v_inst_864_);
lean_closure_set(v___f_882_, 3, v_inst_865_);
lean_closure_set(v___f_882_, 4, v_inst_866_);
lean_closure_set(v___f_882_, 5, v_resolve_867_);
lean_closure_set(v___f_882_, 6, v_leanOpts_868_);
lean_closure_set(v___f_882_, 7, v___x_881_);
lean_closure_set(v___f_882_, 8, v_toBind_870_);
lean_closure_set(v___f_882_, 9, v___f_871_);
lean_closure_set(v___f_882_, 10, v___f_872_);
v___f_883_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 7, 6);
lean_closure_set(v___f_883_, 0, v___f_882_);
lean_closure_set(v___f_883_, 1, v_start_873_);
lean_closure_set(v___f_883_, 2, v_ws_876_);
lean_closure_set(v___f_883_, 3, v_toBind_870_);
lean_closure_set(v___f_883_, 4, v___f_874_);
lean_closure_set(v___f_883_, 5, v___f_879_);
v___x_884_ = lean_apply_2(v_toPure_863_, lean_box(0), lean_box(0));
v___x_885_ = lean_apply_4(v_toBind_870_, lean_box(0), lean_box(0), v___x_884_, v___f_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object* v_pkg_886_, lean_object* v_toPure_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_resolve_891_, lean_object* v_leanOpts_892_, lean_object* v_reconfigure_893_, lean_object* v_toBind_894_, lean_object* v___f_895_, lean_object* v___f_896_, lean_object* v_start_897_, lean_object* v___f_898_, lean_object* v_____x_899_){
_start:
{
uint8_t v_reconfigure_boxed_900_; lean_object* v_res_901_; 
v_reconfigure_boxed_900_ = lean_unbox(v_reconfigure_893_);
v_res_901_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(v_pkg_886_, v_toPure_887_, v_inst_888_, v_inst_889_, v_inst_890_, v_resolve_891_, v_leanOpts_892_, v_reconfigure_boxed_900_, v_toBind_894_, v___f_895_, v___f_896_, v_start_897_, v___f_898_, v_____x_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_resolve_905_, lean_object* v_leanOpts_906_, uint8_t v_reconfigure_907_, lean_object* v_ws_908_, lean_object* v_wsIdx_909_){
_start:
{
lean_object* v_packages_910_; lean_object* v_pkg_911_; lean_object* v_toApplicative_912_; lean_object* v_baseName_913_; lean_object* v_depConfigs_914_; lean_object* v_toBind_915_; lean_object* v_toPure_916_; lean_object* v_start_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_s_920_; lean_object* v___f_921_; lean_object* v___f_922_; lean_object* v___f_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_packages_910_ = lean_ctor_get(v_ws_908_, 4);
v_pkg_911_ = lean_array_fget(v_packages_910_, v_wsIdx_909_);
v_toApplicative_912_ = lean_ctor_get(v_inst_902_, 0);
v_baseName_913_ = lean_ctor_get(v_pkg_911_, 1);
lean_inc(v_baseName_913_);
v_depConfigs_914_ = lean_ctor_get(v_pkg_911_, 12);
lean_inc_ref(v_depConfigs_914_);
v_toBind_915_ = lean_ctor_get(v_inst_902_, 1);
lean_inc_n(v_toBind_915_, 2);
v_toPure_916_ = lean_ctor_get(v_toApplicative_912_, 1);
v_start_917_ = lean_array_get_size(v_packages_910_);
v___x_918_ = lean_array_get_size(v_depConfigs_914_);
v___x_919_ = lean_mk_empty_array_with_capacity(v___x_918_);
v_s_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_920_, 0, v_ws_908_);
lean_ctor_set(v_s_920_, 1, v___x_919_);
lean_inc_n(v_toPure_916_, 4);
v___f_921_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_921_, 0, v_toPure_916_);
v___f_922_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1), 2, 1);
lean_closure_set(v___f_922_, 0, v_toPure_916_);
v___f_923_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2), 2, 1);
lean_closure_set(v___f_923_, 0, v_toPure_916_);
v___x_924_ = lean_box(v_reconfigure_907_);
lean_inc_ref(v_leanOpts_906_);
lean_inc(v_resolve_905_);
lean_inc(v_inst_904_);
lean_inc(v_inst_903_);
lean_inc_ref(v_inst_902_);
lean_inc(v_pkg_911_);
v___f_925_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed), 14, 13);
lean_closure_set(v___f_925_, 0, v_pkg_911_);
lean_closure_set(v___f_925_, 1, v_toPure_916_);
lean_closure_set(v___f_925_, 2, v_inst_902_);
lean_closure_set(v___f_925_, 3, v_inst_903_);
lean_closure_set(v___f_925_, 4, v_inst_904_);
lean_closure_set(v___f_925_, 5, v_resolve_905_);
lean_closure_set(v___f_925_, 6, v_leanOpts_906_);
lean_closure_set(v___f_925_, 7, v___x_924_);
lean_closure_set(v___f_925_, 8, v_toBind_915_);
lean_closure_set(v___f_925_, 9, v___f_923_);
lean_closure_set(v___f_925_, 10, v___f_921_);
lean_closure_set(v___f_925_, 11, v_start_917_);
lean_closure_set(v___f_925_, 12, v___f_922_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_nat_dec_lt(v___x_926_, v___x_918_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_inc(v_toPure_916_);
lean_dec_ref(v_depConfigs_914_);
lean_dec(v_baseName_913_);
lean_dec(v_pkg_911_);
lean_dec_ref(v_leanOpts_906_);
lean_dec(v_resolve_905_);
lean_dec(v_inst_904_);
lean_dec(v_inst_903_);
lean_dec_ref(v_inst_902_);
v___x_928_ = lean_apply_2(v_toPure_916_, lean_box(0), v_s_920_);
v___x_929_ = lean_apply_4(v_toBind_915_, lean_box(0), lean_box(0), v___x_928_, v___f_925_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v___f_931_; size_t v___x_932_; size_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_930_ = lean_box(v_reconfigure_907_);
lean_inc(v_toBind_915_);
lean_inc(v_toPure_916_);
v___f_931_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___boxed), 12, 10);
lean_closure_set(v___f_931_, 0, v_toPure_916_);
lean_closure_set(v___f_931_, 1, v_start_917_);
lean_closure_set(v___f_931_, 2, v_leanOpts_906_);
lean_closure_set(v___f_931_, 3, v___x_930_);
lean_closure_set(v___f_931_, 4, v_inst_904_);
lean_closure_set(v___f_931_, 5, v_resolve_905_);
lean_closure_set(v___f_931_, 6, v_pkg_911_);
lean_closure_set(v___f_931_, 7, v_toBind_915_);
lean_closure_set(v___f_931_, 8, v_baseName_913_);
lean_closure_set(v___f_931_, 9, v_inst_903_);
v___x_932_ = lean_usize_of_nat(v___x_918_);
v___x_933_ = ((size_t)0ULL);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_902_, v___f_931_, v_depConfigs_914_, v___x_932_, v___x_933_, v_s_920_);
v___x_935_ = lean_apply_4(v_toBind_915_, lean_box(0), lean_box(0), v___x_934_, v___f_925_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_stop_936_, lean_object* v_toPure_937_, lean_object* v_inst_938_, lean_object* v_inst_939_, lean_object* v_inst_940_, lean_object* v_resolve_941_, lean_object* v_leanOpts_942_, uint8_t v_reconfigure_943_, lean_object* v_toBind_944_, lean_object* v___f_945_, lean_object* v___f_946_, lean_object* v_next_947_, lean_object* v_acc_948_, lean_object* v_h_949_, lean_object* v_G_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_nat_dec_lt(v_next_947_, v_stop_936_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_dec(v_G_950_);
lean_dec(v_next_947_);
lean_dec(v___f_946_);
lean_dec(v___f_945_);
lean_dec(v_toBind_944_);
lean_dec_ref(v_leanOpts_942_);
lean_dec(v_resolve_941_);
lean_dec(v_inst_940_);
lean_dec(v_inst_939_);
lean_dec_ref(v_inst_938_);
v___x_952_ = lean_apply_2(v_toPure_937_, lean_box(0), v_acc_948_);
return v___x_952_;
}
else
{
lean_object* v___f_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
lean_inc(v_next_947_);
v___f_953_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed), 4, 3);
lean_closure_set(v___f_953_, 0, v_toPure_937_);
lean_closure_set(v___f_953_, 1, v_next_947_);
lean_closure_set(v___f_953_, 2, v_G_950_);
v___x_954_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_938_, v_inst_939_, v_inst_940_, v_resolve_941_, v_leanOpts_942_, v_reconfigure_943_, v_acc_948_, v_next_947_);
lean_dec(v_next_947_);
lean_inc_n(v_toBind_944_, 2);
v___x_955_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v___x_954_, v___f_945_);
v___x_956_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v___x_955_, v___f_946_);
v___x_957_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v___x_956_, v___f_953_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_resolve_961_, lean_object* v_leanOpts_962_, lean_object* v_reconfigure_963_, lean_object* v_ws_964_, lean_object* v_wsIdx_965_){
_start:
{
uint8_t v_reconfigure_boxed_966_; lean_object* v_res_967_; 
v_reconfigure_boxed_966_ = lean_unbox(v_reconfigure_963_);
v_res_967_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_958_, v_inst_959_, v_inst_960_, v_resolve_961_, v_leanOpts_962_, v_reconfigure_boxed_966_, v_ws_964_, v_wsIdx_965_);
lean_dec(v_wsIdx_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_inst_971_, lean_object* v_resolve_972_, lean_object* v_leanOpts_973_, uint8_t v_reconfigure_974_, lean_object* v_ws_975_, lean_object* v_wsIdx_976_, lean_object* v_h_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_969_, v_inst_970_, v_inst_971_, v_resolve_972_, v_leanOpts_973_, v_reconfigure_974_, v_ws_975_, v_wsIdx_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_resolve_983_, lean_object* v_leanOpts_984_, lean_object* v_reconfigure_985_, lean_object* v_ws_986_, lean_object* v_wsIdx_987_, lean_object* v_h_988_){
_start:
{
uint8_t v_reconfigure_boxed_989_; lean_object* v_res_990_; 
v_reconfigure_boxed_989_ = lean_unbox(v_reconfigure_985_);
v_res_990_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_979_, v_inst_980_, v_inst_981_, v_inst_982_, v_resolve_983_, v_leanOpts_984_, v_reconfigure_boxed_989_, v_ws_986_, v_wsIdx_987_, v_h_988_);
lean_dec(v_wsIdx_987_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___redArg(lean_object* v_x_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_){
_start:
{
if (lean_obj_tag(v_x_991_) == 1)
{
lean_object* v_val_994_; lean_object* v___x_995_; 
lean_dec(v_h__2_993_);
v_val_994_ = lean_ctor_get(v_x_991_, 0);
lean_inc(v_val_994_);
lean_dec_ref_known(v_x_991_, 1);
v___x_995_ = lean_apply_1(v_h__1_992_, v_val_994_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; 
lean_dec(v_h__1_992_);
v___x_996_ = lean_apply_2(v_h__2_993_, v_x_991_, lean_box(0));
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(lean_object* v_ws_997_, lean_object* v_s_998_, lean_object* v_motive_999_, lean_object* v_x_1000_, lean_object* v_h__1_1001_, lean_object* v_h__2_1002_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 1)
{
lean_object* v_val_1003_; lean_object* v___x_1004_; 
lean_dec(v_h__2_1002_);
v_val_1003_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v_x_1000_, 1);
v___x_1004_ = lean_apply_1(v_h__1_1001_, v_val_1003_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; 
lean_dec(v_h__1_1001_);
v___x_1005_ = lean_apply_2(v_h__2_1002_, v_x_1000_, lean_box(0));
return v___x_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter___boxed(lean_object* v_ws_1006_, lean_object* v_s_1007_, lean_object* v_motive_1008_, lean_object* v_x_1009_, lean_object* v_h__1_1010_, lean_object* v_h__2_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__1_splitter(v_ws_1006_, v_s_1007_, v_motive_1008_, v_x_1009_, v_h__1_1010_, v_h__2_1011_);
lean_dec_ref(v_s_1007_);
lean_dec_ref(v_ws_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___redArg(lean_object* v_x_1013_, lean_object* v_h__1_1014_){
_start:
{
lean_object* v_ws_1015_; lean_object* v_depIdxs_1016_; lean_object* v___x_1017_; 
v_ws_1015_ = lean_ctor_get(v_x_1013_, 0);
lean_inc_ref(v_ws_1015_);
v_depIdxs_1016_ = lean_ctor_get(v_x_1013_, 1);
lean_inc_ref(v_depIdxs_1016_);
lean_dec_ref(v_x_1013_);
v___x_1017_ = lean_apply_4(v_h__1_1014_, v_ws_1015_, v_depIdxs_1016_, lean_box(0), lean_box(0));
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter(lean_object* v_ws_1018_, lean_object* v_motive_1019_, lean_object* v_x_1020_, lean_object* v_h__1_1021_){
_start:
{
lean_object* v_ws_1022_; lean_object* v_depIdxs_1023_; lean_object* v___x_1024_; 
v_ws_1022_ = lean_ctor_get(v_x_1020_, 0);
lean_inc_ref(v_ws_1022_);
v_depIdxs_1023_ = lean_ctor_get(v_x_1020_, 1);
lean_inc_ref(v_depIdxs_1023_);
lean_dec_ref(v_x_1020_);
v___x_1024_ = lean_apply_4(v_h__1_1021_, v_ws_1022_, v_depIdxs_1023_, lean_box(0), lean_box(0));
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter___boxed(lean_object* v_ws_1025_, lean_object* v_motive_1026_, lean_object* v_x_1027_, lean_object* v_h__1_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__12_splitter(v_ws_1025_, v_motive_1026_, v_x_1027_, v_h__1_1028_);
lean_dec_ref(v_ws_1025_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___redArg(lean_object* v_h__1_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_apply_1(v_h__1_1030_, lean_box(0));
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter(lean_object* v_ws_1032_, lean_object* v_motive_1033_, lean_object* v_x_1034_, lean_object* v_h__1_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_apply_1(v_h__1_1035_, lean_box(0));
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter___boxed(lean_object* v_ws_1037_, lean_object* v_motive_1038_, lean_object* v_x_1039_, lean_object* v_h__1_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__10_splitter(v_ws_1037_, v_motive_1038_, v_x_1039_, v_h__1_1040_);
lean_dec_ref(v_ws_1037_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___redArg(lean_object* v_x_1042_, lean_object* v_h__1_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_apply_2(v_h__1_1043_, v_x_1042_, lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(lean_object* v_stop_1045_, lean_object* v_motive_1046_, lean_object* v_x_1047_, lean_object* v_h__1_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_apply_2(v_h__1_1048_, v_x_1047_, lean_box(0));
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter___boxed(lean_object* v_stop_1050_, lean_object* v_motive_1051_, lean_object* v_x_1052_, lean_object* v_h__1_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__6_splitter(v_stop_1050_, v_motive_1051_, v_x_1052_, v_h__1_1053_);
lean_dec(v_stop_1050_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___redArg(lean_object* v_x_1055_, lean_object* v_h__1_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_apply_2(v_h__1_1056_, v_x_1055_, lean_box(0));
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(lean_object* v_ws_1058_, lean_object* v_motive_1059_, lean_object* v_x_1060_, lean_object* v_h__1_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_apply_2(v_h__1_1061_, v_x_1060_, lean_box(0));
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter___boxed(lean_object* v_ws_1063_, lean_object* v_motive_1064_, lean_object* v_x_1065_, lean_object* v_h__1_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__4_splitter(v_ws_1063_, v_motive_1064_, v_x_1065_, v_h__1_1066_);
lean_dec_ref(v_ws_1063_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___redArg(lean_object* v_x_1068_, lean_object* v_h__1_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_apply_2(v_h__1_1069_, v_x_1068_, lean_box(0));
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter(lean_object* v_depIdxs_1071_, lean_object* v_motive_1072_, lean_object* v_x_1073_, lean_object* v_h__1_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_apply_2(v_h__1_1074_, v_x_1073_, lean_box(0));
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter___boxed(lean_object* v_depIdxs_1076_, lean_object* v_motive_1077_, lean_object* v_x_1078_, lean_object* v_h__1_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go_match__8_splitter(v_depIdxs_1076_, v_motive_1077_, v_x_1078_, v_h__1_1079_);
lean_dec_ref(v_depIdxs_1076_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_ws_1084_, lean_object* v_resolve_1085_, lean_object* v_root_1086_, lean_object* v_leanOpts_1087_, uint8_t v_reconfigure_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1081_, v_inst_1082_, v_inst_1083_, v_resolve_1085_, v_leanOpts_1087_, v_reconfigure_1088_, v_ws_1084_, v_root_1086_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_ws_1093_, lean_object* v_resolve_1094_, lean_object* v_root_1095_, lean_object* v_leanOpts_1096_, lean_object* v_reconfigure_1097_){
_start:
{
uint8_t v_reconfigure_boxed_1098_; lean_object* v_res_1099_; 
v_reconfigure_boxed_1098_ = lean_unbox(v_reconfigure_1097_);
v_res_1099_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1090_, v_inst_1091_, v_inst_1092_, v_ws_1093_, v_resolve_1094_, v_root_1095_, v_leanOpts_1096_, v_reconfigure_boxed_1098_);
lean_dec(v_root_1095_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_ws_1104_, lean_object* v_resolve_1105_, lean_object* v_root_1106_, lean_object* v_h_1107_, lean_object* v_leanOpts_1108_, uint8_t v_reconfigure_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1101_, v_inst_1102_, v_inst_1103_, v_resolve_1105_, v_leanOpts_1108_, v_reconfigure_1109_, v_ws_1104_, v_root_1106_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_ws_1115_, lean_object* v_resolve_1116_, lean_object* v_root_1117_, lean_object* v_h_1118_, lean_object* v_leanOpts_1119_, lean_object* v_reconfigure_1120_){
_start:
{
uint8_t v_reconfigure_boxed_1121_; lean_object* v_res_1122_; 
v_reconfigure_boxed_1121_ = lean_unbox(v_reconfigure_1120_);
v_res_1122_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1111_, v_inst_1112_, v_inst_1113_, v_inst_1114_, v_ws_1115_, v_resolve_1116_, v_root_1117_, v_h_1118_, v_leanOpts_1119_, v_reconfigure_boxed_1121_);
lean_dec(v_root_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1123_, lean_object* v_init_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_apply_1(v_x_1123_, v_init_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1126_, lean_object* v_00_u03b1_1127_, lean_object* v_x_1128_, lean_object* v_init_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_apply_1(v_x_1128_, v_init_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(lean_object* v_toUpdate_1131_, lean_object* v_as_1132_, size_t v_i_1133_, size_t v_stop_1134_, lean_object* v_b_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_fst_1139_; lean_object* v_snd_1140_; uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_eq(v_i_1133_, v_stop_1134_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; uint8_t v_inherited_1148_; 
v___x_1147_ = lean_array_uget_borrowed(v_as_1132_, v_i_1133_);
v_inherited_1148_ = lean_ctor_get_uint8(v___x_1147_, sizeof(void*)*5);
if (v_inherited_1148_ == 0)
{
lean_object* v_name_1149_; uint8_t v___x_1150_; 
v_name_1149_ = lean_ctor_get(v___x_1147_, 0);
v___x_1150_ = l_Lean_NameSet_contains(v_toUpdate_1131_, v_name_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_box(0);
lean_inc(v___x_1147_);
lean_inc(v_name_1149_);
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1149_, v___x_1147_, v___y_1136_);
v_fst_1139_ = v___x_1151_;
v_snd_1140_ = v___x_1152_;
goto v___jp_1138_;
}
else
{
goto v___jp_1144_;
}
}
else
{
goto v___jp_1144_;
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_b_1135_);
lean_ctor_set(v___x_1153_, 1, v___y_1136_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
v___jp_1138_:
{
size_t v___x_1141_; size_t v___x_1142_; 
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1133_, v___x_1141_);
v_i_1133_ = v___x_1142_;
v_b_1135_ = v_fst_1139_;
v___y_1136_ = v_snd_1140_;
goto _start;
}
v___jp_1144_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_box(0);
v_fst_1139_ = v___x_1145_;
v_snd_1140_ = v___y_1136_;
goto v___jp_1138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg___boxed(lean_object* v_toUpdate_1155_, lean_object* v_as_1156_, lean_object* v_i_1157_, lean_object* v_stop_1158_, lean_object* v_b_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
size_t v_i_boxed_1162_; size_t v_stop_boxed_1163_; lean_object* v_res_1164_; 
v_i_boxed_1162_ = lean_unbox_usize(v_i_1157_);
lean_dec(v_i_1157_);
v_stop_boxed_1163_ = lean_unbox_usize(v_stop_1158_);
lean_dec(v_stop_1158_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1155_, v_as_1156_, v_i_boxed_1162_, v_stop_boxed_1163_, v_b_1159_, v___y_1160_);
lean_dec_ref(v_as_1156_);
lean_dec(v_toUpdate_1155_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1165_, size_t v_i_1166_, size_t v_stop_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_usize_dec_eq(v_i_1166_, v_stop_1167_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; 
v___x_1172_ = lean_array_uget_borrowed(v_as_1165_, v_i_1166_);
lean_inc_ref(v___y_1169_);
lean_inc(v___x_1172_);
v___x_1173_ = lean_apply_2(v___y_1169_, v___x_1172_, lean_box(0));
v___x_1174_ = ((size_t)1ULL);
v___x_1175_ = lean_usize_add(v_i_1166_, v___x_1174_);
v_i_1166_ = v___x_1175_;
v_b_1168_ = v___x_1173_;
goto _start;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_b_1168_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1178_, lean_object* v_i_1179_, lean_object* v_stop_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
size_t v_i_boxed_1184_; size_t v_stop_boxed_1185_; lean_object* v_res_1186_; 
v_i_boxed_1184_ = lean_unbox_usize(v_i_1179_);
lean_dec(v_i_1179_);
v_stop_boxed_1185_ = lean_unbox_usize(v_stop_1180_);
lean_dec(v_stop_1180_);
v_res_1186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1178_, v_i_boxed_1184_, v_stop_boxed_1185_, v_b_1181_, v___y_1182_);
lean_dec_ref(v___y_1182_);
lean_dec_ref(v_as_1178_);
return v_res_1186_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1194_ = lean_array_get_size(v___x_1193_);
return v___x_1194_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_nat_dec_lt(v___x_1196_, v___x_1195_);
return v___x_1197_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1199_ = lean_nat_dec_le(v___x_1198_, v___x_1198_);
return v___x_1199_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8(void){
_start:
{
lean_object* v___x_1200_; size_t v___x_1201_; 
v___x_1200_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1201_ = lean_usize_of_nat(v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1204_, lean_object* v_toUpdate_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___y_1210_; lean_object* v___y_1215_; lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v_packages_1236_; lean_object* v___x_1237_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v_val_1242_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___x_1290_; lean_object* v_baseName_1291_; lean_object* v_dir_1292_; lean_object* v_config_1293_; lean_object* v_relManifestFile_1294_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; uint8_t v_fst_1299_; lean_object* v_snd_1300_; lean_object* v_packagesDir_x3f_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1362_; lean_object* v___y_1363_; uint8_t v___x_1366_; lean_object* v_rootName_1367_; lean_object* v_fst_1369_; lean_object* v_snd_1370_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_val_1421_; lean_object* v___x_1447_; 
v_packages_1236_ = lean_ctor_get(v_ws_1204_, 4);
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_array_fget_borrowed(v_packages_1236_, v___x_1237_);
v_baseName_1291_ = lean_ctor_get(v___x_1290_, 1);
v_dir_1292_ = lean_ctor_get(v___x_1290_, 4);
v_config_1293_ = lean_ctor_get(v___x_1290_, 6);
v_relManifestFile_1294_ = lean_ctor_get(v___x_1290_, 9);
v___x_1366_ = 0;
lean_inc(v_baseName_1291_);
v_rootName_1367_ = l_Lean_Name_toString(v_baseName_1291_, v___x_1366_);
lean_inc_ref(v_relManifestFile_1294_);
lean_inc_ref(v_dir_1292_);
v___x_1418_ = l_Lake_joinRelative(v_dir_1292_, v_relManifestFile_1294_);
v___x_1419_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1447_ = l_Lake_Manifest_load(v___x_1418_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
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
lean_ctor_set_tag(v___x_1450_, 1);
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
v_val_1421_ = v___x_1453_;
goto v___jp_1420_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_a_1456_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1447_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1447_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 0);
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
v_val_1421_ = v___x_1461_;
goto v___jp_1420_;
}
}
}
v___jp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___y_1210_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
v___jp_1214_:
{
if (lean_obj_tag(v_fst_1216_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_snd_1217_);
v_a_1218_ = lean_ctor_get(v_fst_1216_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_fst_1216_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1220_ = v_fst_1216_;
v_isShared_1221_ = v_isSharedCheck_1232_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v_fst_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1232_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1222_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1223_ = lean_io_error_to_string(v_a_1218_);
v___x_1224_ = lean_string_append(v___x_1222_, v___x_1223_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = 3;
v___x_1226_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*1, v___x_1225_);
lean_inc_ref(v___y_1215_);
v___x_1227_ = lean_apply_2(v___y_1215_, v___x_1226_, lean_box(0));
v___x_1228_ = lean_box(0);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 1);
lean_ctor_set(v___x_1220_, 0, v___x_1228_);
v___x_1230_ = v___x_1220_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref(v_fst_1216_);
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_snd_1217_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
v___jp_1238_:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = lean_array_get_size(v___y_1239_);
v___x_1244_ = lean_nat_dec_lt(v___x_1237_, v___x_1243_);
if (v___x_1244_ == 0)
{
v___y_1215_ = v___y_1240_;
v_fst_1216_ = v_val_1242_;
v_snd_1217_ = v___y_1241_;
goto v___jp_1214_;
}
else
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_nat_dec_le(v___x_1243_, v___x_1243_);
if (v___x_1246_ == 0)
{
if (v___x_1244_ == 0)
{
v___y_1215_ = v___y_1240_;
v_fst_1216_ = v_val_1242_;
v_snd_1217_ = v___y_1241_;
goto v___jp_1214_;
}
else
{
size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((size_t)0ULL);
v___x_1248_ = lean_usize_of_nat(v___x_1243_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1239_, v___x_1247_, v___x_1248_, v___x_1245_, v___y_1240_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_dec_ref_known(v___x_1249_, 1);
v___y_1215_ = v___y_1240_;
v_fst_1216_ = v_val_1242_;
v_snd_1217_ = v___y_1241_;
goto v___jp_1214_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_val_1242_);
lean_dec(v___y_1241_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
else
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = lean_usize_of_nat(v___x_1243_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1239_, v___x_1258_, v___x_1259_, v___x_1245_, v___y_1240_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_dec_ref_known(v___x_1260_, 1);
v___y_1215_ = v___y_1240_;
v_fst_1216_ = v_val_1242_;
v_snd_1217_ = v___y_1241_;
goto v___jp_1214_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref(v_val_1242_);
lean_dec(v___y_1241_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
v___jp_1269_:
{
if (lean_obj_tag(v___y_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___y_1273_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___y_1273_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___y_1273_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___y_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 1);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v___y_1239_ = v___y_1270_;
v___y_1240_ = v___y_1271_;
v___y_1241_ = v___y_1272_;
v_val_1242_ = v___x_1279_;
goto v___jp_1238_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___y_1273_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___y_1273_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___y_1273_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___y_1273_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 0);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
v___y_1239_ = v___y_1270_;
v___y_1240_ = v___y_1271_;
v___y_1241_ = v___y_1272_;
v_val_1242_ = v___x_1287_;
goto v___jp_1238_;
}
}
}
}
v___jp_1295_:
{
lean_object* v_toWorkspaceConfig_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_toWorkspaceConfig_1301_ = lean_ctor_get(v_config_1293_, 0);
v___x_1302_ = l_System_FilePath_normalize(v___y_1297_);
lean_inc_ref(v_toWorkspaceConfig_1301_);
v___x_1303_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1301_);
lean_inc_ref(v___x_1303_);
v___x_1304_ = l_System_FilePath_normalize(v___x_1303_);
v___x_1305_ = lean_string_dec_eq(v___x_1302_, v___x_1304_);
lean_dec_ref(v___x_1304_);
lean_dec_ref(v___x_1302_);
if (v___x_1305_ == 0)
{
if (v_fst_1299_ == 0)
{
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___y_1296_);
v___y_1210_ = v_snd_1300_;
goto v___jp_1209_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1306_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1307_ = lean_string_append(v___x_1306_, v___y_1296_);
v___x_1308_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1309_ = lean_string_append(v___x_1307_, v___x_1308_);
lean_inc_ref(v_dir_1292_);
v___x_1310_ = l_Lake_joinRelative(v_dir_1292_, v___x_1303_);
v___x_1311_ = lean_string_append(v___x_1309_, v___x_1310_);
v___x_1312_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1313_ = lean_string_append(v___x_1311_, v___x_1312_);
v___x_1314_ = 1;
v___x_1315_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*1, v___x_1314_);
lean_inc_ref(v___y_1298_);
v___x_1316_ = lean_apply_2(v___y_1298_, v___x_1315_, lean_box(0));
v___x_1317_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1310_);
v___x_1318_ = l_Lake_createParentDirs(v___x_1310_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref_known(v___x_1318_, 1);
v___x_1319_ = lean_io_rename(v___y_1296_, v___x_1310_);
lean_dec_ref(v___x_1310_);
lean_dec_ref(v___y_1296_);
v___y_1270_ = v___x_1317_;
v___y_1271_ = v___y_1298_;
v___y_1272_ = v_snd_1300_;
v___y_1273_ = v___x_1319_;
goto v___jp_1269_;
}
else
{
lean_dec_ref(v___x_1310_);
lean_dec_ref(v___y_1296_);
v___y_1270_ = v___x_1317_;
v___y_1271_ = v___y_1298_;
v___y_1272_ = v_snd_1300_;
v___y_1273_ = v___x_1318_;
goto v___jp_1269_;
}
}
}
else
{
lean_dec_ref(v___x_1303_);
lean_dec_ref(v___y_1296_);
v___y_1210_ = v_snd_1300_;
goto v___jp_1209_;
}
}
v___jp_1320_:
{
if (lean_obj_tag(v_packagesDir_x3f_1321_) == 1)
{
lean_object* v_val_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v_val_1324_ = lean_ctor_get(v_packagesDir_x3f_1321_, 0);
lean_inc_n(v_val_1324_, 2);
lean_dec_ref_known(v_packagesDir_x3f_1321_, 1);
lean_inc_ref(v_dir_1292_);
v___x_1325_ = l_Lake_joinRelative(v_dir_1292_, v_val_1324_);
v___x_1326_ = l_System_FilePath_pathExists(v___x_1325_);
v___x_1327_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1328_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1328_ == 0)
{
v___y_1296_ = v___x_1325_;
v___y_1297_ = v_val_1324_;
v___y_1298_ = v___y_1323_;
v_fst_1299_ = v___x_1326_;
v_snd_1300_ = v___y_1322_;
goto v___jp_1295_;
}
else
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1330_ == 0)
{
if (v___x_1328_ == 0)
{
v___y_1296_ = v___x_1325_;
v___y_1297_ = v_val_1324_;
v___y_1298_ = v___y_1323_;
v_fst_1299_ = v___x_1326_;
v_snd_1300_ = v___y_1322_;
goto v___jp_1295_;
}
else
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1327_, v___x_1331_, v___x_1332_, v___x_1329_, v___y_1323_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_dec_ref_known(v___x_1333_, 1);
v___y_1296_ = v___x_1325_;
v___y_1297_ = v_val_1324_;
v___y_1298_ = v___y_1323_;
v_fst_1299_ = v___x_1326_;
v_snd_1300_ = v___y_1322_;
goto v___jp_1295_;
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v___x_1325_);
lean_dec(v_val_1324_);
lean_dec(v___y_1322_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
else
{
size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((size_t)0ULL);
v___x_1343_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1327_, v___x_1342_, v___x_1343_, v___x_1329_, v___y_1323_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_dec_ref_known(v___x_1344_, 1);
v___y_1296_ = v___x_1325_;
v___y_1297_ = v_val_1324_;
v___y_1298_ = v___y_1323_;
v_fst_1299_ = v___x_1326_;
v_snd_1300_ = v___y_1322_;
goto v___jp_1295_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v___x_1325_);
lean_dec(v_val_1324_);
lean_dec(v___y_1322_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_packagesDir_x3f_1321_);
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___y_1322_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
v___jp_1356_:
{
lean_object* v_packagesDir_x3f_1360_; 
v_packagesDir_x3f_1360_ = lean_ctor_get(v___y_1357_, 2);
lean_inc(v_packagesDir_x3f_1360_);
lean_dec_ref(v___y_1357_);
v_packagesDir_x3f_1321_ = v_packagesDir_x3f_1360_;
v___y_1322_ = v___y_1358_;
v___y_1323_ = v___y_1359_;
goto v___jp_1320_;
}
v___jp_1361_:
{
if (lean_obj_tag(v___y_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v_snd_1365_; 
v_a_1364_ = lean_ctor_get(v___y_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___y_1363_, 1);
v_snd_1365_ = lean_ctor_get(v_a_1364_, 1);
lean_inc(v_snd_1365_);
lean_dec(v_a_1364_);
v___y_1357_ = v___y_1362_;
v___y_1358_ = v_snd_1365_;
v___y_1359_ = v_a_1207_;
goto v___jp_1356_;
}
else
{
lean_dec_ref(v___y_1362_);
return v___y_1363_;
}
}
v___jp_1368_:
{
if (lean_obj_tag(v_fst_1369_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1403_; 
v_a_1371_ = lean_ctor_get(v_fst_1369_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_fst_1369_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1373_ = v_fst_1369_;
v_isShared_1374_ = v_isSharedCheck_1403_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v_fst_1369_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1403_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
if (lean_obj_tag(v_a_1371_) == 11)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec_ref_known(v_a_1371_, 2);
v___x_1375_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1376_ = lean_string_append(v_rootName_1367_, v___x_1375_);
v___x_1377_ = 1;
v___x_1378_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*1, v___x_1377_);
lean_inc_ref(v_a_1207_);
v___x_1379_ = lean_apply_2(v_a_1207_, v___x_1378_, lean_box(0));
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v_snd_1370_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1380_);
v___x_1382_ = v___x_1373_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1205_) == 0)
{
lean_object* v___x_1384_; uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_dec(v_snd_1370_);
lean_dec_ref(v_rootName_1367_);
v___x_1384_ = lean_io_error_to_string(v_a_1371_);
v___x_1385_ = 3;
v___x_1386_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*1, v___x_1385_);
lean_inc_ref(v_a_1207_);
v___x_1387_ = lean_apply_2(v_a_1207_, v___x_1386_, lean_box(0));
v___x_1388_ = lean_box(0);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 1);
lean_ctor_set(v___x_1373_, 0, v___x_1388_);
v___x_1390_ = v___x_1373_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1392_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_1393_ = lean_string_append(v_rootName_1367_, v___x_1392_);
v___x_1394_ = lean_io_error_to_string(v_a_1371_);
v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = 2;
v___x_1397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1397_, 0, v___x_1395_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*1, v___x_1396_);
lean_inc_ref(v_a_1207_);
v___x_1398_ = lean_apply_2(v_a_1207_, v___x_1397_, lean_box(0));
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v_snd_1370_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1399_);
v___x_1401_ = v___x_1373_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1367_);
if (lean_obj_tag(v_toUpdate_1205_) == 0)
{
lean_object* v_a_1404_; lean_object* v_packagesDir_x3f_1405_; lean_object* v_packages_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_a_1404_ = lean_ctor_get(v_fst_1369_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v_fst_1369_, 1);
v_packagesDir_x3f_1405_ = lean_ctor_get(v_a_1404_, 2);
v_packages_1406_ = lean_ctor_get(v_a_1404_, 3);
v___x_1407_ = lean_array_get_size(v_packages_1406_);
v___x_1408_ = lean_nat_dec_lt(v___x_1237_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_inc(v_packagesDir_x3f_1405_);
lean_dec(v_a_1404_);
v_packagesDir_x3f_1321_ = v_packagesDir_x3f_1405_;
v___y_1322_ = v_snd_1370_;
v___y_1323_ = v_a_1207_;
goto v___jp_1320_;
}
else
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = lean_nat_dec_le(v___x_1407_, v___x_1407_);
if (v___x_1410_ == 0)
{
if (v___x_1408_ == 0)
{
lean_inc(v_packagesDir_x3f_1405_);
lean_dec(v_a_1404_);
v_packagesDir_x3f_1321_ = v_packagesDir_x3f_1405_;
v___y_1322_ = v_snd_1370_;
v___y_1323_ = v_a_1207_;
goto v___jp_1320_;
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1407_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1205_, v_packages_1406_, v___x_1411_, v___x_1412_, v___x_1409_, v_snd_1370_);
v___y_1362_ = v_a_1404_;
v___y_1363_ = v___x_1413_;
goto v___jp_1361_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1407_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1205_, v_packages_1406_, v___x_1414_, v___x_1415_, v___x_1409_, v_snd_1370_);
v___y_1362_ = v_a_1404_;
v___y_1363_ = v___x_1416_;
goto v___jp_1361_;
}
}
}
else
{
lean_object* v_a_1417_; 
v_a_1417_ = lean_ctor_get(v_fst_1369_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v_fst_1369_, 1);
v___y_1357_ = v_a_1417_;
v___y_1358_ = v_snd_1370_;
v___y_1359_ = v_a_1207_;
goto v___jp_1356_;
}
}
}
v___jp_1420_:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1422_ == 0)
{
v_fst_1369_ = v_val_1421_;
v_snd_1370_ = v_a_1206_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1424_ == 0)
{
if (v___x_1422_ == 0)
{
v_fst_1369_ = v_val_1421_;
v_snd_1370_ = v_a_1206_;
goto v___jp_1368_;
}
else
{
size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1419_, v___x_1425_, v___x_1426_, v___x_1423_, v_a_1207_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec_ref_known(v___x_1427_, 1);
v_fst_1369_ = v_val_1421_;
v_snd_1370_ = v_a_1206_;
goto v___jp_1368_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref(v_val_1421_);
lean_dec_ref(v_rootName_1367_);
lean_dec(v_a_1206_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1419_, v___x_1436_, v___x_1437_, v___x_1423_, v_a_1207_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref_known(v___x_1438_, 1);
v_fst_1369_ = v_val_1421_;
v_snd_1370_ = v_a_1206_;
goto v___jp_1368_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_val_1421_);
lean_dec_ref(v_rootName_1367_);
lean_dec(v_a_1206_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1464_, lean_object* v_toUpdate_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1464_, v_toUpdate_1465_, v_a_1466_, v_a_1467_);
lean_dec_ref(v_a_1467_);
lean_dec(v_toUpdate_1465_);
lean_dec_ref(v_ws_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_toUpdate_1470_, lean_object* v_as_1471_, size_t v_i_1472_, size_t v_stop_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1470_, v_as_1471_, v_i_1472_, v_stop_1473_, v_b_1474_, v___y_1475_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_toUpdate_1479_, lean_object* v_as_1480_, lean_object* v_i_1481_, lean_object* v_stop_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
size_t v_i_boxed_1487_; size_t v_stop_boxed_1488_; lean_object* v_res_1489_; 
v_i_boxed_1487_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_stop_boxed_1488_ = lean_unbox_usize(v_stop_1482_);
lean_dec(v_stop_1482_);
v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_toUpdate_1479_, v_as_1480_, v_i_boxed_1487_, v_stop_boxed_1488_, v_b_1483_, v___y_1484_, v___y_1485_);
lean_dec_ref(v___y_1485_);
lean_dec_ref(v_as_1480_);
lean_dec(v_toUpdate_1479_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1490_, lean_object* v_as_1491_, size_t v_i_1492_, size_t v_stop_1493_, lean_object* v_b_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_fst_1498_; lean_object* v_snd_1499_; lean_object* v___y_1504_; lean_object* v_name_1505_; uint8_t v___x_1508_; 
v___x_1508_ = lean_usize_dec_eq(v_i_1492_, v_stop_1493_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v_name_1510_; lean_object* v_scope_1511_; lean_object* v_configFile_1512_; lean_object* v_manifestFile_x3f_1513_; lean_object* v_src_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1537_; 
v___x_1509_ = lean_array_uget(v_as_1491_, v_i_1492_);
v_name_1510_ = lean_ctor_get(v___x_1509_, 0);
v_scope_1511_ = lean_ctor_get(v___x_1509_, 1);
v_configFile_1512_ = lean_ctor_get(v___x_1509_, 2);
v_manifestFile_x3f_1513_ = lean_ctor_get(v___x_1509_, 3);
v_src_1514_ = lean_ctor_get(v___x_1509_, 4);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1516_ = v___x_1509_;
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_src_1514_);
lean_inc(v_manifestFile_x3f_1513_);
lean_inc(v_configFile_1512_);
lean_inc(v_scope_1511_);
lean_inc(v_name_1510_);
lean_dec(v___x_1509_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1537_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
uint8_t v___x_1518_; 
v___x_1518_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1510_, v___y_1495_);
if (v___x_1518_ == 0)
{
uint8_t v___x_1519_; 
v___x_1519_ = 1;
if (lean_obj_tag(v_src_1514_) == 0)
{
lean_object* v_dir_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1532_; 
v_dir_1520_ = lean_ctor_get(v_src_1514_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_src_1514_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1522_ = v_src_1514_;
v_isShared_1523_ = v_isSharedCheck_1532_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_dir_1520_);
lean_dec(v_src_1514_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1532_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v_relPkgDir_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v_relPkgDir_1524_ = lean_ctor_get(v_dep_1490_, 1);
lean_inc_ref(v_relPkgDir_1524_);
v___x_1525_ = l_Lake_joinRelative(v_relPkgDir_1524_, v_dir_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1525_);
v___x_1527_ = v___x_1522_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
lean_inc(v_name_1510_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 4, v___x_1527_);
v___x_1529_ = v___x_1516_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_name_1510_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_scope_1511_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_configFile_1512_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_manifestFile_x3f_1513_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*5, v___x_1519_);
v___y_1504_ = v___x_1529_;
v_name_1505_ = v_name_1510_;
goto v___jp_1503_;
}
}
}
}
else
{
lean_object* v___x_1534_; 
lean_inc(v_name_1510_);
if (v_isShared_1517_ == 0)
{
v___x_1534_ = v___x_1516_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_name_1510_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_scope_1511_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_configFile_1512_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_manifestFile_x3f_1513_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v_src_1514_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*5, v___x_1519_);
v___y_1504_ = v___x_1534_;
v_name_1505_ = v_name_1510_;
goto v___jp_1503_;
}
}
}
else
{
lean_object* v___x_1536_; 
lean_del_object(v___x_1516_);
lean_dec_ref(v_src_1514_);
lean_dec(v_manifestFile_x3f_1513_);
lean_dec_ref(v_configFile_1512_);
lean_dec_ref(v_scope_1511_);
lean_dec(v_name_1510_);
v___x_1536_ = lean_box(0);
v_fst_1498_ = v___x_1536_;
v_snd_1499_ = v___y_1495_;
goto v___jp_1497_;
}
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec_ref(v_dep_1490_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_b_1494_);
lean_ctor_set(v___x_1538_, 1, v___y_1495_);
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
v___jp_1497_:
{
size_t v___x_1500_; size_t v___x_1501_; 
v___x_1500_ = ((size_t)1ULL);
v___x_1501_ = lean_usize_add(v_i_1492_, v___x_1500_);
v_i_1492_ = v___x_1501_;
v_b_1494_ = v_fst_1498_;
v___y_1495_ = v_snd_1499_;
goto _start;
}
v___jp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1505_, v___y_1504_, v___y_1495_);
v_fst_1498_ = v___x_1506_;
v_snd_1499_ = v___x_1507_;
goto v___jp_1497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1540_, lean_object* v_as_1541_, lean_object* v_i_1542_, lean_object* v_stop_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
size_t v_i_boxed_1547_; size_t v_stop_boxed_1548_; lean_object* v_res_1549_; 
v_i_boxed_1547_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_stop_boxed_1548_ = lean_unbox_usize(v_stop_1543_);
lean_dec(v_stop_1543_);
v_res_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1540_, v_as_1541_, v_i_boxed_1547_, v_stop_boxed_1548_, v_b_1544_, v___y_1545_);
lean_dec_ref(v_as_1541_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_manifestEntry_1556_; lean_object* v_pkgDir_1557_; lean_object* v_name_1558_; lean_object* v_manifestFile_x3f_1559_; lean_object* v___y_1561_; lean_object* v_fst_1562_; lean_object* v_snd_1563_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v_val_1623_; lean_object* v___y_1651_; 
v_manifestEntry_1556_ = lean_ctor_get(v_dep_1552_, 4);
v_pkgDir_1557_ = lean_ctor_get(v_dep_1552_, 0);
v_name_1558_ = lean_ctor_get(v_manifestEntry_1556_, 0);
v_manifestFile_x3f_1559_ = lean_ctor_get(v_manifestEntry_1556_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1559_) == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1557_);
v___x_1672_ = l_Lake_joinRelative(v_pkgDir_1557_, v___x_1671_);
v___y_1651_ = v___x_1672_;
goto v___jp_1650_;
}
else
{
lean_object* v_val_1673_; lean_object* v___x_1674_; 
v_val_1673_ = lean_ctor_get(v_manifestFile_x3f_1559_, 0);
lean_inc(v_val_1673_);
lean_inc_ref(v_pkgDir_1557_);
v___x_1674_ = l_Lake_joinRelative(v_pkgDir_1557_, v_val_1673_);
v___y_1651_ = v___x_1674_;
goto v___jp_1650_;
}
v___jp_1560_:
{
if (lean_obj_tag(v_fst_1562_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1593_; 
lean_inc(v_name_1558_);
lean_dec_ref(v_dep_1552_);
v_a_1564_ = lean_ctor_get(v_fst_1562_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_fst_1562_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1566_ = v_fst_1562_;
v_isShared_1567_ = v_isSharedCheck_1593_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v_fst_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1593_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
if (lean_obj_tag(v_a_1564_) == 11)
{
uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec_ref_known(v_a_1564_, 2);
v___x_1568_ = 0;
v___x_1569_ = l_Lean_Name_toString(v_name_1558_, v___x_1568_);
v___x_1570_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1571_ = lean_string_append(v___x_1569_, v___x_1570_);
v___x_1572_ = lean_string_append(v___x_1571_, v___y_1561_);
lean_dec_ref(v___y_1561_);
v___x_1573_ = 2;
v___x_1574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*1, v___x_1573_);
lean_inc_ref(v_a_1554_);
v___x_1575_ = lean_apply_2(v_a_1554_, v___x_1574_, lean_box(0));
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v_snd_1563_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1576_);
v___x_1578_ = v___x_1566_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
else
{
uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_dec_ref(v___y_1561_);
v___x_1580_ = 0;
v___x_1581_ = l_Lean_Name_toString(v_name_1558_, v___x_1580_);
v___x_1582_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1583_ = lean_string_append(v___x_1581_, v___x_1582_);
v___x_1584_ = lean_io_error_to_string(v_a_1564_);
v___x_1585_ = lean_string_append(v___x_1583_, v___x_1584_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = 2;
v___x_1587_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*1, v___x_1586_);
lean_inc_ref(v_a_1554_);
v___x_1588_ = lean_apply_2(v_a_1554_, v___x_1587_, lean_box(0));
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v_snd_1563_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1589_);
v___x_1591_ = v___x_1566_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v___y_1561_);
v_a_1594_ = lean_ctor_get(v_fst_1562_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_fst_1562_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1596_ = v_fst_1562_;
v_isShared_1597_ = v_isSharedCheck_1618_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v_fst_1562_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1618_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_packages_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v_packages_1598_ = lean_ctor_get(v_a_1594_, 3);
lean_inc_ref(v_packages_1598_);
lean_dec(v_a_1594_);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = lean_array_get_size(v_packages_1598_);
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_nat_dec_lt(v___x_1599_, v___x_1600_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_dec_ref(v_packages_1598_);
lean_dec_ref(v_dep_1552_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v_snd_1563_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1603_);
v___x_1605_ = v___x_1596_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_nat_dec_le(v___x_1600_, v___x_1600_);
if (v___x_1607_ == 0)
{
if (v___x_1602_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_dec_ref(v_packages_1598_);
lean_dec_ref(v_dep_1552_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1601_);
lean_ctor_set(v___x_1608_, 1, v_snd_1563_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1608_);
v___x_1610_ = v___x_1596_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
lean_del_object(v___x_1596_);
v___x_1612_ = ((size_t)0ULL);
v___x_1613_ = lean_usize_of_nat(v___x_1600_);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1552_, v_packages_1598_, v___x_1612_, v___x_1613_, v___x_1601_, v_snd_1563_);
lean_dec_ref(v_packages_1598_);
return v___x_1614_;
}
}
else
{
size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
lean_del_object(v___x_1596_);
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = lean_usize_of_nat(v___x_1600_);
v___x_1617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1552_, v_packages_1598_, v___x_1615_, v___x_1616_, v___x_1601_, v_snd_1563_);
lean_dec_ref(v_packages_1598_);
return v___x_1617_;
}
}
}
}
}
v___jp_1619_:
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = lean_array_get_size(v___y_1622_);
v___x_1625_ = lean_nat_dec_lt(v___y_1621_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1561_ = v___y_1620_;
v_fst_1562_ = v_val_1623_;
v_snd_1563_ = v_a_1553_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_nat_dec_le(v___x_1624_, v___x_1624_);
if (v___x_1627_ == 0)
{
if (v___x_1625_ == 0)
{
v___y_1561_ = v___y_1620_;
v_fst_1562_ = v_val_1623_;
v_snd_1563_ = v_a_1553_;
goto v___jp_1560_;
}
else
{
size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = lean_usize_of_nat(v___x_1624_);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1622_, v___x_1628_, v___x_1629_, v___x_1626_, v_a_1554_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_dec_ref_known(v___x_1630_, 1);
v___y_1561_ = v___y_1620_;
v_fst_1562_ = v_val_1623_;
v_snd_1563_ = v_a_1553_;
goto v___jp_1560_;
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_val_1623_);
lean_dec_ref(v___y_1620_);
lean_dec(v_a_1553_);
lean_dec_ref(v_dep_1552_);
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
else
{
size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = lean_usize_of_nat(v___x_1624_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1622_, v___x_1639_, v___x_1640_, v___x_1626_, v_a_1554_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec_ref_known(v___x_1641_, 1);
v___y_1561_ = v___y_1620_;
v_fst_1562_ = v_val_1623_;
v_snd_1563_ = v_a_1553_;
goto v___jp_1560_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v_val_1623_);
lean_dec_ref(v___y_1620_);
lean_dec(v_a_1553_);
lean_dec_ref(v_dep_1552_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1651_);
v___x_1654_ = l_Lake_Manifest_load(v___y_1651_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set_tag(v___x_1657_, 1);
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
v___y_1620_ = v___y_1651_;
v___y_1621_ = v___x_1652_;
v___y_1622_ = v___x_1653_;
v_val_1623_ = v___x_1660_;
goto v___jp_1619_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_a_1663_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1654_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1654_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 0);
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v___y_1620_ = v___y_1651_;
v___y_1621_ = v___x_1652_;
v___y_1622_ = v___x_1653_;
v_val_1623_ = v___x_1668_;
goto v___jp_1619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1675_, v_a_1676_, v_a_1677_);
lean_dec_ref(v_a_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1680_, lean_object* v_as_1681_, size_t v_i_1682_, size_t v_stop_1683_, lean_object* v_b_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1680_, v_as_1681_, v_i_1682_, v_stop_1683_, v_b_1684_, v___y_1685_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1689_, lean_object* v_as_1690_, lean_object* v_i_1691_, lean_object* v_stop_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
size_t v_i_boxed_1697_; size_t v_stop_boxed_1698_; lean_object* v_res_1699_; 
v_i_boxed_1697_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_stop_boxed_1698_ = lean_unbox_usize(v_stop_1692_);
lean_dec(v_stop_1692_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1689_, v_as_1690_, v_i_boxed_1697_, v_stop_boxed_1698_, v_b_1693_, v___y_1694_, v___y_1695_);
lean_dec_ref(v___y_1695_);
lean_dec_ref(v_as_1690_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1701_, lean_object* v_pkg_1702_, lean_object* v_dep_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
uint8_t v___y_1708_; lean_object* v___y_1709_; lean_object* v_name_1739_; lean_object* v___x_1740_; 
v_name_1739_ = lean_ctor_get(v_dep_1703_, 0);
v___x_1740_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1704_, v_name_1739_);
if (lean_obj_tag(v___x_1740_) == 1)
{
lean_object* v_val_1741_; lean_object* v_lakeEnv_1742_; lean_object* v_packages_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v_config_1746_; lean_object* v_dir_1747_; lean_object* v_toWorkspaceConfig_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec_ref(v_dep_1703_);
lean_dec_ref(v_pkg_1702_);
v_val_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v_lakeEnv_1742_ = lean_ctor_get(v_ws_1701_, 0);
lean_inc_ref(v_lakeEnv_1742_);
v_packages_1743_ = lean_ctor_get(v_ws_1701_, 4);
lean_inc_ref(v_packages_1743_);
lean_dec_ref(v_ws_1701_);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = lean_array_fget(v_packages_1743_, v___x_1744_);
lean_dec_ref(v_packages_1743_);
v_config_1746_ = lean_ctor_get(v___x_1745_, 6);
lean_inc_ref(v_config_1746_);
v_dir_1747_ = lean_ctor_get(v___x_1745_, 4);
lean_inc_ref(v_dir_1747_);
lean_dec(v___x_1745_);
v_toWorkspaceConfig_1748_ = lean_ctor_get(v_config_1746_, 0);
lean_inc_ref(v_toWorkspaceConfig_1748_);
lean_dec_ref(v_config_1746_);
v___x_1749_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1748_);
v___x_1750_ = l_Lake_PackageEntry_materialize(v_val_1741_, v_lakeEnv_1742_, v_dir_1747_, v___x_1749_, v_a_1705_);
lean_dec_ref(v_lakeEnv_1742_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1759_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_a_1751_);
lean_ctor_set(v___x_1755_, 1, v_a_1704_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_a_1704_);
v_a_1760_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1750_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1750_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v_wsIdx_1768_; lean_object* v_relDir_1769_; uint8_t v___y_1771_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
lean_dec(v___x_1740_);
v_wsIdx_1768_ = lean_ctor_get(v_pkg_1702_, 0);
lean_inc(v_wsIdx_1768_);
v_relDir_1769_ = lean_ctor_get(v_pkg_1702_, 5);
lean_inc_ref(v_relDir_1769_);
lean_dec_ref(v_pkg_1702_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_nat_dec_eq(v_wsIdx_1768_, v___x_1775_);
lean_dec(v_wsIdx_1768_);
if (v___x_1776_ == 0)
{
uint8_t v___x_1777_; 
v___x_1777_ = 1;
v___y_1771_ = v___x_1777_;
goto v___jp_1770_;
}
else
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
v___y_1771_ = v___x_1778_;
goto v___jp_1770_;
}
v___jp_1770_:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1773_ = lean_string_dec_eq(v_relDir_1769_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lake_joinRelative(v_relDir_1769_, v___x_1772_);
v___y_1708_ = v___y_1771_;
v___y_1709_ = v___x_1774_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___y_1771_;
v___y_1709_ = v_relDir_1769_;
goto v___jp_1707_;
}
}
}
v___jp_1707_:
{
lean_object* v_lakeEnv_1710_; lean_object* v_packages_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v_config_1714_; lean_object* v_dir_1715_; lean_object* v_toWorkspaceConfig_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_lakeEnv_1710_ = lean_ctor_get(v_ws_1701_, 0);
lean_inc_ref(v_lakeEnv_1710_);
v_packages_1711_ = lean_ctor_get(v_ws_1701_, 4);
lean_inc_ref(v_packages_1711_);
lean_dec_ref(v_ws_1701_);
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = lean_array_fget(v_packages_1711_, v___x_1712_);
lean_dec_ref(v_packages_1711_);
v_config_1714_ = lean_ctor_get(v___x_1713_, 6);
lean_inc_ref(v_config_1714_);
v_dir_1715_ = lean_ctor_get(v___x_1713_, 4);
lean_inc_ref(v_dir_1715_);
lean_dec(v___x_1713_);
v_toWorkspaceConfig_1716_ = lean_ctor_get(v_config_1714_, 0);
lean_inc_ref(v_toWorkspaceConfig_1716_);
lean_dec_ref(v_config_1714_);
v___x_1717_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1716_);
v___x_1718_ = l_Lake_Dependency_materialize(v_dep_1703_, v___y_1708_, v_lakeEnv_1710_, v_dir_1715_, v___x_1717_, v___y_1709_, v_a_1705_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1730_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1730_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_manifestEntry_1723_; lean_object* v_name_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v_manifestEntry_1723_ = lean_ctor_get(v_a_1719_, 4);
v_name_1724_ = lean_ctor_get(v_manifestEntry_1723_, 0);
lean_inc_ref(v_manifestEntry_1723_);
lean_inc(v_name_1724_);
v___x_1725_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1724_, v_manifestEntry_1723_, v_a_1704_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_a_1719_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1726_);
v___x_1728_ = v___x_1721_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_a_1704_);
v_a_1731_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1718_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1718_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1779_, lean_object* v_pkg_1780_, lean_object* v_dep_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1779_, v_pkg_1780_, v_dep_1781_, v_a_1782_, v_a_1783_);
lean_dec_ref(v_a_1783_);
return v_res_1785_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1786_; 
v___x_1786_ = 4;
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1787_, lean_object* v_tc_x3f_1788_, uint8_t v_fixed_1789_, lean_object* v_self_1790_){
_start:
{
lean_object* v_clashes_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_clashes_1791_ = lean_ctor_get(v_self_1790_, 2);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_self_1790_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; 
v_unused_1799_ = lean_ctor_get(v_self_1790_, 1);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_self_1790_, 0);
lean_dec(v_unused_1800_);
v___x_1793_ = v_self_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_clashes_1791_);
lean_dec(v_self_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v_tc_x3f_1788_);
lean_ctor_set(v___x_1793_, 0, v_src_1787_);
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_src_1787_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_tc_x3f_1788_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_clashes_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*3, v_fixed_1789_);
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1801_, lean_object* v_tc_x3f_1802_, lean_object* v_fixed_1803_, lean_object* v_self_1804_){
_start:
{
uint8_t v_fixed_boxed_1805_; lean_object* v_res_1806_; 
v_fixed_boxed_1805_ = lean_unbox(v_fixed_1803_);
v_res_1806_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1801_, v_tc_x3f_1802_, v_fixed_boxed_1805_, v_self_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1807_, lean_object* v_ver_1808_, uint8_t v_fixed_1809_, lean_object* v_self_1810_){
_start:
{
lean_object* v_src_1811_; lean_object* v_tc_x3f_1812_; lean_object* v_clashes_1813_; uint8_t v_fixed_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1823_; 
v_src_1811_ = lean_ctor_get(v_self_1810_, 0);
v_tc_x3f_1812_ = lean_ctor_get(v_self_1810_, 1);
v_clashes_1813_ = lean_ctor_get(v_self_1810_, 2);
v_fixed_1814_ = lean_ctor_get_uint8(v_self_1810_, sizeof(void*)*3);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_self_1810_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1816_ = v_self_1810_;
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_clashes_1813_);
lean_inc(v_tc_x3f_1812_);
lean_inc(v_src_1811_);
lean_dec(v_self_1810_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1818_, 0, v_src_1807_);
lean_ctor_set(v___x_1818_, 1, v_ver_1808_);
lean_ctor_set_uint8(v___x_1818_, sizeof(void*)*2, v_fixed_1809_);
v___x_1819_ = lean_array_push(v_clashes_1813_, v___x_1818_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 2, v___x_1819_);
v___x_1821_ = v___x_1816_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_src_1811_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_tc_x3f_1812_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v___x_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, sizeof(void*)*3, v_fixed_1814_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1824_, lean_object* v_ver_1825_, lean_object* v_fixed_1826_, lean_object* v_self_1827_){
_start:
{
uint8_t v_fixed_boxed_1828_; lean_object* v_res_1829_; 
v_fixed_boxed_1828_ = lean_unbox(v_fixed_1826_);
v_res_1829_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1824_, v_ver_1825_, v_fixed_boxed_1828_, v_self_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v_as_1834_, size_t v_i_1835_, size_t v_stop_1836_, lean_object* v_b_1837_){
_start:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_usize_dec_eq(v_i_1835_, v_stop_1836_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v_src_1840_; lean_object* v_ver_1841_; uint8_t v_fixed_1842_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1858_; 
v___x_1839_ = lean_array_uget_borrowed(v_as_1834_, v_i_1835_);
v_src_1840_ = lean_ctor_get(v___x_1839_, 0);
v_ver_1841_ = lean_ctor_get(v___x_1839_, 1);
v_fixed_1842_ = lean_ctor_get_uint8(v___x_1839_, sizeof(void*)*2);
if (v_fixed_1842_ == 0)
{
lean_object* v___x_1862_; 
v___x_1862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1858_ = v___x_1862_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1858_ = v___x_1863_;
goto v___jp_1857_;
}
v___jp_1843_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; 
v___x_1847_ = lean_string_append(v___y_1844_, v___y_1846_);
lean_dec_ref(v___y_1846_);
v___x_1848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1849_ = lean_string_append(v___x_1847_, v___x_1848_);
v___x_1850_ = 1;
lean_inc(v_src_1840_);
v___x_1851_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1840_, v___x_1850_);
v___x_1852_ = lean_string_append(v___x_1849_, v___x_1851_);
lean_dec_ref(v___x_1851_);
v___x_1853_ = lean_string_append(v___x_1852_, v___y_1845_);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1835_, v___x_1854_);
v_i_1835_ = v___x_1855_;
v_b_1837_ = v___x_1853_;
goto _start;
}
v___jp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_toString_1861_; 
v___x_1859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1860_ = lean_string_append(v_b_1837_, v___x_1859_);
v_toString_1861_ = lean_ctor_get(v_ver_1841_, 0);
lean_inc_ref(v_toString_1861_);
v___y_1844_ = v___x_1860_;
v___y_1845_ = v___y_1858_;
v___y_1846_ = v_toString_1861_;
goto v___jp_1843_;
}
}
else
{
return v_b_1837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v_as_1864_, lean_object* v_i_1865_, lean_object* v_stop_1866_, lean_object* v_b_1867_){
_start:
{
size_t v_i_boxed_1868_; size_t v_stop_boxed_1869_; lean_object* v_res_1870_; 
v_i_boxed_1868_ = lean_unbox_usize(v_i_1865_);
lean_dec(v_i_1865_);
v_stop_boxed_1869_ = lean_unbox_usize(v_stop_1866_);
lean_dec(v_stop_1866_);
v_res_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1864_, v_i_boxed_1868_, v_stop_boxed_1869_, v_b_1867_);
lean_dec_ref(v_as_1864_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v_as_1871_, size_t v_i_1872_, size_t v_stop_1873_, lean_object* v_b_1874_){
_start:
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_usize_dec_eq(v_i_1872_, v_stop_1873_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v_src_1877_; lean_object* v_ver_1878_; uint8_t v_fixed_1879_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1895_; 
v___x_1876_ = lean_array_uget_borrowed(v_as_1871_, v_i_1872_);
v_src_1877_ = lean_ctor_get(v___x_1876_, 0);
v_ver_1878_ = lean_ctor_get(v___x_1876_, 1);
v_fixed_1879_ = lean_ctor_get_uint8(v___x_1876_, sizeof(void*)*2);
if (v_fixed_1879_ == 0)
{
lean_object* v___x_1899_; 
v___x_1899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1895_ = v___x_1899_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1895_ = v___x_1900_;
goto v___jp_1894_;
}
v___jp_1880_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1884_ = lean_string_append(v___y_1882_, v___y_1883_);
lean_dec_ref(v___y_1883_);
v___x_1885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1886_ = lean_string_append(v___x_1884_, v___x_1885_);
v___x_1887_ = 1;
lean_inc(v_src_1877_);
v___x_1888_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1877_, v___x_1887_);
v___x_1889_ = lean_string_append(v___x_1886_, v___x_1888_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = lean_string_append(v___x_1889_, v___y_1881_);
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = lean_usize_add(v_i_1872_, v___x_1891_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1871_, v___x_1892_, v_stop_1873_, v___x_1890_);
return v___x_1893_;
}
v___jp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v_toString_1898_; 
v___x_1896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1897_ = lean_string_append(v_b_1874_, v___x_1896_);
v_toString_1898_ = lean_ctor_get(v_ver_1878_, 0);
lean_inc_ref(v_toString_1898_);
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___x_1897_;
v___y_1883_ = v_toString_1898_;
goto v___jp_1880_;
}
}
else
{
return v_b_1874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v_as_1901_, lean_object* v_i_1902_, lean_object* v_stop_1903_, lean_object* v_b_1904_){
_start:
{
size_t v_i_boxed_1905_; size_t v_stop_boxed_1906_; lean_object* v_res_1907_; 
v_i_boxed_1905_ = lean_unbox_usize(v_i_1902_);
lean_dec(v_i_1902_);
v_stop_boxed_1906_ = lean_unbox_usize(v_stop_1903_);
lean_dec(v_stop_1903_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v_as_1901_, v_i_boxed_1905_, v_stop_boxed_1906_, v_b_1904_);
lean_dec_ref(v_as_1901_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_1908_, lean_object* v_as_1909_, size_t v_i_1910_, size_t v_stop_1911_, lean_object* v_b_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_eq(v_i_1910_, v_stop_1911_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v_relPkgDir_1917_; lean_object* v_manifestEntry_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1916_ = lean_array_uget_borrowed(v_as_1909_, v_i_1910_);
v_relPkgDir_1917_ = lean_ctor_get(v___x_1916_, 1);
v_manifestEntry_1918_ = lean_ctor_get(v___x_1916_, 4);
lean_inc_ref(v_relPkgDir_1917_);
lean_inc_ref(v___x_1908_);
v___x_1919_ = l_Lake_joinRelative(v___x_1908_, v_relPkgDir_1917_);
v___x_1920_ = l_Lake_toolchainFileName;
v___x_1921_ = l_System_FilePath_join(v___x_1919_, v___x_1920_);
v___x_1922_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1921_);
lean_dec_ref(v___x_1921_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v_a_1925_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
if (lean_obj_tag(v_a_1923_) == 1)
{
lean_object* v_tc_x3f_1929_; 
v_tc_x3f_1929_ = lean_ctor_get(v_b_1912_, 1);
if (lean_obj_tag(v_tc_x3f_1929_) == 1)
{
lean_object* v_val_1930_; lean_object* v_src_1931_; lean_object* v_clashes_1932_; uint8_t v_fixed_1933_; lean_object* v_val_1934_; uint8_t v___x_1935_; 
v_val_1930_ = lean_ctor_get(v_a_1923_, 0);
v_src_1931_ = lean_ctor_get(v_b_1912_, 0);
v_clashes_1932_ = lean_ctor_get(v_b_1912_, 2);
v_fixed_1933_ = lean_ctor_get_uint8(v_b_1912_, sizeof(void*)*3);
v_val_1934_ = lean_ctor_get(v_tc_x3f_1929_, 0);
v___x_1935_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1916_);
if (v___x_1935_ == 0)
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lake_ToolchainVer_ble(v_val_1930_, v_val_1934_);
if (v___x_1945_ == 0)
{
lean_inc_ref(v_clashes_1932_);
lean_inc(v_src_1931_);
lean_inc_ref(v_tc_x3f_1929_);
lean_dec_ref(v_b_1912_);
if (v_fixed_1933_ == 0)
{
goto v___jp_1941_;
}
else
{
if (v___x_1935_ == 0)
{
lean_inc(v_val_1930_);
lean_dec_ref_known(v_a_1923_, 1);
goto v___jp_1936_;
}
else
{
goto v___jp_1941_;
}
}
}
else
{
lean_dec_ref_known(v_a_1923_, 1);
v_a_1925_ = v_b_1912_;
goto v___jp_1924_;
}
}
else
{
if (v_fixed_1933_ == 0)
{
lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1960_; 
lean_inc_ref(v_clashes_1932_);
lean_inc(v_src_1931_);
lean_inc_ref(v_tc_x3f_1929_);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_b_1912_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; lean_object* v_unused_1962_; lean_object* v_unused_1963_; 
v_unused_1961_ = lean_ctor_get(v_b_1912_, 2);
lean_dec(v_unused_1961_);
v_unused_1962_ = lean_ctor_get(v_b_1912_, 1);
lean_dec(v_unused_1962_);
v_unused_1963_ = lean_ctor_get(v_b_1912_, 0);
lean_dec(v_unused_1963_);
v___x_1947_ = v_b_1912_;
v_isShared_1948_ = v_isSharedCheck_1960_;
goto v_resetjp_1946_;
}
else
{
lean_dec(v_b_1912_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1960_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
uint8_t v___x_1949_; 
v___x_1949_ = l_Lake_ToolchainVer_ble(v_val_1934_, v_val_1930_);
if (v___x_1949_ == 0)
{
lean_object* v_name_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
lean_inc(v_val_1930_);
lean_dec_ref_known(v_a_1923_, 1);
v_name_1950_ = lean_ctor_get(v_manifestEntry_1918_, 0);
lean_inc(v_name_1950_);
v___x_1951_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1951_, 0, v_name_1950_);
lean_ctor_set(v___x_1951_, 1, v_val_1930_);
lean_ctor_set_uint8(v___x_1951_, sizeof(void*)*2, v___x_1935_);
v___x_1952_ = lean_array_push(v_clashes_1932_, v___x_1951_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 2, v___x_1952_);
v___x_1954_ = v___x_1947_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_src_1931_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_tc_x3f_1929_);
lean_ctor_set(v_reuseFailAlloc_1955_, 2, v___x_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1955_, sizeof(void*)*3, v_fixed_1933_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
v_a_1925_ = v___x_1954_;
goto v___jp_1924_;
}
}
else
{
lean_object* v_name_1956_; lean_object* v___x_1958_; 
lean_dec(v_src_1931_);
lean_dec_ref_known(v_tc_x3f_1929_, 1);
v_name_1956_ = lean_ctor_get(v_manifestEntry_1918_, 0);
lean_inc(v_name_1956_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v_a_1923_);
lean_ctor_set(v___x_1947_, 0, v_name_1956_);
v___x_1958_ = v___x_1947_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_name_1956_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_a_1923_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_clashes_1932_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3, v___x_1935_);
v_a_1925_ = v___x_1958_;
goto v___jp_1924_;
}
}
}
}
else
{
uint8_t v___x_1964_; 
lean_inc_n(v_val_1930_, 2);
lean_dec_ref_known(v_a_1923_, 1);
lean_inc(v_val_1934_);
v___x_1964_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_1934_, v_val_1930_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1974_; 
lean_inc_ref(v_clashes_1932_);
lean_inc(v_src_1931_);
lean_inc_ref(v_tc_x3f_1929_);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_b_1912_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; lean_object* v_unused_1977_; 
v_unused_1975_ = lean_ctor_get(v_b_1912_, 2);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_b_1912_, 1);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_b_1912_, 0);
lean_dec(v_unused_1977_);
v___x_1966_ = v_b_1912_;
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v_b_1912_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_name_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v_name_1968_ = lean_ctor_get(v_manifestEntry_1918_, 0);
lean_inc(v_name_1968_);
v___x_1969_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1969_, 0, v_name_1968_);
lean_ctor_set(v___x_1969_, 1, v_val_1930_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2, v___x_1935_);
v___x_1970_ = lean_array_push(v_clashes_1932_, v___x_1969_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 2, v___x_1970_);
v___x_1972_ = v___x_1966_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_src_1931_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_tc_x3f_1929_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v___x_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*3, v_fixed_1933_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v_a_1925_ = v___x_1972_;
goto v___jp_1924_;
}
}
}
else
{
lean_dec(v_val_1930_);
v_a_1925_ = v_b_1912_;
goto v___jp_1924_;
}
}
}
v___jp_1936_:
{
lean_object* v_name_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_name_1937_ = lean_ctor_get(v_manifestEntry_1918_, 0);
lean_inc(v_name_1937_);
v___x_1938_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1938_, 0, v_name_1937_);
lean_ctor_set(v___x_1938_, 1, v_val_1930_);
lean_ctor_set_uint8(v___x_1938_, sizeof(void*)*2, v___x_1935_);
v___x_1939_ = lean_array_push(v_clashes_1932_, v___x_1938_);
v___x_1940_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1940_, 0, v_src_1931_);
lean_ctor_set(v___x_1940_, 1, v_tc_x3f_1929_);
lean_ctor_set(v___x_1940_, 2, v___x_1939_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*3, v_fixed_1933_);
v_a_1925_ = v___x_1940_;
goto v___jp_1924_;
}
v___jp_1941_:
{
uint8_t v___x_1942_; 
v___x_1942_ = l_Lake_ToolchainVer_blt(v_val_1934_, v_val_1930_);
if (v___x_1942_ == 0)
{
lean_inc(v_val_1930_);
lean_dec_ref_known(v_a_1923_, 1);
goto v___jp_1936_;
}
else
{
lean_object* v_name_1943_; lean_object* v___x_1944_; 
lean_dec(v_src_1931_);
lean_dec_ref_known(v_tc_x3f_1929_, 1);
v_name_1943_ = lean_ctor_get(v_manifestEntry_1918_, 0);
lean_inc(v_name_1943_);
v___x_1944_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1944_, 0, v_name_1943_);
lean_ctor_set(v___x_1944_, 1, v_a_1923_);
lean_ctor_set(v___x_1944_, 2, v_clashes_1932_);
lean_ctor_set_uint8(v___x_1944_, sizeof(void*)*3, v___x_1935_);
v_a_1925_ = v___x_1944_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v_clashes_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1987_; 
v_clashes_1978_ = lean_ctor_get(v_b_1912_, 2);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_b_1912_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; lean_object* v_unused_1989_; 
v_unused_1988_ = lean_ctor_get(v_b_1912_, 1);
lean_dec(v_unused_1988_);
v_unused_1989_ = lean_ctor_get(v_b_1912_, 0);
lean_dec(v_unused_1989_);
v___x_1980_ = v_b_1912_;
v_isShared_1981_ = v_isSharedCheck_1987_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_clashes_1978_);
lean_dec(v_b_1912_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1987_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_name_1982_; uint8_t v___x_1983_; lean_object* v___x_1985_; 
v_name_1982_ = lean_ctor_get(v_manifestEntry_1918_, 0);
v___x_1983_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1916_);
lean_inc(v_name_1982_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v_a_1923_);
lean_ctor_set(v___x_1980_, 0, v_name_1982_);
v___x_1985_ = v___x_1980_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_name_1982_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_a_1923_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_clashes_1978_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*3, v___x_1983_);
v_a_1925_ = v___x_1985_;
goto v___jp_1924_;
}
}
}
}
else
{
lean_dec(v_a_1923_);
v_a_1925_ = v_b_1912_;
goto v___jp_1924_;
}
v___jp_1924_:
{
size_t v___x_1926_; size_t v___x_1927_; 
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_add(v_i_1910_, v___x_1926_);
v_i_1910_ = v___x_1927_;
v_b_1912_ = v_a_1925_;
goto _start;
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_b_1912_);
lean_dec_ref(v___x_1908_);
v_a_1990_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1992_ = v___x_1922_;
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1922_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2002_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1994_ = lean_io_error_to_string(v_a_1990_);
v___x_1995_ = 3;
v___x_1996_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set_uint8(v___x_1996_, sizeof(void*)*1, v___x_1995_);
lean_inc_ref(v___y_1913_);
v___x_1997_ = lean_apply_2(v___y_1913_, v___x_1996_, lean_box(0));
v___x_1998_ = lean_box(0);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1998_);
v___x_2000_ = v___x_1992_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v___x_2003_; 
lean_dec_ref(v___x_1908_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_b_1912_);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2004_, lean_object* v_as_2005_, lean_object* v_i_2006_, lean_object* v_stop_2007_, lean_object* v_b_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
size_t v_i_boxed_2011_; size_t v_stop_boxed_2012_; lean_object* v_res_2013_; 
v_i_boxed_2011_ = lean_unbox_usize(v_i_2006_);
lean_dec(v_i_2006_);
v_stop_boxed_2012_ = lean_unbox_usize(v_stop_2007_);
lean_dec(v_stop_2007_);
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2004_, v_as_2005_, v_i_boxed_2011_, v_stop_boxed_2012_, v_b_2008_, v___y_2009_);
lean_dec_ref(v___y_2009_);
lean_dec_ref(v_as_2005_);
return v_res_2013_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2023_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v___x_2024_ = lean_unsigned_to_nat(4u);
v___x_2025_ = lean_mk_empty_array_with_capacity(v___x_2024_);
v___x_2026_ = lean_array_push(v___x_2025_, v___x_2023_);
return v___x_2026_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2028_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6);
v___x_2029_ = lean_array_push(v___x_2028_, v___x_2027_);
return v___x_2029_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10(void){
_start:
{
uint32_t v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = 4;
v___x_2035_ = lean_uint32_to_uint8(v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2053_, lean_object* v_rootDeps_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___y_2058_; lean_object* v_lakeEnv_2063_; lean_object* v_lakeArgs_x3f_2064_; lean_object* v_packages_2065_; uint8_t v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2212_; lean_object* v___y_2213_; uint8_t v___y_2214_; lean_object* v___x_2217_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2231_; lean_object* v___y_2232_; uint8_t v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2245_; lean_object* v___y_2246_; uint8_t v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___x_2253_; lean_object* v_baseName_2254_; lean_object* v_dir_2255_; lean_object* v_config_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v_lakeEnv_2063_ = lean_ctor_get(v_ws_2053_, 0);
lean_inc_ref(v_lakeEnv_2063_);
v_lakeArgs_x3f_2064_ = lean_ctor_get(v_ws_2053_, 3);
lean_inc(v_lakeArgs_x3f_2064_);
v_packages_2065_ = lean_ctor_get(v_ws_2053_, 4);
lean_inc_ref(v_packages_2065_);
lean_dec_ref(v_ws_2053_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2253_ = lean_array_fget(v_packages_2065_, v___x_2217_);
lean_dec_ref(v_packages_2065_);
v_baseName_2254_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_baseName_2254_);
v_dir_2255_ = lean_ctor_get(v___x_2253_, 4);
lean_inc_ref_n(v_dir_2255_, 2);
v_config_2256_ = lean_ctor_get(v___x_2253_, 6);
lean_inc_ref(v_config_2256_);
lean_dec(v___x_2253_);
v___x_2257_ = l_Lake_toolchainFileName;
v___x_2258_ = l_System_FilePath_join(v_dir_2255_, v___x_2257_);
v___x_2259_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2258_);
lean_dec_ref(v___x_2258_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2318_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2318_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2318_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v_src_2265_; lean_object* v_tc_x3f_2266_; lean_object* v_clashes_2267_; uint8_t v_fixed_2268_; lean_object* v___y_2292_; uint8_t v_fixedToolchain_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_fixedToolchain_2306_ = lean_ctor_get_uint8(v_config_2256_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_2256_);
v___x_2307_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2308_ = lean_array_get_size(v_rootDeps_2054_);
v___x_2309_ = lean_nat_dec_lt(v___x_2217_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_inc(v_a_2260_);
v_src_2265_ = v_baseName_2254_;
v_tc_x3f_2266_ = v_a_2260_;
v_clashes_2267_ = v___x_2307_;
v_fixed_2268_ = v_fixedToolchain_2306_;
goto v___jp_2264_;
}
else
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
lean_inc(v_a_2260_);
lean_inc(v_baseName_2254_);
v___x_2310_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2310_, 0, v_baseName_2254_);
lean_ctor_set(v___x_2310_, 1, v_a_2260_);
lean_ctor_set(v___x_2310_, 2, v___x_2307_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*3, v_fixedToolchain_2306_);
v___x_2311_ = lean_nat_dec_le(v___x_2308_, v___x_2308_);
if (v___x_2311_ == 0)
{
if (v___x_2309_ == 0)
{
lean_dec_ref_known(v___x_2310_, 3);
lean_inc(v_a_2260_);
v_src_2265_ = v_baseName_2254_;
v_tc_x3f_2266_ = v_a_2260_;
v_clashes_2267_ = v___x_2307_;
v_fixed_2268_ = v_fixedToolchain_2306_;
goto v___jp_2264_;
}
else
{
size_t v___x_2312_; size_t v___x_2313_; lean_object* v___x_2314_; 
lean_dec(v_baseName_2254_);
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = lean_usize_of_nat(v___x_2308_);
lean_inc_ref(v_dir_2255_);
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2255_, v_rootDeps_2054_, v___x_2312_, v___x_2313_, v___x_2310_, v_a_2055_);
v___y_2292_ = v___x_2314_;
goto v___jp_2291_;
}
}
else
{
size_t v___x_2315_; size_t v___x_2316_; lean_object* v___x_2317_; 
lean_dec(v_baseName_2254_);
v___x_2315_ = ((size_t)0ULL);
v___x_2316_ = lean_usize_of_nat(v___x_2308_);
lean_inc_ref(v_dir_2255_);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2255_, v_rootDeps_2054_, v___x_2315_, v___x_2316_, v___x_2310_, v_a_2055_);
v___y_2292_ = v___x_2317_;
goto v___jp_2291_;
}
}
v___jp_2264_:
{
lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2269_ = lean_array_get_size(v_clashes_2267_);
v___x_2270_ = lean_nat_dec_lt(v___x_2217_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v_clashes_2267_);
lean_dec(v_src_2265_);
if (lean_obj_tag(v_tc_x3f_2266_) == 1)
{
lean_object* v_val_2271_; lean_object* v_rootToolchainFile_2272_; 
v_val_2271_ = lean_ctor_get(v_tc_x3f_2266_, 0);
lean_inc(v_val_2271_);
lean_dec_ref_known(v_tc_x3f_2266_, 1);
v_rootToolchainFile_2272_ = l_Lake_joinRelative(v_dir_2255_, v___x_2257_);
if (lean_obj_tag(v_a_2260_) == 0)
{
lean_del_object(v___x_2262_);
v___y_2212_ = v_val_2271_;
v___y_2213_ = v_rootToolchainFile_2272_;
v___y_2214_ = v___x_2270_;
goto v___jp_2211_;
}
else
{
lean_object* v_val_2273_; uint8_t v___x_2274_; 
v_val_2273_ = lean_ctor_get(v_a_2260_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v_a_2260_, 1);
lean_inc(v_val_2271_);
v___x_2274_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2273_, v_val_2271_);
if (v___x_2274_ == 0)
{
lean_del_object(v___x_2262_);
v___y_2212_ = v_val_2271_;
v___y_2213_ = v_rootToolchainFile_2272_;
v___y_2214_ = v___x_2274_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
lean_dec_ref(v_rootToolchainFile_2272_);
lean_dec(v_val_2271_);
lean_dec(v_lakeArgs_x3f_2064_);
lean_dec_ref(v_lakeEnv_2063_);
v___x_2275_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2055_);
v___x_2276_ = lean_apply_2(v_a_2055_, v___x_2275_, lean_box(0));
v___x_2277_ = lean_box(0);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2277_);
v___x_2279_ = v___x_2262_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
lean_dec(v_tc_x3f_2266_);
lean_dec(v_a_2260_);
lean_dec_ref(v_dir_2255_);
lean_dec(v_lakeArgs_x3f_2064_);
lean_dec_ref(v_lakeEnv_2063_);
v___x_2281_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2055_);
v___x_2282_ = lean_apply_2(v_a_2055_, v___x_2281_, lean_box(0));
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2282_);
v___x_2284_ = v___x_2262_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
else
{
lean_del_object(v___x_2262_);
lean_dec(v_a_2260_);
lean_dec_ref(v_dir_2255_);
lean_dec(v_lakeArgs_x3f_2064_);
lean_dec_ref(v_lakeEnv_2063_);
if (lean_obj_tag(v_tc_x3f_2266_) == 1)
{
if (v_fixed_2268_ == 0)
{
lean_object* v_val_2286_; lean_object* v___x_2287_; 
v_val_2286_ = lean_ctor_get(v_tc_x3f_2266_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v_tc_x3f_2266_, 1);
v___x_2287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2245_ = v_src_2265_;
v___y_2246_ = v_val_2286_;
v___y_2247_ = v___x_2270_;
v___y_2248_ = v_clashes_2267_;
v___y_2249_ = v___x_2269_;
v___y_2250_ = v___x_2287_;
goto v___jp_2244_;
}
else
{
lean_object* v_val_2288_; lean_object* v___x_2289_; 
v_val_2288_ = lean_ctor_get(v_tc_x3f_2266_, 0);
lean_inc(v_val_2288_);
lean_dec_ref_known(v_tc_x3f_2266_, 1);
v___x_2289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2245_ = v_src_2265_;
v___y_2246_ = v_val_2288_;
v___y_2247_ = v___x_2270_;
v___y_2248_ = v_clashes_2267_;
v___y_2249_ = v___x_2269_;
v___y_2250_ = v___x_2289_;
goto v___jp_2244_;
}
}
else
{
lean_object* v___x_2290_; 
lean_dec(v_tc_x3f_2266_);
lean_dec(v_src_2265_);
v___x_2290_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2219_ = v_clashes_2267_;
v___y_2220_ = v___x_2269_;
v___y_2221_ = v___x_2290_;
goto v___jp_2218_;
}
}
}
v___jp_2291_:
{
if (lean_obj_tag(v___y_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v_src_2294_; lean_object* v_tc_x3f_2295_; lean_object* v_clashes_2296_; uint8_t v_fixed_2297_; 
v_a_2293_ = lean_ctor_get(v___y_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___y_2292_, 1);
v_src_2294_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_src_2294_);
v_tc_x3f_2295_ = lean_ctor_get(v_a_2293_, 1);
lean_inc(v_tc_x3f_2295_);
v_clashes_2296_ = lean_ctor_get(v_a_2293_, 2);
lean_inc_ref(v_clashes_2296_);
v_fixed_2297_ = lean_ctor_get_uint8(v_a_2293_, sizeof(void*)*3);
lean_dec(v_a_2293_);
v_src_2265_ = v_src_2294_;
v_tc_x3f_2266_ = v_tc_x3f_2295_;
v_clashes_2267_ = v_clashes_2296_;
v_fixed_2268_ = v_fixed_2297_;
goto v___jp_2264_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_del_object(v___x_2262_);
lean_dec(v_a_2260_);
lean_dec_ref(v_dir_2255_);
lean_dec(v_lakeArgs_x3f_2064_);
lean_dec_ref(v_lakeEnv_2063_);
v_a_2298_ = lean_ctor_get(v___y_2292_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___y_2292_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___y_2292_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___y_2292_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_config_2256_);
lean_dec_ref(v_dir_2255_);
lean_dec(v_baseName_2254_);
lean_dec(v_lakeArgs_x3f_2064_);
lean_dec_ref(v_lakeEnv_2063_);
v_a_2319_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2321_ = v___x_2259_;
v_isShared_2322_ = v_isSharedCheck_2331_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2259_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2331_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2323_ = lean_io_error_to_string(v_a_2319_);
v___x_2324_ = 3;
v___x_2325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2325_, 0, v___x_2323_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*1, v___x_2324_);
lean_inc_ref(v_a_2055_);
v___x_2326_ = lean_apply_2(v_a_2055_, v___x_2325_, lean_box(0));
v___x_2327_ = lean_box(0);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2327_);
v___x_2329_ = v___x_2321_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
v___jp_2057_:
{
uint8_t v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2059_ = 2;
v___x_2060_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2060_, 0, v___y_2058_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*1, v___x_2059_);
lean_inc_ref(v_a_2055_);
v___x_2061_ = lean_apply_2(v_a_2055_, v___x_2060_, lean_box(0));
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
v___jp_2066_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_inc_ref(v___y_2068_);
v___x_2071_ = lean_string_append(v___y_2068_, v___y_2070_);
v___x_2072_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2073_ = lean_string_append(v___x_2071_, v___x_2072_);
v___x_2074_ = 1;
v___x_2075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*1, v___x_2074_);
lean_inc_ref(v_a_2055_);
v___x_2076_ = lean_apply_2(v_a_2055_, v___x_2075_, lean_box(0));
v___x_2077_ = l_IO_FS_writeFile(v___y_2069_, v___y_2070_);
lean_dec_ref(v___y_2069_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_dec_ref_known(v___x_2077_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2064_) == 1)
{
lean_object* v_elan_x3f_2078_; 
v_elan_x3f_2078_ = lean_ctor_get(v_lakeEnv_2063_, 2);
if (lean_obj_tag(v_elan_x3f_2078_) == 1)
{
lean_object* v_val_2079_; lean_object* v_val_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_elan_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_val_2079_ = lean_ctor_get(v_lakeArgs_x3f_2064_, 0);
lean_inc(v_val_2079_);
lean_dec_ref_known(v_lakeArgs_x3f_2064_, 1);
v_val_2080_ = lean_ctor_get(v_elan_x3f_2078_, 0);
v___x_2081_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2055_);
v___x_2082_ = lean_apply_2(v_a_2055_, v___x_2081_, lean_box(0));
v___x_2083_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2084_ = lean_ctor_get(v_val_2080_, 1);
lean_inc_ref(v_elan_2084_);
v___x_2085_ = 1;
v___x_2086_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2087_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2088_ = lean_array_push(v___x_2087_, v___y_2070_);
v___x_2089_ = lean_array_push(v___x_2088_, v___x_2086_);
v___x_2090_ = l_Array_append___redArg(v___x_2089_, v_val_2079_);
lean_dec(v_val_2079_);
v___x_2091_ = lean_box(0);
v___x_2092_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2063_);
v___x_2093_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2093_, 0, v___x_2083_);
lean_ctor_set(v___x_2093_, 1, v_elan_2084_);
lean_ctor_set(v___x_2093_, 2, v___x_2090_);
lean_ctor_set(v___x_2093_, 3, v___x_2091_);
lean_ctor_set(v___x_2093_, 4, v___x_2092_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*5, v___x_2085_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*5 + 1, v___y_2067_);
v___x_2094_ = lean_io_process_spawn(v___x_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = lean_io_process_child_wait(v___x_2083_, v_a_2095_);
lean_dec(v_a_2095_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; uint32_t v___x_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = lean_unbox_uint32(v_a_2097_);
lean_dec(v_a_2097_);
v___x_2099_ = lean_uint32_to_uint8(v___x_2098_);
v___x_2100_ = lean_io_exit(v___x_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2121_; 
v_a_2109_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2111_ = v___x_2100_;
v_isShared_2112_ = v_isSharedCheck_2121_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2100_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2121_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2113_ = lean_io_error_to_string(v_a_2109_);
v___x_2114_ = 3;
v___x_2115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1, v___x_2114_);
lean_inc_ref(v_a_2055_);
v___x_2116_ = lean_apply_2(v_a_2055_, v___x_2115_, lean_box(0));
v___x_2117_ = lean_box(0);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2117_);
v___x_2119_ = v___x_2111_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2134_; 
v_a_2122_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2124_ = v___x_2096_;
v_isShared_2125_ = v_isSharedCheck_2134_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2096_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2134_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2126_ = lean_io_error_to_string(v_a_2122_);
v___x_2127_ = 3;
v___x_2128_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*1, v___x_2127_);
lean_inc_ref(v_a_2055_);
v___x_2129_ = lean_apply_2(v_a_2055_, v___x_2128_, lean_box(0));
v___x_2130_ = lean_box(0);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2130_);
v___x_2132_ = v___x_2124_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2147_; 
v_a_2135_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2137_ = v___x_2094_;
v_isShared_2138_ = v_isSharedCheck_2147_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2094_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2147_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2139_ = lean_io_error_to_string(v_a_2135_);
v___x_2140_ = 3;
v___x_2141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1, v___x_2140_);
lean_inc_ref(v_a_2055_);
v___x_2142_ = lean_apply_2(v_a_2055_, v___x_2141_, lean_box(0));
v___x_2143_ = lean_box(0);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2143_);
v___x_2145_ = v___x_2137_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref_known(v_lakeArgs_x3f_2064_, 1);
lean_dec_ref(v___y_2070_);
lean_dec_ref(v_lakeEnv_2063_);
v___x_2148_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2055_);
v___x_2149_ = lean_apply_2(v_a_2055_, v___x_2148_, lean_box(0));
v___x_2150_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2151_ = lean_io_exit(v___x_2150_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2172_; 
v_a_2160_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2162_ = v___x_2151_;
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2151_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2164_ = lean_io_error_to_string(v_a_2160_);
v___x_2165_ = 3;
v___x_2166_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*1, v___x_2165_);
lean_inc_ref(v_a_2055_);
v___x_2167_ = lean_apply_2(v_a_2055_, v___x_2166_, lean_box(0));
v___x_2168_ = lean_box(0);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2168_);
v___x_2170_ = v___x_2162_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v___y_2070_);
lean_dec(v_lakeArgs_x3f_2064_);
lean_dec_ref(v_lakeEnv_2063_);
v___x_2173_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2055_);
v___x_2174_ = lean_apply_2(v_a_2055_, v___x_2173_, lean_box(0));
v___x_2175_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2176_ = lean_io_exit(v___x_2175_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2197_; 
v_a_2185_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2187_ = v___x_2176_;
v_isShared_2188_ = v_isSharedCheck_2197_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2176_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2197_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2189_ = lean_io_error_to_string(v_a_2185_);
v___x_2190_ = 3;
v___x_2191_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*1, v___x_2190_);
lean_inc_ref(v_a_2055_);
v___x_2192_ = lean_apply_2(v_a_2055_, v___x_2191_, lean_box(0));
v___x_2193_ = lean_box(0);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2193_);
v___x_2195_ = v___x_2187_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v___y_2070_);
lean_dec(v_lakeArgs_x3f_2064_);
lean_dec_ref(v_lakeEnv_2063_);
v_a_2198_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2200_ = v___x_2077_;
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2077_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2202_ = lean_io_error_to_string(v_a_2198_);
v___x_2203_ = 3;
v___x_2204_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v___x_2203_);
lean_inc_ref(v_a_2055_);
v___x_2205_ = lean_apply_2(v_a_2055_, v___x_2204_, lean_box(0));
v___x_2206_ = lean_box(0);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2206_);
v___x_2208_ = v___x_2200_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
v___jp_2211_:
{
lean_object* v___x_2215_; lean_object* v_toString_2216_; 
v___x_2215_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2216_ = lean_ctor_get(v___y_2212_, 0);
lean_inc_ref(v_toString_2216_);
lean_dec_ref(v___y_2212_);
v___y_2067_ = v___y_2214_;
v___y_2068_ = v___x_2215_;
v___y_2069_ = v___y_2213_;
v___y_2070_ = v_toString_2216_;
goto v___jp_2066_;
}
v___jp_2218_:
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_nat_dec_lt(v___x_2217_, v___y_2220_);
if (v___x_2222_ == 0)
{
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
v___y_2058_ = v___y_2221_;
goto v___jp_2057_;
}
else
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_nat_dec_le(v___y_2220_, v___y_2220_);
if (v___x_2223_ == 0)
{
if (v___x_2222_ == 0)
{
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
v___y_2058_ = v___y_2221_;
goto v___jp_2057_;
}
else
{
size_t v___x_2224_; size_t v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((size_t)0ULL);
v___x_2225_ = lean_usize_of_nat(v___y_2220_);
lean_dec(v___y_2220_);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2219_, v___x_2224_, v___x_2225_, v___y_2221_);
lean_dec_ref(v___y_2219_);
v___y_2058_ = v___x_2226_;
goto v___jp_2057_;
}
}
else
{
size_t v___x_2227_; size_t v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = ((size_t)0ULL);
v___x_2228_ = lean_usize_of_nat(v___y_2220_);
lean_dec(v___y_2220_);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2219_, v___x_2227_, v___x_2228_, v___y_2221_);
lean_dec_ref(v___y_2219_);
v___y_2058_ = v___x_2229_;
goto v___jp_2057_;
}
}
}
v___jp_2230_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_inc_ref(v___y_2236_);
v___x_2238_ = lean_string_append(v___y_2236_, v___y_2237_);
lean_dec_ref(v___y_2237_);
v___x_2239_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
v___x_2241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2231_, v___y_2233_);
v___x_2242_ = lean_string_append(v___x_2240_, v___x_2241_);
lean_dec_ref(v___x_2241_);
v___x_2243_ = lean_string_append(v___x_2242_, v___y_2232_);
v___y_2219_ = v___y_2234_;
v___y_2220_ = v___y_2235_;
v___y_2221_ = v___x_2243_;
goto v___jp_2218_;
}
v___jp_2244_:
{
lean_object* v___x_2251_; lean_object* v_toString_2252_; 
v___x_2251_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2252_ = lean_ctor_get(v___y_2246_, 0);
lean_inc_ref(v_toString_2252_);
lean_dec_ref(v___y_2246_);
v___y_2231_ = v___y_2245_;
v___y_2232_ = v___y_2250_;
v___y_2233_ = v___y_2247_;
v___y_2234_ = v___y_2248_;
v___y_2235_ = v___y_2249_;
v___y_2236_ = v___x_2251_;
v___y_2237_ = v_toString_2252_;
goto v___jp_2230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2332_, lean_object* v_rootDeps_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2332_, v_rootDeps_2333_, v_a_2334_);
lean_dec_ref(v_a_2334_);
lean_dec_ref(v_rootDeps_2333_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2337_, lean_object* v_dep_2338_, lean_object* v_ws_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2339_, v_pkg_2337_, v_dep_2338_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v_fst_2345_; lean_object* v_snd_2346_; lean_object* v___x_2347_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v_fst_2345_ = lean_ctor_get(v_a_2344_, 0);
lean_inc_n(v_fst_2345_, 2);
v_snd_2346_ = lean_ctor_get(v_a_2344_, 1);
lean_inc(v_snd_2346_);
lean_dec(v_a_2344_);
v___x_2347_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2345_, v_snd_2346_, v_a_2341_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2364_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2364_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_snd_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2362_; 
v_snd_2352_ = lean_ctor_get(v_a_2348_, 1);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v_a_2348_, 0);
lean_dec(v_unused_2363_);
v___x_2354_ = v_a_2348_;
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_snd_2352_);
lean_dec(v_a_2348_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v_fst_2345_);
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_fst_2345_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_snd_2352_);
v___x_2357_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2357_);
v___x_2359_ = v___x_2350_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_fst_2345_);
v_a_2365_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2347_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2347_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
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
return v___x_2343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2373_, lean_object* v_dep_2374_, lean_object* v_ws_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2373_, v_dep_2374_, v_ws_2375_, v_a_2376_, v_a_2377_);
lean_dec_ref(v_a_2377_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2380_, lean_object* v_ws_2381_, lean_object* v_pkg_2382_, lean_object* v_dep_2383_, lean_object* v_a_2384_){
_start:
{
uint8_t v___y_2387_; lean_object* v___y_2388_; lean_object* v_name_2418_; lean_object* v___x_2419_; 
v_name_2418_ = lean_ctor_get(v_dep_2383_, 0);
v___x_2419_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2384_, v_name_2418_);
if (lean_obj_tag(v___x_2419_) == 1)
{
lean_object* v_val_2420_; lean_object* v_lakeEnv_2421_; lean_object* v_packages_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_config_2425_; lean_object* v_dir_2426_; lean_object* v_toWorkspaceConfig_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_dec_ref(v_dep_2383_);
lean_dec_ref(v_pkg_2382_);
v_val_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_val_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v_lakeEnv_2421_ = lean_ctor_get(v_ws_2381_, 0);
lean_inc_ref(v_lakeEnv_2421_);
v_packages_2422_ = lean_ctor_get(v_ws_2381_, 4);
lean_inc_ref(v_packages_2422_);
lean_dec_ref(v_ws_2381_);
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = lean_array_fget(v_packages_2422_, v___x_2423_);
lean_dec_ref(v_packages_2422_);
v_config_2425_ = lean_ctor_get(v___x_2424_, 6);
lean_inc_ref(v_config_2425_);
v_dir_2426_ = lean_ctor_get(v___x_2424_, 4);
lean_inc_ref(v_dir_2426_);
lean_dec(v___x_2424_);
v_toWorkspaceConfig_2427_ = lean_ctor_get(v_config_2425_, 0);
lean_inc_ref(v_toWorkspaceConfig_2427_);
lean_dec_ref(v_config_2425_);
v___x_2428_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2427_);
v___x_2429_ = l_Lake_PackageEntry_materialize(v_val_2420_, v_lakeEnv_2421_, v_dir_2426_, v___x_2428_, v___y_2380_);
lean_dec_ref(v_lakeEnv_2421_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2438_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2430_);
lean_ctor_set(v___x_2434_, 1, v_a_2384_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v_a_2384_);
v_a_2439_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2429_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2429_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
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
else
{
lean_object* v_wsIdx_2447_; lean_object* v_relDir_2448_; uint8_t v___y_2450_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
lean_dec(v___x_2419_);
v_wsIdx_2447_ = lean_ctor_get(v_pkg_2382_, 0);
lean_inc(v_wsIdx_2447_);
v_relDir_2448_ = lean_ctor_get(v_pkg_2382_, 5);
lean_inc_ref(v_relDir_2448_);
lean_dec_ref(v_pkg_2382_);
v___x_2454_ = lean_unsigned_to_nat(0u);
v___x_2455_ = lean_nat_dec_eq(v_wsIdx_2447_, v___x_2454_);
lean_dec(v_wsIdx_2447_);
if (v___x_2455_ == 0)
{
uint8_t v___x_2456_; 
v___x_2456_ = 1;
v___y_2450_ = v___x_2456_;
goto v___jp_2449_;
}
else
{
uint8_t v___x_2457_; 
v___x_2457_ = 0;
v___y_2450_ = v___x_2457_;
goto v___jp_2449_;
}
v___jp_2449_:
{
lean_object* v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2452_ = lean_string_dec_eq(v_relDir_2448_, v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lake_joinRelative(v_relDir_2448_, v___x_2451_);
v___y_2387_ = v___y_2450_;
v___y_2388_ = v___x_2453_;
goto v___jp_2386_;
}
else
{
v___y_2387_ = v___y_2450_;
v___y_2388_ = v_relDir_2448_;
goto v___jp_2386_;
}
}
}
v___jp_2386_:
{
lean_object* v_lakeEnv_2389_; lean_object* v_packages_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_config_2393_; lean_object* v_dir_2394_; lean_object* v_toWorkspaceConfig_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_lakeEnv_2389_ = lean_ctor_get(v_ws_2381_, 0);
lean_inc_ref(v_lakeEnv_2389_);
v_packages_2390_ = lean_ctor_get(v_ws_2381_, 4);
lean_inc_ref(v_packages_2390_);
lean_dec_ref(v_ws_2381_);
v___x_2391_ = lean_unsigned_to_nat(0u);
v___x_2392_ = lean_array_fget(v_packages_2390_, v___x_2391_);
lean_dec_ref(v_packages_2390_);
v_config_2393_ = lean_ctor_get(v___x_2392_, 6);
lean_inc_ref(v_config_2393_);
v_dir_2394_ = lean_ctor_get(v___x_2392_, 4);
lean_inc_ref(v_dir_2394_);
lean_dec(v___x_2392_);
v_toWorkspaceConfig_2395_ = lean_ctor_get(v_config_2393_, 0);
lean_inc_ref(v_toWorkspaceConfig_2395_);
lean_dec_ref(v_config_2393_);
v___x_2396_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2395_);
v___x_2397_ = l_Lake_Dependency_materialize(v_dep_2383_, v___y_2387_, v_lakeEnv_2389_, v_dir_2394_, v___x_2396_, v___y_2388_, v___y_2380_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2409_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2409_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2409_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v_manifestEntry_2402_; lean_object* v_name_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v_manifestEntry_2402_ = lean_ctor_get(v_a_2398_, 4);
v_name_2403_ = lean_ctor_get(v_manifestEntry_2402_, 0);
lean_inc_ref(v_manifestEntry_2402_);
lean_inc(v_name_2403_);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2403_, v_manifestEntry_2402_, v_a_2384_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_a_2398_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2405_);
v___x_2407_ = v___x_2400_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_a_2384_);
v_a_2410_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2397_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2397_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2458_, lean_object* v_ws_2459_, lean_object* v_pkg_2460_, lean_object* v_dep_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2458_, v_ws_2459_, v_pkg_2460_, v_dep_2461_, v_a_2462_);
lean_dec_ref(v___y_2458_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2465_, lean_object* v_dep_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_manifestEntry_2469_; lean_object* v_pkgDir_2470_; lean_object* v_name_2471_; lean_object* v_manifestFile_x3f_2472_; lean_object* v___y_2474_; lean_object* v_fst_2475_; lean_object* v_snd_2476_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v_val_2536_; lean_object* v___y_2564_; 
v_manifestEntry_2469_ = lean_ctor_get(v_dep_2466_, 4);
v_pkgDir_2470_ = lean_ctor_get(v_dep_2466_, 0);
v_name_2471_ = lean_ctor_get(v_manifestEntry_2469_, 0);
v_manifestFile_x3f_2472_ = lean_ctor_get(v_manifestEntry_2469_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2472_) == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2470_);
v___x_2585_ = l_Lake_joinRelative(v_pkgDir_2470_, v___x_2584_);
v___y_2564_ = v___x_2585_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2586_; lean_object* v___x_2587_; 
v_val_2586_ = lean_ctor_get(v_manifestFile_x3f_2472_, 0);
lean_inc(v_val_2586_);
lean_inc_ref(v_pkgDir_2470_);
v___x_2587_ = l_Lake_joinRelative(v_pkgDir_2470_, v_val_2586_);
v___y_2564_ = v___x_2587_;
goto v___jp_2563_;
}
v___jp_2473_:
{
if (lean_obj_tag(v_fst_2475_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2506_; 
lean_inc(v_name_2471_);
lean_dec_ref(v_dep_2466_);
v_a_2477_ = lean_ctor_get(v_fst_2475_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_fst_2475_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2479_ = v_fst_2475_;
v_isShared_2480_ = v_isSharedCheck_2506_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v_fst_2475_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2506_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
if (lean_obj_tag(v_a_2477_) == 11)
{
uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
lean_dec_ref_known(v_a_2477_, 2);
v___x_2481_ = 0;
v___x_2482_ = l_Lean_Name_toString(v_name_2471_, v___x_2481_);
v___x_2483_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2484_ = lean_string_append(v___x_2482_, v___x_2483_);
v___x_2485_ = lean_string_append(v___x_2484_, v___y_2474_);
lean_dec_ref(v___y_2474_);
v___x_2486_ = 2;
v___x_2487_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set_uint8(v___x_2487_, sizeof(void*)*1, v___x_2486_);
v___x_2488_ = lean_apply_2(v___y_2465_, v___x_2487_, lean_box(0));
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v_snd_2476_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v___x_2489_);
v___x_2491_ = v___x_2479_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
else
{
uint8_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_dec_ref(v___y_2474_);
v___x_2493_ = 0;
v___x_2494_ = l_Lean_Name_toString(v_name_2471_, v___x_2493_);
v___x_2495_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2496_ = lean_string_append(v___x_2494_, v___x_2495_);
v___x_2497_ = lean_io_error_to_string(v_a_2477_);
v___x_2498_ = lean_string_append(v___x_2496_, v___x_2497_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = 2;
v___x_2500_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*1, v___x_2499_);
v___x_2501_ = lean_apply_2(v___y_2465_, v___x_2500_, lean_box(0));
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v_snd_2476_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v___x_2502_);
v___x_2504_ = v___x_2479_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2465_);
v_a_2507_ = lean_ctor_get(v_fst_2475_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_fst_2475_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2509_ = v_fst_2475_;
v_isShared_2510_ = v_isSharedCheck_2531_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v_fst_2475_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2531_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_packages_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v_packages_2511_ = lean_ctor_get(v_a_2507_, 3);
lean_inc_ref(v_packages_2511_);
lean_dec(v_a_2507_);
v___x_2512_ = lean_unsigned_to_nat(0u);
v___x_2513_ = lean_array_get_size(v_packages_2511_);
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_nat_dec_lt(v___x_2512_, v___x_2513_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
lean_dec_ref(v_packages_2511_);
lean_dec_ref(v_dep_2466_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v_snd_2476_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set_tag(v___x_2509_, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2516_);
v___x_2518_ = v___x_2509_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_nat_dec_le(v___x_2513_, v___x_2513_);
if (v___x_2520_ == 0)
{
if (v___x_2515_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_dec_ref(v_packages_2511_);
lean_dec_ref(v_dep_2466_);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2514_);
lean_ctor_set(v___x_2521_, 1, v_snd_2476_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set_tag(v___x_2509_, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2521_);
v___x_2523_ = v___x_2509_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
lean_del_object(v___x_2509_);
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2513_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2466_, v_packages_2511_, v___x_2525_, v___x_2526_, v___x_2514_, v_snd_2476_);
lean_dec_ref(v_packages_2511_);
return v___x_2527_;
}
}
else
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
lean_del_object(v___x_2509_);
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = lean_usize_of_nat(v___x_2513_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2466_, v_packages_2511_, v___x_2528_, v___x_2529_, v___x_2514_, v_snd_2476_);
lean_dec_ref(v_packages_2511_);
return v___x_2530_;
}
}
}
}
}
v___jp_2532_:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = lean_array_get_size(v___y_2534_);
v___x_2538_ = lean_nat_dec_lt(v___y_2533_, v___x_2537_);
if (v___x_2538_ == 0)
{
v___y_2474_ = v___y_2535_;
v_fst_2475_ = v_val_2536_;
v_snd_2476_ = v_a_2467_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_nat_dec_le(v___x_2537_, v___x_2537_);
if (v___x_2540_ == 0)
{
if (v___x_2538_ == 0)
{
v___y_2474_ = v___y_2535_;
v_fst_2475_ = v_val_2536_;
v_snd_2476_ = v_a_2467_;
goto v___jp_2473_;
}
else
{
size_t v___x_2541_; size_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2537_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2534_, v___x_2541_, v___x_2542_, v___x_2539_, v___y_2465_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_dec_ref_known(v___x_2543_, 1);
v___y_2474_ = v___y_2535_;
v_fst_2475_ = v_val_2536_;
v_snd_2476_ = v_a_2467_;
goto v___jp_2473_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v_val_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v_a_2467_);
lean_dec_ref(v_dep_2466_);
lean_dec_ref(v___y_2465_);
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
else
{
size_t v___x_2552_; size_t v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((size_t)0ULL);
v___x_2553_ = lean_usize_of_nat(v___x_2537_);
v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2534_, v___x_2552_, v___x_2553_, v___x_2539_, v___y_2465_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_dec_ref_known(v___x_2554_, 1);
v___y_2474_ = v___y_2535_;
v_fst_2475_ = v_val_2536_;
v_snd_2476_ = v_a_2467_;
goto v___jp_2473_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_val_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v_a_2467_);
lean_dec_ref(v_dep_2466_);
lean_dec_ref(v___y_2465_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
v___jp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2564_);
v___x_2567_ = l_Lake_Manifest_load(v___y_2564_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 1);
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
v___y_2533_ = v___x_2565_;
v___y_2534_ = v___x_2566_;
v___y_2535_ = v___y_2564_;
v_val_2536_ = v___x_2573_;
goto v___jp_2532_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
v_a_2576_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2567_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2567_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 0);
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
v___y_2533_ = v___x_2565_;
v___y_2534_ = v___x_2566_;
v___y_2535_ = v___y_2564_;
v_val_2536_ = v___x_2581_;
goto v___jp_2532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2588_, lean_object* v_dep_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2588_, v_dep_2589_, v_a_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2597_, v___y_2595_, v___y_2593_, v___y_2594_, v___y_2596_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2603_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_fst_2601_ = lean_ctor_get(v_a_2600_, 0);
lean_inc_n(v_fst_2601_, 2);
v_snd_2602_ = lean_ctor_get(v_a_2600_, 1);
lean_inc(v_snd_2602_);
lean_dec(v_a_2600_);
v___x_2603_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2597_, v_fst_2601_, v_snd_2602_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2620_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2620_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2620_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_snd_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2618_; 
v_snd_2608_ = lean_ctor_get(v_a_2604_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v_a_2604_, 0);
lean_dec(v_unused_2619_);
v___x_2610_ = v_a_2604_;
v_isShared_2611_ = v_isSharedCheck_2618_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snd_2608_);
lean_dec(v_a_2604_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2618_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v_fst_2601_);
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_fst_2601_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_snd_2608_);
v___x_2613_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2613_);
v___x_2615_ = v___x_2606_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
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
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_fst_2601_);
v_a_2621_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2603_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2603_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_dec_ref(v___y_2597_);
return v___x_2599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2636_, lean_object* v_ws_2637_, lean_object* v_toUpdate_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___y_2642_; lean_object* v___y_2647_; lean_object* v_fst_2648_; lean_object* v_snd_2649_; lean_object* v_packages_2668_; lean_object* v___x_2669_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v_val_2674_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___x_2722_; lean_object* v_baseName_2723_; lean_object* v_dir_2724_; lean_object* v_config_2725_; lean_object* v_relManifestFile_2726_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; uint8_t v_fst_2731_; lean_object* v_snd_2732_; lean_object* v_packagesDir_x3f_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2794_; lean_object* v___y_2795_; uint8_t v___x_2798_; lean_object* v_rootName_2799_; lean_object* v_fst_2801_; lean_object* v_snd_2802_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v_val_2853_; lean_object* v___x_2879_; 
v_packages_2668_ = lean_ctor_get(v_ws_2637_, 4);
v___x_2669_ = lean_unsigned_to_nat(0u);
v___x_2722_ = lean_array_fget_borrowed(v_packages_2668_, v___x_2669_);
v_baseName_2723_ = lean_ctor_get(v___x_2722_, 1);
v_dir_2724_ = lean_ctor_get(v___x_2722_, 4);
v_config_2725_ = lean_ctor_get(v___x_2722_, 6);
v_relManifestFile_2726_ = lean_ctor_get(v___x_2722_, 9);
v___x_2798_ = 0;
lean_inc(v_baseName_2723_);
v_rootName_2799_ = l_Lean_Name_toString(v_baseName_2723_, v___x_2798_);
lean_inc_ref(v_relManifestFile_2726_);
lean_inc_ref(v_dir_2724_);
v___x_2850_ = l_Lake_joinRelative(v_dir_2724_, v_relManifestFile_2726_);
v___x_2851_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2879_ = l_Lake_Manifest_load(v___x_2850_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set_tag(v___x_2882_, 1);
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
v_val_2853_ = v___x_2885_;
goto v___jp_2852_;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2879_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2879_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set_tag(v___x_2890_, 0);
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
v_val_2853_ = v___x_2893_;
goto v___jp_2852_;
}
}
}
v___jp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v___y_2642_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
v___jp_2646_:
{
if (lean_obj_tag(v_fst_2648_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_snd_2649_);
v_a_2650_ = lean_ctor_get(v_fst_2648_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_fst_2648_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2652_ = v_fst_2648_;
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v_fst_2648_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2654_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2655_ = lean_io_error_to_string(v_a_2650_);
v___x_2656_ = lean_string_append(v___x_2654_, v___x_2655_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = 3;
v___x_2658_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*1, v___x_2657_);
lean_inc_ref(v___y_2647_);
v___x_2659_ = lean_apply_2(v___y_2647_, v___x_2658_, lean_box(0));
v___x_2660_ = lean_box(0);
if (v_isShared_2653_ == 0)
{
lean_ctor_set_tag(v___x_2652_, 1);
lean_ctor_set(v___x_2652_, 0, v___x_2660_);
v___x_2662_ = v___x_2652_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec_ref(v_fst_2648_);
v___x_2665_ = lean_box(0);
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v_snd_2649_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
return v___x_2667_;
}
}
v___jp_2670_:
{
lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2675_ = lean_array_get_size(v___y_2672_);
v___x_2676_ = lean_nat_dec_lt(v___x_2669_, v___x_2675_);
if (v___x_2676_ == 0)
{
v___y_2647_ = v___y_2673_;
v_fst_2648_ = v_val_2674_;
v_snd_2649_ = v___y_2671_;
goto v___jp_2646_;
}
else
{
lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = lean_box(0);
v___x_2678_ = lean_nat_dec_le(v___x_2675_, v___x_2675_);
if (v___x_2678_ == 0)
{
if (v___x_2676_ == 0)
{
v___y_2647_ = v___y_2673_;
v_fst_2648_ = v_val_2674_;
v_snd_2649_ = v___y_2671_;
goto v___jp_2646_;
}
else
{
size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2675_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2672_, v___x_2679_, v___x_2680_, v___x_2677_, v___y_2673_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec_ref_known(v___x_2681_, 1);
v___y_2647_ = v___y_2673_;
v_fst_2648_ = v_val_2674_;
v_snd_2649_ = v___y_2671_;
goto v___jp_2646_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref(v_val_2674_);
lean_dec(v___y_2671_);
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2681_);
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
}
else
{
size_t v___x_2690_; size_t v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((size_t)0ULL);
v___x_2691_ = lean_usize_of_nat(v___x_2675_);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2672_, v___x_2690_, v___x_2691_, v___x_2677_, v___y_2673_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_dec_ref_known(v___x_2692_, 1);
v___y_2647_ = v___y_2673_;
v_fst_2648_ = v_val_2674_;
v_snd_2649_ = v___y_2671_;
goto v___jp_2646_;
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v_val_2674_);
lean_dec(v___y_2671_);
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
v___jp_2701_:
{
if (lean_obj_tag(v___y_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
v_a_2706_ = lean_ctor_get(v___y_2705_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___y_2705_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___y_2705_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___y_2705_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set_tag(v___x_2708_, 1);
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
v___y_2671_ = v___y_2702_;
v___y_2672_ = v___y_2703_;
v___y_2673_ = v___y_2704_;
v_val_2674_ = v___x_2711_;
goto v___jp_2670_;
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
v_a_2714_ = lean_ctor_get(v___y_2705_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___y_2705_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___y_2705_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___y_2705_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 0);
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
v___y_2671_ = v___y_2702_;
v___y_2672_ = v___y_2703_;
v___y_2673_ = v___y_2704_;
v_val_2674_ = v___x_2719_;
goto v___jp_2670_;
}
}
}
}
v___jp_2727_:
{
lean_object* v_toWorkspaceConfig_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v_toWorkspaceConfig_2733_ = lean_ctor_get(v_config_2725_, 0);
v___x_2734_ = l_System_FilePath_normalize(v___y_2729_);
lean_inc_ref(v_toWorkspaceConfig_2733_);
v___x_2735_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2733_);
lean_inc_ref(v___x_2735_);
v___x_2736_ = l_System_FilePath_normalize(v___x_2735_);
v___x_2737_ = lean_string_dec_eq(v___x_2734_, v___x_2736_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v___x_2734_);
if (v___x_2737_ == 0)
{
if (v_fst_2731_ == 0)
{
lean_dec_ref(v___x_2735_);
lean_dec_ref(v___y_2728_);
v___y_2642_ = v_snd_2732_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2738_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2739_ = lean_string_append(v___x_2738_, v___y_2728_);
v___x_2740_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2741_ = lean_string_append(v___x_2739_, v___x_2740_);
lean_inc_ref(v_dir_2724_);
v___x_2742_ = l_Lake_joinRelative(v_dir_2724_, v___x_2735_);
v___x_2743_ = lean_string_append(v___x_2741_, v___x_2742_);
v___x_2744_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2745_ = lean_string_append(v___x_2743_, v___x_2744_);
v___x_2746_ = 1;
v___x_2747_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*1, v___x_2746_);
lean_inc_ref(v___y_2730_);
v___x_2748_ = lean_apply_2(v___y_2730_, v___x_2747_, lean_box(0));
v___x_2749_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2742_);
v___x_2750_ = l_Lake_createParentDirs(v___x_2742_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v___x_2751_; 
lean_dec_ref_known(v___x_2750_, 1);
v___x_2751_ = lean_io_rename(v___y_2728_, v___x_2742_);
lean_dec_ref(v___x_2742_);
lean_dec_ref(v___y_2728_);
v___y_2702_ = v_snd_2732_;
v___y_2703_ = v___x_2749_;
v___y_2704_ = v___y_2730_;
v___y_2705_ = v___x_2751_;
goto v___jp_2701_;
}
else
{
lean_dec_ref(v___x_2742_);
lean_dec_ref(v___y_2728_);
v___y_2702_ = v_snd_2732_;
v___y_2703_ = v___x_2749_;
v___y_2704_ = v___y_2730_;
v___y_2705_ = v___x_2750_;
goto v___jp_2701_;
}
}
}
else
{
lean_dec_ref(v___x_2735_);
lean_dec_ref(v___y_2728_);
v___y_2642_ = v_snd_2732_;
goto v___jp_2641_;
}
}
v___jp_2752_:
{
if (lean_obj_tag(v_packagesDir_x3f_2753_) == 1)
{
lean_object* v_val_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_val_2756_ = lean_ctor_get(v_packagesDir_x3f_2753_, 0);
lean_inc_n(v_val_2756_, 2);
lean_dec_ref_known(v_packagesDir_x3f_2753_, 1);
lean_inc_ref(v_dir_2724_);
v___x_2757_ = l_Lake_joinRelative(v_dir_2724_, v_val_2756_);
v___x_2758_ = l_System_FilePath_pathExists(v___x_2757_);
v___x_2759_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2760_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2760_ == 0)
{
v___y_2728_ = v___x_2757_;
v___y_2729_ = v_val_2756_;
v___y_2730_ = v___y_2755_;
v_fst_2731_ = v___x_2758_;
v_snd_2732_ = v___y_2754_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2762_ == 0)
{
if (v___x_2760_ == 0)
{
v___y_2728_ = v___x_2757_;
v___y_2729_ = v_val_2756_;
v___y_2730_ = v___y_2755_;
v_fst_2731_ = v___x_2758_;
v_snd_2732_ = v___y_2754_;
goto v___jp_2727_;
}
else
{
size_t v___x_2763_; size_t v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2759_, v___x_2763_, v___x_2764_, v___x_2761_, v___y_2755_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_dec_ref_known(v___x_2765_, 1);
v___y_2728_ = v___x_2757_;
v___y_2729_ = v_val_2756_;
v___y_2730_ = v___y_2755_;
v_fst_2731_ = v___x_2758_;
v_snd_2732_ = v___y_2754_;
goto v___jp_2727_;
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref(v___x_2757_);
lean_dec(v_val_2756_);
lean_dec(v___y_2754_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
else
{
size_t v___x_2774_; size_t v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2759_, v___x_2774_, v___x_2775_, v___x_2761_, v___y_2755_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_dec_ref_known(v___x_2776_, 1);
v___y_2728_ = v___x_2757_;
v___y_2729_ = v_val_2756_;
v___y_2730_ = v___y_2755_;
v_fst_2731_ = v___x_2758_;
v_snd_2732_ = v___y_2754_;
goto v___jp_2727_;
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v___x_2757_);
lean_dec(v_val_2756_);
lean_dec(v___y_2754_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v_packagesDir_x3f_2753_);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___y_2754_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
v___jp_2788_:
{
lean_object* v_packagesDir_x3f_2792_; 
v_packagesDir_x3f_2792_ = lean_ctor_get(v___y_2789_, 2);
lean_inc(v_packagesDir_x3f_2792_);
lean_dec_ref(v___y_2789_);
v_packagesDir_x3f_2753_ = v_packagesDir_x3f_2792_;
v___y_2754_ = v___y_2790_;
v___y_2755_ = v___y_2791_;
goto v___jp_2752_;
}
v___jp_2793_:
{
if (lean_obj_tag(v___y_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v_snd_2797_; 
v_a_2796_ = lean_ctor_get(v___y_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___y_2795_, 1);
v_snd_2797_ = lean_ctor_get(v_a_2796_, 1);
lean_inc(v_snd_2797_);
lean_dec(v_a_2796_);
v___y_2789_ = v___y_2794_;
v___y_2790_ = v_snd_2797_;
v___y_2791_ = v_a_2636_;
goto v___jp_2788_;
}
else
{
lean_dec_ref(v___y_2794_);
return v___y_2795_;
}
}
v___jp_2800_:
{
if (lean_obj_tag(v_fst_2801_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2835_; 
v_a_2803_ = lean_ctor_get(v_fst_2801_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_fst_2801_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2805_ = v_fst_2801_;
v_isShared_2806_ = v_isSharedCheck_2835_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v_fst_2801_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2835_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
if (lean_obj_tag(v_a_2803_) == 11)
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
lean_dec_ref_known(v_a_2803_, 2);
v___x_2807_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2808_ = lean_string_append(v_rootName_2799_, v___x_2807_);
v___x_2809_ = 1;
v___x_2810_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set_uint8(v___x_2810_, sizeof(void*)*1, v___x_2809_);
lean_inc_ref(v_a_2636_);
v___x_2811_ = lean_apply_2(v_a_2636_, v___x_2810_, lean_box(0));
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v_snd_2802_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2812_);
v___x_2814_ = v___x_2805_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2638_) == 0)
{
lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_dec(v_snd_2802_);
lean_dec_ref(v_rootName_2799_);
v___x_2816_ = lean_io_error_to_string(v_a_2803_);
v___x_2817_ = 3;
v___x_2818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
lean_ctor_set_uint8(v___x_2818_, sizeof(void*)*1, v___x_2817_);
lean_inc_ref(v_a_2636_);
v___x_2819_ = lean_apply_2(v_a_2636_, v___x_2818_, lean_box(0));
v___x_2820_ = lean_box(0);
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 1);
lean_ctor_set(v___x_2805_, 0, v___x_2820_);
v___x_2822_ = v___x_2805_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2824_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_2825_ = lean_string_append(v_rootName_2799_, v___x_2824_);
v___x_2826_ = lean_io_error_to_string(v_a_2803_);
v___x_2827_ = lean_string_append(v___x_2825_, v___x_2826_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = 2;
v___x_2829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*1, v___x_2828_);
lean_inc_ref(v_a_2636_);
v___x_2830_ = lean_apply_2(v_a_2636_, v___x_2829_, lean_box(0));
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v_snd_2802_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2831_);
v___x_2833_ = v___x_2805_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_2799_);
if (lean_obj_tag(v_toUpdate_2638_) == 0)
{
lean_object* v_a_2836_; lean_object* v_packagesDir_x3f_2837_; lean_object* v_packages_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v_a_2836_ = lean_ctor_get(v_fst_2801_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v_fst_2801_, 1);
v_packagesDir_x3f_2837_ = lean_ctor_get(v_a_2836_, 2);
v_packages_2838_ = lean_ctor_get(v_a_2836_, 3);
v___x_2839_ = lean_array_get_size(v_packages_2838_);
v___x_2840_ = lean_nat_dec_lt(v___x_2669_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_inc(v_packagesDir_x3f_2837_);
lean_dec(v_a_2836_);
v_packagesDir_x3f_2753_ = v_packagesDir_x3f_2837_;
v___y_2754_ = v_snd_2802_;
v___y_2755_ = v_a_2636_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2841_; uint8_t v___x_2842_; 
v___x_2841_ = lean_box(0);
v___x_2842_ = lean_nat_dec_le(v___x_2839_, v___x_2839_);
if (v___x_2842_ == 0)
{
if (v___x_2840_ == 0)
{
lean_inc(v_packagesDir_x3f_2837_);
lean_dec(v_a_2836_);
v_packagesDir_x3f_2753_ = v_packagesDir_x3f_2837_;
v___y_2754_ = v_snd_2802_;
v___y_2755_ = v_a_2636_;
goto v___jp_2752_;
}
else
{
size_t v___x_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = lean_usize_of_nat(v___x_2839_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2638_, v_packages_2838_, v___x_2843_, v___x_2844_, v___x_2841_, v_snd_2802_);
v___y_2794_ = v_a_2836_;
v___y_2795_ = v___x_2845_;
goto v___jp_2793_;
}
}
else
{
size_t v___x_2846_; size_t v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = ((size_t)0ULL);
v___x_2847_ = lean_usize_of_nat(v___x_2839_);
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2638_, v_packages_2838_, v___x_2846_, v___x_2847_, v___x_2841_, v_snd_2802_);
v___y_2794_ = v_a_2836_;
v___y_2795_ = v___x_2848_;
goto v___jp_2793_;
}
}
}
else
{
lean_object* v_a_2849_; 
v_a_2849_ = lean_ctor_get(v_fst_2801_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v_fst_2801_, 1);
v___y_2789_ = v_a_2849_;
v___y_2790_ = v_snd_2802_;
v___y_2791_ = v_a_2636_;
goto v___jp_2788_;
}
}
}
v___jp_2852_:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2854_ == 0)
{
v_fst_2801_ = v_val_2853_;
v_snd_2802_ = v_a_2639_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2856_ == 0)
{
if (v___x_2854_ == 0)
{
v_fst_2801_ = v_val_2853_;
v_snd_2802_ = v_a_2639_;
goto v___jp_2800_;
}
else
{
size_t v___x_2857_; size_t v___x_2858_; lean_object* v___x_2859_; 
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2851_, v___x_2857_, v___x_2858_, v___x_2855_, v_a_2636_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_dec_ref_known(v___x_2859_, 1);
v_fst_2801_ = v_val_2853_;
v_snd_2802_ = v_a_2639_;
goto v___jp_2800_;
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_val_2853_);
lean_dec_ref(v_rootName_2799_);
lean_dec(v_a_2639_);
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
else
{
size_t v___x_2868_; size_t v___x_2869_; lean_object* v___x_2870_; 
v___x_2868_ = ((size_t)0ULL);
v___x_2869_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2851_, v___x_2868_, v___x_2869_, v___x_2855_, v_a_2636_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_dec_ref_known(v___x_2870_, 1);
v_fst_2801_ = v_val_2853_;
v_snd_2802_ = v_a_2639_;
goto v___jp_2800_;
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v_val_2853_);
lean_dec_ref(v_rootName_2799_);
lean_dec(v_a_2639_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_2896_, lean_object* v_ws_2897_, lean_object* v_toUpdate_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_2896_, v_ws_2897_, v_toUpdate_2898_, v_a_2899_);
lean_dec(v_toUpdate_2898_);
lean_dec_ref(v_ws_2897_);
lean_dec_ref(v_a_2896_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_a_2902_, lean_object* v_ws_2903_, lean_object* v_rootDeps_2904_){
_start:
{
lean_object* v___y_2907_; lean_object* v_lakeEnv_2912_; lean_object* v_lakeArgs_x3f_2913_; lean_object* v_packages_2914_; uint8_t v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_3063_; lean_object* v___y_3064_; uint8_t v___y_3065_; lean_object* v___x_3068_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; uint8_t v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; uint8_t v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___x_3104_; lean_object* v_baseName_3105_; lean_object* v_dir_3106_; lean_object* v_config_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_lakeEnv_2912_ = lean_ctor_get(v_ws_2903_, 0);
lean_inc_ref(v_lakeEnv_2912_);
v_lakeArgs_x3f_2913_ = lean_ctor_get(v_ws_2903_, 3);
lean_inc(v_lakeArgs_x3f_2913_);
v_packages_2914_ = lean_ctor_get(v_ws_2903_, 4);
lean_inc_ref(v_packages_2914_);
lean_dec_ref(v_ws_2903_);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3104_ = lean_array_fget(v_packages_2914_, v___x_3068_);
lean_dec_ref(v_packages_2914_);
v_baseName_3105_ = lean_ctor_get(v___x_3104_, 1);
lean_inc(v_baseName_3105_);
v_dir_3106_ = lean_ctor_get(v___x_3104_, 4);
lean_inc_ref_n(v_dir_3106_, 2);
v_config_3107_ = lean_ctor_get(v___x_3104_, 6);
lean_inc_ref(v_config_3107_);
lean_dec(v___x_3104_);
v___x_3108_ = l_Lake_toolchainFileName;
v___x_3109_ = l_System_FilePath_join(v_dir_3106_, v___x_3108_);
v___x_3110_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3109_);
lean_dec_ref(v___x_3109_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3169_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3169_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3169_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_src_3116_; lean_object* v_tc_x3f_3117_; lean_object* v_clashes_3118_; uint8_t v_fixed_3119_; lean_object* v___y_3143_; uint8_t v_fixedToolchain_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v_fixedToolchain_3157_ = lean_ctor_get_uint8(v_config_3107_, sizeof(void*)*27 + 6);
lean_dec_ref(v_config_3107_);
v___x_3158_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3159_ = lean_array_get_size(v_rootDeps_2904_);
v___x_3160_ = lean_nat_dec_lt(v___x_3068_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_inc(v_a_3111_);
v_src_3116_ = v_baseName_3105_;
v_tc_x3f_3117_ = v_a_3111_;
v_clashes_3118_ = v___x_3158_;
v_fixed_3119_ = v_fixedToolchain_3157_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
lean_inc(v_a_3111_);
lean_inc(v_baseName_3105_);
v___x_3161_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3161_, 0, v_baseName_3105_);
lean_ctor_set(v___x_3161_, 1, v_a_3111_);
lean_ctor_set(v___x_3161_, 2, v___x_3158_);
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*3, v_fixedToolchain_3157_);
v___x_3162_ = lean_nat_dec_le(v___x_3159_, v___x_3159_);
if (v___x_3162_ == 0)
{
if (v___x_3160_ == 0)
{
lean_dec_ref_known(v___x_3161_, 3);
lean_inc(v_a_3111_);
v_src_3116_ = v_baseName_3105_;
v_tc_x3f_3117_ = v_a_3111_;
v_clashes_3118_ = v___x_3158_;
v_fixed_3119_ = v_fixedToolchain_3157_;
goto v___jp_3115_;
}
else
{
size_t v___x_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v_baseName_3105_);
v___x_3163_ = ((size_t)0ULL);
v___x_3164_ = lean_usize_of_nat(v___x_3159_);
lean_inc_ref(v_dir_3106_);
v___x_3165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3106_, v_rootDeps_2904_, v___x_3163_, v___x_3164_, v___x_3161_, v_a_2902_);
v___y_3143_ = v___x_3165_;
goto v___jp_3142_;
}
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
lean_dec(v_baseName_3105_);
v___x_3166_ = ((size_t)0ULL);
v___x_3167_ = lean_usize_of_nat(v___x_3159_);
lean_inc_ref(v_dir_3106_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3106_, v_rootDeps_2904_, v___x_3166_, v___x_3167_, v___x_3161_, v_a_2902_);
v___y_3143_ = v___x_3168_;
goto v___jp_3142_;
}
}
v___jp_3115_:
{
lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3120_ = lean_array_get_size(v_clashes_3118_);
v___x_3121_ = lean_nat_dec_lt(v___x_3068_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_dec_ref(v_clashes_3118_);
lean_dec(v_src_3116_);
if (lean_obj_tag(v_tc_x3f_3117_) == 1)
{
lean_object* v_val_3122_; lean_object* v_rootToolchainFile_3123_; 
v_val_3122_ = lean_ctor_get(v_tc_x3f_3117_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v_tc_x3f_3117_, 1);
v_rootToolchainFile_3123_ = l_Lake_joinRelative(v_dir_3106_, v___x_3108_);
if (lean_obj_tag(v_a_3111_) == 0)
{
lean_del_object(v___x_3113_);
v___y_3063_ = v_rootToolchainFile_3123_;
v___y_3064_ = v_val_3122_;
v___y_3065_ = v___x_3121_;
goto v___jp_3062_;
}
else
{
lean_object* v_val_3124_; uint8_t v___x_3125_; 
v_val_3124_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_val_3124_);
lean_dec_ref_known(v_a_3111_, 1);
lean_inc(v_val_3122_);
v___x_3125_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3124_, v_val_3122_);
if (v___x_3125_ == 0)
{
lean_del_object(v___x_3113_);
v___y_3063_ = v_rootToolchainFile_3123_;
v___y_3064_ = v_val_3122_;
v___y_3065_ = v___x_3125_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3130_; 
lean_dec_ref(v_rootToolchainFile_3123_);
lean_dec(v_val_3122_);
lean_dec(v_lakeArgs_x3f_2913_);
lean_dec_ref(v_lakeEnv_2912_);
v___x_3126_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2902_);
v___x_3127_ = lean_apply_2(v_a_2902_, v___x_3126_, lean_box(0));
v___x_3128_ = lean_box(0);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3128_);
v___x_3130_ = v___x_3113_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
lean_dec(v_tc_x3f_3117_);
lean_dec(v_a_3111_);
lean_dec_ref(v_dir_3106_);
lean_dec(v_lakeArgs_x3f_2913_);
lean_dec_ref(v_lakeEnv_2912_);
v___x_3132_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2902_);
v___x_3133_ = lean_apply_2(v_a_2902_, v___x_3132_, lean_box(0));
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3133_);
v___x_3135_ = v___x_3113_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
lean_del_object(v___x_3113_);
lean_dec(v_a_3111_);
lean_dec_ref(v_dir_3106_);
lean_dec(v_lakeArgs_x3f_2913_);
lean_dec_ref(v_lakeEnv_2912_);
if (lean_obj_tag(v_tc_x3f_3117_) == 1)
{
if (v_fixed_3119_ == 0)
{
lean_object* v_val_3137_; lean_object* v___x_3138_; 
v_val_3137_ = lean_ctor_get(v_tc_x3f_3117_, 0);
lean_inc(v_val_3137_);
lean_dec_ref_known(v_tc_x3f_3117_, 1);
v___x_3138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3096_ = v_val_3137_;
v___y_3097_ = v_src_3116_;
v___y_3098_ = v_clashes_3118_;
v___y_3099_ = v___x_3121_;
v___y_3100_ = v___x_3120_;
v___y_3101_ = v___x_3138_;
goto v___jp_3095_;
}
else
{
lean_object* v_val_3139_; lean_object* v___x_3140_; 
v_val_3139_ = lean_ctor_get(v_tc_x3f_3117_, 0);
lean_inc(v_val_3139_);
lean_dec_ref_known(v_tc_x3f_3117_, 1);
v___x_3140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3096_ = v_val_3139_;
v___y_3097_ = v_src_3116_;
v___y_3098_ = v_clashes_3118_;
v___y_3099_ = v___x_3121_;
v___y_3100_ = v___x_3120_;
v___y_3101_ = v___x_3140_;
goto v___jp_3095_;
}
}
else
{
lean_object* v___x_3141_; 
lean_dec(v_tc_x3f_3117_);
lean_dec(v_src_3116_);
v___x_3141_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3070_ = v_clashes_3118_;
v___y_3071_ = v___x_3120_;
v___y_3072_ = v___x_3141_;
goto v___jp_3069_;
}
}
}
v___jp_3142_:
{
if (lean_obj_tag(v___y_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v_src_3145_; lean_object* v_tc_x3f_3146_; lean_object* v_clashes_3147_; uint8_t v_fixed_3148_; 
v_a_3144_ = lean_ctor_get(v___y_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v___y_3143_, 1);
v_src_3145_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_src_3145_);
v_tc_x3f_3146_ = lean_ctor_get(v_a_3144_, 1);
lean_inc(v_tc_x3f_3146_);
v_clashes_3147_ = lean_ctor_get(v_a_3144_, 2);
lean_inc_ref(v_clashes_3147_);
v_fixed_3148_ = lean_ctor_get_uint8(v_a_3144_, sizeof(void*)*3);
lean_dec(v_a_3144_);
v_src_3116_ = v_src_3145_;
v_tc_x3f_3117_ = v_tc_x3f_3146_;
v_clashes_3118_ = v_clashes_3147_;
v_fixed_3119_ = v_fixed_3148_;
goto v___jp_3115_;
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_del_object(v___x_3113_);
lean_dec(v_a_3111_);
lean_dec_ref(v_dir_3106_);
lean_dec(v_lakeArgs_x3f_2913_);
lean_dec_ref(v_lakeEnv_2912_);
v_a_3149_ = lean_ctor_get(v___y_3143_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___y_3143_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___y_3143_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___y_3143_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v_config_3107_);
lean_dec_ref(v_dir_3106_);
lean_dec(v_baseName_3105_);
lean_dec(v_lakeArgs_x3f_2913_);
lean_dec_ref(v_lakeEnv_2912_);
v_a_3170_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3172_ = v___x_3110_;
v_isShared_3173_ = v_isSharedCheck_3182_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3110_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3182_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3174_ = lean_io_error_to_string(v_a_3170_);
v___x_3175_ = 3;
v___x_3176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3176_, 0, v___x_3174_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*1, v___x_3175_);
lean_inc_ref(v_a_2902_);
v___x_3177_ = lean_apply_2(v_a_2902_, v___x_3176_, lean_box(0));
v___x_3178_ = lean_box(0);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3178_);
v___x_3180_ = v___x_3172_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
v___jp_2906_:
{
uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2908_ = 2;
v___x_2909_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2909_, 0, v___y_2907_);
lean_ctor_set_uint8(v___x_2909_, sizeof(void*)*1, v___x_2908_);
lean_inc_ref(v_a_2902_);
v___x_2910_ = lean_apply_2(v_a_2902_, v___x_2909_, lean_box(0));
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
v___jp_2915_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_inc_ref(v___y_2918_);
v___x_2920_ = lean_string_append(v___y_2918_, v___y_2919_);
v___x_2921_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2922_ = lean_string_append(v___x_2920_, v___x_2921_);
v___x_2923_ = 1;
v___x_2924_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*1, v___x_2923_);
lean_inc_ref(v_a_2902_);
v___x_2925_ = lean_apply_2(v_a_2902_, v___x_2924_, lean_box(0));
v___x_2926_ = l_IO_FS_writeFile(v___y_2917_, v___y_2919_);
lean_dec_ref(v___y_2917_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_dec_ref_known(v___x_2926_, 1);
if (lean_obj_tag(v_lakeArgs_x3f_2913_) == 1)
{
lean_object* v_elan_x3f_2927_; 
v_elan_x3f_2927_ = lean_ctor_get(v_lakeEnv_2912_, 2);
if (lean_obj_tag(v_elan_x3f_2927_) == 1)
{
lean_object* v_val_2928_; lean_object* v_val_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v_elan_2933_; uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_val_2928_ = lean_ctor_get(v_lakeArgs_x3f_2913_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v_lakeArgs_x3f_2913_, 1);
v_val_2929_ = lean_ctor_get(v_elan_x3f_2927_, 0);
v___x_2930_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2902_);
v___x_2931_ = lean_apply_2(v_a_2902_, v___x_2930_, lean_box(0));
v___x_2932_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2933_ = lean_ctor_get(v_val_2929_, 1);
lean_inc_ref(v_elan_2933_);
v___x_2934_ = 1;
v___x_2935_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2936_ = lean_unsigned_to_nat(4u);
v___x_2937_ = lean_mk_empty_array_with_capacity(v___x_2936_);
lean_dec_ref(v___x_2937_);
v___x_2938_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2939_ = lean_array_push(v___x_2938_, v___y_2919_);
v___x_2940_ = lean_array_push(v___x_2939_, v___x_2935_);
v___x_2941_ = l_Array_append___redArg(v___x_2940_, v_val_2928_);
lean_dec(v_val_2928_);
v___x_2942_ = lean_box(0);
v___x_2943_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2912_);
v___x_2944_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2944_, 0, v___x_2932_);
lean_ctor_set(v___x_2944_, 1, v_elan_2933_);
lean_ctor_set(v___x_2944_, 2, v___x_2941_);
lean_ctor_set(v___x_2944_, 3, v___x_2942_);
lean_ctor_set(v___x_2944_, 4, v___x_2943_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*5, v___x_2934_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*5 + 1, v___y_2916_);
v___x_2945_ = lean_io_process_spawn(v___x_2944_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = lean_io_process_child_wait(v___x_2932_, v_a_2946_);
lean_dec(v_a_2946_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; uint32_t v___x_2949_; uint8_t v___x_2950_; lean_object* v___x_2951_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2949_ = lean_unbox_uint32(v_a_2948_);
lean_dec(v_a_2948_);
v___x_2950_ = lean_uint32_to_uint8(v___x_2949_);
v___x_2951_ = lean_io_exit(v___x_2950_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
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
return v___x_2957_;
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2972_; 
v_a_2960_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2962_ = v___x_2951_;
v_isShared_2963_ = v_isSharedCheck_2972_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2951_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2972_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2964_ = lean_io_error_to_string(v_a_2960_);
v___x_2965_ = 3;
v___x_2966_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set_uint8(v___x_2966_, sizeof(void*)*1, v___x_2965_);
lean_inc_ref(v_a_2902_);
v___x_2967_ = lean_apply_2(v_a_2902_, v___x_2966_, lean_box(0));
v___x_2968_ = lean_box(0);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2968_);
v___x_2970_ = v___x_2962_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2985_; 
v_a_2973_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2975_ = v___x_2947_;
v_isShared_2976_ = v_isSharedCheck_2985_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2947_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2985_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2977_ = lean_io_error_to_string(v_a_2973_);
v___x_2978_ = 3;
v___x_2979_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2979_, 0, v___x_2977_);
lean_ctor_set_uint8(v___x_2979_, sizeof(void*)*1, v___x_2978_);
lean_inc_ref(v_a_2902_);
v___x_2980_ = lean_apply_2(v_a_2902_, v___x_2979_, lean_box(0));
v___x_2981_ = lean_box(0);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2981_);
v___x_2983_ = v___x_2975_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2998_; 
v_a_2986_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2988_ = v___x_2945_;
v_isShared_2989_ = v_isSharedCheck_2998_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2945_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2998_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2990_ = lean_io_error_to_string(v_a_2986_);
v___x_2991_ = 3;
v___x_2992_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set_uint8(v___x_2992_, sizeof(void*)*1, v___x_2991_);
lean_inc_ref(v_a_2902_);
v___x_2993_ = lean_apply_2(v_a_2902_, v___x_2992_, lean_box(0));
v___x_2994_ = lean_box(0);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2994_);
v___x_2996_ = v___x_2988_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; 
lean_dec_ref_known(v_lakeArgs_x3f_2913_, 1);
lean_dec_ref(v___y_2919_);
lean_dec_ref(v_lakeEnv_2912_);
v___x_2999_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2902_);
v___x_3000_ = lean_apply_2(v_a_2902_, v___x_2999_, lean_box(0));
v___x_3001_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3002_ = lean_io_exit(v___x_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3023_; 
v_a_3011_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3013_ = v___x_3002_;
v_isShared_3014_ = v_isSharedCheck_3023_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3002_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3023_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3015_ = lean_io_error_to_string(v_a_3011_);
v___x_3016_ = 3;
v___x_3017_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*1, v___x_3016_);
lean_inc_ref(v_a_2902_);
v___x_3018_ = lean_apply_2(v_a_2902_, v___x_3017_, lean_box(0));
v___x_3019_ = lean_box(0);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3019_);
v___x_3021_ = v___x_3013_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; 
lean_dec_ref(v___y_2919_);
lean_dec(v_lakeArgs_x3f_2913_);
lean_dec_ref(v_lakeEnv_2912_);
v___x_3024_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2902_);
v___x_3025_ = lean_apply_2(v_a_2902_, v___x_3024_, lean_box(0));
v___x_3026_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3027_ = lean_io_exit(v___x_3026_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3048_; 
v_a_3036_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3038_ = v___x_3027_;
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3027_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; uint8_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3040_ = lean_io_error_to_string(v_a_3036_);
v___x_3041_ = 3;
v___x_3042_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*1, v___x_3041_);
lean_inc_ref(v_a_2902_);
v___x_3043_ = lean_apply_2(v_a_2902_, v___x_3042_, lean_box(0));
v___x_3044_ = lean_box(0);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3044_);
v___x_3046_ = v___x_3038_;
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
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___y_2919_);
lean_dec(v_lakeArgs_x3f_2913_);
lean_dec_ref(v_lakeEnv_2912_);
v_a_3049_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3051_ = v___x_2926_;
v_isShared_3052_ = v_isSharedCheck_3061_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_2926_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3061_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3053_ = lean_io_error_to_string(v_a_3049_);
v___x_3054_ = 3;
v___x_3055_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*1, v___x_3054_);
lean_inc_ref(v_a_2902_);
v___x_3056_ = lean_apply_2(v_a_2902_, v___x_3055_, lean_box(0));
v___x_3057_ = lean_box(0);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3057_);
v___x_3059_ = v___x_3051_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_3062_:
{
lean_object* v___x_3066_; lean_object* v_toString_3067_; 
v___x_3066_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3067_ = lean_ctor_get(v___y_3064_, 0);
lean_inc_ref(v_toString_3067_);
lean_dec_ref(v___y_3064_);
v___y_2916_ = v___y_3065_;
v___y_2917_ = v___y_3063_;
v___y_2918_ = v___x_3066_;
v___y_2919_ = v_toString_3067_;
goto v___jp_2915_;
}
v___jp_3069_:
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_nat_dec_lt(v___x_3068_, v___y_3071_);
if (v___x_3073_ == 0)
{
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
v___y_2907_ = v___y_3072_;
goto v___jp_2906_;
}
else
{
uint8_t v___x_3074_; 
v___x_3074_ = lean_nat_dec_le(v___y_3071_, v___y_3071_);
if (v___x_3074_ == 0)
{
if (v___x_3073_ == 0)
{
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
v___y_2907_ = v___y_3072_;
goto v___jp_2906_;
}
else
{
size_t v___x_3075_; size_t v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((size_t)0ULL);
v___x_3076_ = lean_usize_of_nat(v___y_3071_);
lean_dec(v___y_3071_);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3070_, v___x_3075_, v___x_3076_, v___y_3072_);
lean_dec_ref(v___y_3070_);
v___y_2907_ = v___x_3077_;
goto v___jp_2906_;
}
}
else
{
size_t v___x_3078_; size_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((size_t)0ULL);
v___x_3079_ = lean_usize_of_nat(v___y_3071_);
lean_dec(v___y_3071_);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3070_, v___x_3078_, v___x_3079_, v___y_3072_);
lean_dec_ref(v___y_3070_);
v___y_2907_ = v___x_3080_;
goto v___jp_2906_;
}
}
}
v___jp_3081_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_inc_ref(v___y_3083_);
v___x_3089_ = lean_string_append(v___y_3083_, v___y_3088_);
lean_dec_ref(v___y_3088_);
v___x_3090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3091_ = lean_string_append(v___x_3089_, v___x_3090_);
v___x_3092_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3084_, v___y_3086_);
v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
lean_dec_ref(v___x_3092_);
v___x_3094_ = lean_string_append(v___x_3093_, v___y_3082_);
v___y_3070_ = v___y_3085_;
v___y_3071_ = v___y_3087_;
v___y_3072_ = v___x_3094_;
goto v___jp_3069_;
}
v___jp_3095_:
{
lean_object* v___x_3102_; lean_object* v_toString_3103_; 
v___x_3102_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3103_ = lean_ctor_get(v___y_3096_, 0);
lean_inc_ref(v_toString_3103_);
lean_dec_ref(v___y_3096_);
v___y_3082_ = v___y_3101_;
v___y_3083_ = v___x_3102_;
v___y_3084_ = v___y_3097_;
v___y_3085_ = v___y_3098_;
v___y_3086_ = v___y_3099_;
v___y_3087_ = v___y_3100_;
v___y_3088_ = v_toString_3103_;
goto v___jp_3081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v_a_3183_, lean_object* v_ws_3184_, lean_object* v_rootDeps_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_3183_, v_ws_3184_, v_rootDeps_3185_);
lean_dec_ref(v_rootDeps_3185_);
lean_dec_ref(v_a_3183_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(lean_object* v_msg_3188_){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_box(1);
v___x_3190_ = lean_panic_fn_borrowed(v___x_3189_, v_msg_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3194_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2));
v___x_3195_ = lean_unsigned_to_nat(35u);
v___x_3196_ = lean_unsigned_to_nat(182u);
v___x_3197_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1));
v___x_3198_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3199_ = l_mkPanicMessageWithDecl(v___x_3198_, v___x_3197_, v___x_3196_, v___x_3195_, v___x_3194_);
return v___x_3199_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3200_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__2));
v___x_3201_ = lean_unsigned_to_nat(21u);
v___x_3202_ = lean_unsigned_to_nat(183u);
v___x_3203_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__1));
v___x_3204_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3205_ = l_mkPanicMessageWithDecl(v___x_3204_, v___x_3203_, v___x_3202_, v___x_3201_, v___x_3200_);
return v___x_3205_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3208_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6));
v___x_3209_ = lean_unsigned_to_nat(35u);
v___x_3210_ = lean_unsigned_to_nat(276u);
v___x_3211_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5));
v___x_3212_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3213_ = l_mkPanicMessageWithDecl(v___x_3212_, v___x_3211_, v___x_3210_, v___x_3209_, v___x_3208_);
return v___x_3213_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3214_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__6));
v___x_3215_ = lean_unsigned_to_nat(21u);
v___x_3216_ = lean_unsigned_to_nat(277u);
v___x_3217_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__5));
v___x_3218_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__0));
v___x_3219_ = l_mkPanicMessageWithDecl(v___x_3218_, v___x_3217_, v___x_3216_, v___x_3215_, v___x_3214_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(lean_object* v_k_3220_, lean_object* v_v_3221_, lean_object* v_t_3222_){
_start:
{
if (lean_obj_tag(v_t_3222_) == 0)
{
lean_object* v_size_3223_; lean_object* v_k_3224_; lean_object* v_v_3225_; lean_object* v_l_3226_; lean_object* v_r_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3583_; 
v_size_3223_ = lean_ctor_get(v_t_3222_, 0);
v_k_3224_ = lean_ctor_get(v_t_3222_, 1);
v_v_3225_ = lean_ctor_get(v_t_3222_, 2);
v_l_3226_ = lean_ctor_get(v_t_3222_, 3);
v_r_3227_ = lean_ctor_get(v_t_3222_, 4);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_t_3222_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3229_ = v_t_3222_;
v_isShared_3230_ = v_isSharedCheck_3583_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_r_3227_);
lean_inc(v_l_3226_);
lean_inc(v_v_3225_);
lean_inc(v_k_3224_);
lean_inc(v_size_3223_);
lean_dec(v_t_3222_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3583_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
uint8_t v___x_3231_; 
v___x_3231_ = lean_string_compare(v_k_3220_, v_k_3224_);
switch(v___x_3231_)
{
case 0:
{
lean_object* v___x_3232_; 
lean_dec(v_size_3223_);
v___x_3232_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v_k_3220_, v_v_3221_, v_l_3226_);
if (lean_obj_tag(v_r_3227_) == 0)
{
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_size_3233_; lean_object* v_size_3234_; lean_object* v_k_3235_; lean_object* v_v_3236_; lean_object* v_l_3237_; lean_object* v_r_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; uint8_t v___x_3241_; 
v_size_3233_ = lean_ctor_get(v_r_3227_, 0);
v_size_3234_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_size_3234_);
v_k_3235_ = lean_ctor_get(v___x_3232_, 1);
lean_inc(v_k_3235_);
v_v_3236_ = lean_ctor_get(v___x_3232_, 2);
lean_inc(v_v_3236_);
v_l_3237_ = lean_ctor_get(v___x_3232_, 3);
lean_inc(v_l_3237_);
v_r_3238_ = lean_ctor_get(v___x_3232_, 4);
lean_inc(v_r_3238_);
v___x_3239_ = lean_unsigned_to_nat(3u);
v___x_3240_ = lean_nat_mul(v___x_3239_, v_size_3233_);
v___x_3241_ = lean_nat_dec_lt(v___x_3240_, v_size_3234_);
lean_dec(v___x_3240_);
if (v___x_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_dec(v_r_3238_);
lean_dec(v_l_3237_);
lean_dec(v_v_3236_);
lean_dec(v_k_3235_);
v___x_3242_ = lean_unsigned_to_nat(1u);
v___x_3243_ = lean_nat_add(v___x_3242_, v_size_3234_);
lean_dec(v_size_3234_);
v___x_3244_ = lean_nat_add(v___x_3243_, v_size_3233_);
lean_dec(v___x_3243_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 3, v___x_3232_);
lean_ctor_set(v___x_3229_, 0, v___x_3244_);
v___x_3246_ = v___x_3229_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_r_3227_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
else
{
lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3319_; 
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; lean_object* v_unused_3321_; lean_object* v_unused_3322_; lean_object* v_unused_3323_; lean_object* v_unused_3324_; 
v_unused_3320_ = lean_ctor_get(v___x_3232_, 4);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v___x_3232_, 3);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v___x_3232_, 2);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v___x_3232_, 1);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3324_);
v___x_3249_ = v___x_3232_;
v_isShared_3250_ = v_isSharedCheck_3319_;
goto v_resetjp_3248_;
}
else
{
lean_dec(v___x_3232_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3319_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
if (lean_obj_tag(v_l_3237_) == 0)
{
if (lean_obj_tag(v_r_3238_) == 0)
{
lean_object* v_size_3251_; lean_object* v_size_3252_; lean_object* v_k_3253_; lean_object* v_v_3254_; lean_object* v_l_3255_; lean_object* v_r_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_size_3251_ = lean_ctor_get(v_l_3237_, 0);
v_size_3252_ = lean_ctor_get(v_r_3238_, 0);
v_k_3253_ = lean_ctor_get(v_r_3238_, 1);
v_v_3254_ = lean_ctor_get(v_r_3238_, 2);
v_l_3255_ = lean_ctor_get(v_r_3238_, 3);
v_r_3256_ = lean_ctor_get(v_r_3238_, 4);
v___x_3257_ = lean_unsigned_to_nat(2u);
v___x_3258_ = lean_nat_mul(v___x_3257_, v_size_3251_);
v___x_3259_ = lean_nat_dec_lt(v_size_3252_, v___x_3258_);
lean_dec(v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3289_; 
lean_inc(v_r_3256_);
lean_inc(v_l_3255_);
lean_inc(v_v_3254_);
lean_inc(v_k_3253_);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_r_3238_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; lean_object* v_unused_3291_; lean_object* v_unused_3292_; lean_object* v_unused_3293_; lean_object* v_unused_3294_; 
v_unused_3290_ = lean_ctor_get(v_r_3238_, 4);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_r_3238_, 3);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v_r_3238_, 2);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_r_3238_, 1);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v_r_3238_, 0);
lean_dec(v_unused_3294_);
v___x_3261_ = v_r_3238_;
v_isShared_3262_ = v_isSharedCheck_3289_;
goto v_resetjp_3260_;
}
else
{
lean_dec(v_r_3238_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3289_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___x_3277_; lean_object* v___y_3279_; 
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3264_ = lean_nat_add(v___x_3263_, v_size_3234_);
lean_dec(v_size_3234_);
v___x_3265_ = lean_nat_add(v___x_3264_, v_size_3233_);
lean_dec(v___x_3264_);
v___x_3277_ = lean_nat_add(v___x_3263_, v_size_3251_);
if (lean_obj_tag(v_l_3255_) == 0)
{
lean_object* v_size_3287_; 
v_size_3287_ = lean_ctor_get(v_l_3255_, 0);
lean_inc(v_size_3287_);
v___y_3279_ = v_size_3287_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_unsigned_to_nat(0u);
v___y_3279_ = v___x_3288_;
goto v___jp_3278_;
}
v___jp_3266_:
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3270_ = lean_nat_add(v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec(v___y_3268_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 4, v_r_3227_);
lean_ctor_set(v___x_3261_, 3, v_r_3256_);
lean_ctor_set(v___x_3261_, 2, v_v_3225_);
lean_ctor_set(v___x_3261_, 1, v_k_3224_);
lean_ctor_set(v___x_3261_, 0, v___x_3270_);
v___x_3272_ = v___x_3261_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_r_3256_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v_r_3227_);
v___x_3272_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3274_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 4, v___x_3272_);
lean_ctor_set(v___x_3249_, 3, v___y_3267_);
lean_ctor_set(v___x_3249_, 2, v_v_3254_);
lean_ctor_set(v___x_3249_, 1, v_k_3253_);
lean_ctor_set(v___x_3249_, 0, v___x_3265_);
v___x_3274_ = v___x_3249_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_k_3253_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_v_3254_);
lean_ctor_set(v_reuseFailAlloc_3275_, 3, v___y_3267_);
lean_ctor_set(v_reuseFailAlloc_3275_, 4, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
v___jp_3278_:
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3280_ = lean_nat_add(v___x_3277_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec(v___x_3277_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v_l_3255_);
lean_ctor_set(v___x_3229_, 3, v_l_3237_);
lean_ctor_set(v___x_3229_, 2, v_v_3236_);
lean_ctor_set(v___x_3229_, 1, v_k_3235_);
lean_ctor_set(v___x_3229_, 0, v___x_3280_);
v___x_3282_ = v___x_3229_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v_l_3255_);
v___x_3282_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_nat_add(v___x_3263_, v_size_3233_);
if (lean_obj_tag(v_r_3256_) == 0)
{
lean_object* v_size_3284_; 
v_size_3284_ = lean_ctor_get(v_r_3256_, 0);
lean_inc(v_size_3284_);
v___y_3267_ = v___x_3282_;
v___y_3268_ = v___x_3283_;
v___y_3269_ = v_size_3284_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_unsigned_to_nat(0u);
v___y_3267_ = v___x_3282_;
v___y_3268_ = v___x_3283_;
v___y_3269_ = v___x_3285_;
goto v___jp_3266_;
}
}
}
}
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
lean_del_object(v___x_3229_);
v___x_3295_ = lean_unsigned_to_nat(1u);
v___x_3296_ = lean_nat_add(v___x_3295_, v_size_3234_);
lean_dec(v_size_3234_);
v___x_3297_ = lean_nat_add(v___x_3296_, v_size_3233_);
lean_dec(v___x_3296_);
v___x_3298_ = lean_nat_add(v___x_3295_, v_size_3233_);
v___x_3299_ = lean_nat_add(v___x_3298_, v_size_3252_);
lean_dec(v___x_3298_);
lean_inc_ref(v_r_3227_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 4, v_r_3227_);
lean_ctor_set(v___x_3249_, 3, v_r_3238_);
lean_ctor_set(v___x_3249_, 2, v_v_3225_);
lean_ctor_set(v___x_3249_, 1, v_k_3224_);
lean_ctor_set(v___x_3249_, 0, v___x_3299_);
v___x_3301_ = v___x_3249_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_r_3238_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_r_3227_);
v___x_3301_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
v_isSharedCheck_3308_ = !lean_is_exclusive(v_r_3227_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; lean_object* v_unused_3313_; 
v_unused_3309_ = lean_ctor_get(v_r_3227_, 4);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_r_3227_, 3);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_r_3227_, 2);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_r_3227_, 1);
lean_dec(v_unused_3312_);
v_unused_3313_ = lean_ctor_get(v_r_3227_, 0);
lean_dec(v_unused_3313_);
v___x_3303_ = v_r_3227_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_dec(v_r_3227_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
lean_ctor_set(v___x_3303_, 4, v___x_3301_);
lean_ctor_set(v___x_3303_, 3, v_l_3237_);
lean_ctor_set(v___x_3303_, 2, v_v_3236_);
lean_ctor_set(v___x_3303_, 1, v_k_3235_);
lean_ctor_set(v___x_3303_, 0, v___x_3297_);
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3307_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3307_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3307_, 4, v___x_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref_known(v_l_3237_, 5);
lean_del_object(v___x_3249_);
lean_dec(v_v_3236_);
lean_dec(v_k_3235_);
lean_dec(v_size_3234_);
lean_dec_ref_known(v_r_3227_, 5);
lean_del_object(v___x_3229_);
lean_dec(v_v_3225_);
lean_dec(v_k_3224_);
v___x_3315_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__3);
v___x_3316_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3315_);
return v___x_3316_;
}
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
lean_del_object(v___x_3249_);
lean_dec(v_r_3238_);
lean_dec(v_v_3236_);
lean_dec(v_k_3235_);
lean_dec(v_size_3234_);
lean_dec_ref_known(v_r_3227_, 5);
lean_del_object(v___x_3229_);
lean_dec(v_v_3225_);
lean_dec(v_k_3224_);
v___x_3317_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__4);
v___x_3318_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3317_);
return v___x_3318_;
}
}
}
}
else
{
lean_object* v_size_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v_size_3325_ = lean_ctor_get(v_r_3227_, 0);
v___x_3326_ = lean_unsigned_to_nat(1u);
v___x_3327_ = lean_nat_add(v___x_3326_, v_size_3325_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 3, v___x_3232_);
lean_ctor_set(v___x_3229_, 0, v___x_3327_);
v___x_3329_ = v___x_3229_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v_r_3227_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
else
{
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_l_3331_; 
v_l_3331_ = lean_ctor_get(v___x_3232_, 3);
lean_inc(v_l_3331_);
if (lean_obj_tag(v_l_3331_) == 0)
{
lean_object* v_r_3332_; 
v_r_3332_ = lean_ctor_get(v___x_3232_, 4);
lean_inc(v_r_3332_);
if (lean_obj_tag(v_r_3332_) == 0)
{
lean_object* v_size_3333_; lean_object* v_k_3334_; lean_object* v_v_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3349_; 
v_size_3333_ = lean_ctor_get(v___x_3232_, 0);
v_k_3334_ = lean_ctor_get(v___x_3232_, 1);
v_v_3335_ = lean_ctor_get(v___x_3232_, 2);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3349_ == 0)
{
lean_object* v_unused_3350_; lean_object* v_unused_3351_; 
v_unused_3350_ = lean_ctor_get(v___x_3232_, 4);
lean_dec(v_unused_3350_);
v_unused_3351_ = lean_ctor_get(v___x_3232_, 3);
lean_dec(v_unused_3351_);
v___x_3337_ = v___x_3232_;
v_isShared_3338_ = v_isSharedCheck_3349_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_v_3335_);
lean_inc(v_k_3334_);
lean_inc(v_size_3333_);
lean_dec(v___x_3232_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3349_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_size_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v_size_3339_ = lean_ctor_get(v_r_3332_, 0);
v___x_3340_ = lean_unsigned_to_nat(1u);
v___x_3341_ = lean_nat_add(v___x_3340_, v_size_3333_);
lean_dec(v_size_3333_);
v___x_3342_ = lean_nat_add(v___x_3340_, v_size_3339_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 4, v_r_3227_);
lean_ctor_set(v___x_3337_, 3, v_r_3332_);
lean_ctor_set(v___x_3337_, 2, v_v_3225_);
lean_ctor_set(v___x_3337_, 1, v_k_3224_);
lean_ctor_set(v___x_3337_, 0, v___x_3342_);
v___x_3344_ = v___x_3337_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_r_3332_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v_r_3227_);
v___x_3344_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3346_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3344_);
lean_ctor_set(v___x_3229_, 3, v_l_3331_);
lean_ctor_set(v___x_3229_, 2, v_v_3335_);
lean_ctor_set(v___x_3229_, 1, v_k_3334_);
lean_ctor_set(v___x_3229_, 0, v___x_3341_);
v___x_3346_ = v___x_3229_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_k_3334_);
lean_ctor_set(v_reuseFailAlloc_3347_, 2, v_v_3335_);
lean_ctor_set(v_reuseFailAlloc_3347_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3347_, 4, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_k_3352_; lean_object* v_v_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3365_; 
v_k_3352_ = lean_ctor_get(v___x_3232_, 1);
v_v_3353_ = lean_ctor_get(v___x_3232_, 2);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; lean_object* v_unused_3367_; lean_object* v_unused_3368_; 
v_unused_3366_ = lean_ctor_get(v___x_3232_, 4);
lean_dec(v_unused_3366_);
v_unused_3367_ = lean_ctor_get(v___x_3232_, 3);
lean_dec(v_unused_3367_);
v_unused_3368_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3368_);
v___x_3355_ = v___x_3232_;
v_isShared_3356_ = v_isSharedCheck_3365_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_v_3353_);
lean_inc(v_k_3352_);
lean_dec(v___x_3232_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3365_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3357_ = lean_unsigned_to_nat(3u);
v___x_3358_ = lean_unsigned_to_nat(1u);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 3, v_r_3332_);
lean_ctor_set(v___x_3355_, 2, v_v_3225_);
lean_ctor_set(v___x_3355_, 1, v_k_3224_);
lean_ctor_set(v___x_3355_, 0, v___x_3358_);
v___x_3360_ = v___x_3355_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_r_3332_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_r_3332_);
v___x_3360_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3362_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3360_);
lean_ctor_set(v___x_3229_, 3, v_l_3331_);
lean_ctor_set(v___x_3229_, 2, v_v_3353_);
lean_ctor_set(v___x_3229_, 1, v_k_3352_);
lean_ctor_set(v___x_3229_, 0, v___x_3357_);
v___x_3362_ = v___x_3229_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3352_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3353_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
else
{
lean_object* v_r_3369_; 
v_r_3369_ = lean_ctor_get(v___x_3232_, 4);
lean_inc(v_r_3369_);
if (lean_obj_tag(v_r_3369_) == 0)
{
lean_object* v_k_3370_; lean_object* v_v_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3395_; 
v_k_3370_ = lean_ctor_get(v___x_3232_, 1);
v_v_3371_ = lean_ctor_get(v___x_3232_, 2);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3395_ == 0)
{
lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; 
v_unused_3396_ = lean_ctor_get(v___x_3232_, 4);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v___x_3232_, 3);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3398_);
v___x_3373_ = v___x_3232_;
v_isShared_3374_ = v_isSharedCheck_3395_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_v_3371_);
lean_inc(v_k_3370_);
lean_dec(v___x_3232_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3395_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_k_3375_; lean_object* v_v_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3391_; 
v_k_3375_ = lean_ctor_get(v_r_3369_, 1);
v_v_3376_ = lean_ctor_get(v_r_3369_, 2);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_r_3369_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; lean_object* v_unused_3393_; lean_object* v_unused_3394_; 
v_unused_3392_ = lean_ctor_get(v_r_3369_, 4);
lean_dec(v_unused_3392_);
v_unused_3393_ = lean_ctor_get(v_r_3369_, 3);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_r_3369_, 0);
lean_dec(v_unused_3394_);
v___x_3378_ = v_r_3369_;
v_isShared_3379_ = v_isSharedCheck_3391_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_v_3376_);
lean_inc(v_k_3375_);
lean_dec(v_r_3369_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3391_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3380_ = lean_unsigned_to_nat(3u);
v___x_3381_ = lean_unsigned_to_nat(1u);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 4, v_l_3331_);
lean_ctor_set(v___x_3378_, 3, v_l_3331_);
lean_ctor_set(v___x_3378_, 2, v_v_3371_);
lean_ctor_set(v___x_3378_, 1, v_k_3370_);
lean_ctor_set(v___x_3378_, 0, v___x_3381_);
v___x_3383_ = v___x_3378_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_k_3370_);
lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_v_3371_);
lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_l_3331_);
v___x_3383_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 4, v_l_3331_);
lean_ctor_set(v___x_3373_, 2, v_v_3225_);
lean_ctor_set(v___x_3373_, 1, v_k_3224_);
lean_ctor_set(v___x_3373_, 0, v___x_3381_);
v___x_3385_ = v___x_3373_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3389_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3389_, 3, v_l_3331_);
lean_ctor_set(v_reuseFailAlloc_3389_, 4, v_l_3331_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3385_);
lean_ctor_set(v___x_3229_, 3, v___x_3383_);
lean_ctor_set(v___x_3229_, 2, v_v_3376_);
lean_ctor_set(v___x_3229_, 1, v_k_3375_);
lean_ctor_set(v___x_3229_, 0, v___x_3380_);
v___x_3387_ = v___x_3229_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_k_3375_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_v_3376_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_unsigned_to_nat(2u);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v_r_3369_);
lean_ctor_set(v___x_3229_, 3, v___x_3232_);
lean_ctor_set(v___x_3229_, 0, v___x_3399_);
v___x_3401_ = v___x_3229_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3402_, 3, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3402_, 4, v_r_3369_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_unsigned_to_nat(1u);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3232_);
lean_ctor_set(v___x_3229_, 3, v___x_3232_);
lean_ctor_set(v___x_3229_, 0, v___x_3403_);
v___x_3405_ = v___x_3229_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v___x_3232_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
case 1:
{
lean_object* v___x_3408_; 
lean_dec(v_v_3225_);
lean_dec(v_k_3224_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 2, v_v_3221_);
lean_ctor_set(v___x_3229_, 1, v_k_3220_);
v___x_3408_ = v___x_3229_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_size_3223_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_k_3220_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_v_3221_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v_l_3226_);
lean_ctor_set(v_reuseFailAlloc_3409_, 4, v_r_3227_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
default: 
{
lean_object* v___x_3410_; 
lean_dec(v_size_3223_);
v___x_3410_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v_k_3220_, v_v_3221_, v_r_3227_);
if (lean_obj_tag(v_l_3226_) == 0)
{
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_size_3411_; lean_object* v_size_3412_; lean_object* v_k_3413_; lean_object* v_v_3414_; lean_object* v_l_3415_; lean_object* v_r_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v_size_3411_ = lean_ctor_get(v_l_3226_, 0);
v_size_3412_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_size_3412_);
v_k_3413_ = lean_ctor_get(v___x_3410_, 1);
lean_inc(v_k_3413_);
v_v_3414_ = lean_ctor_get(v___x_3410_, 2);
lean_inc(v_v_3414_);
v_l_3415_ = lean_ctor_get(v___x_3410_, 3);
lean_inc(v_l_3415_);
v_r_3416_ = lean_ctor_get(v___x_3410_, 4);
lean_inc(v_r_3416_);
v___x_3417_ = lean_unsigned_to_nat(3u);
v___x_3418_ = lean_nat_mul(v___x_3417_, v_size_3411_);
v___x_3419_ = lean_nat_dec_lt(v___x_3418_, v_size_3412_);
lean_dec(v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_dec(v_r_3416_);
lean_dec(v_l_3415_);
lean_dec(v_v_3414_);
lean_dec(v_k_3413_);
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_add(v___x_3420_, v_size_3411_);
v___x_3422_ = lean_nat_add(v___x_3421_, v_size_3412_);
lean_dec(v_size_3412_);
lean_dec(v___x_3421_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3410_);
lean_ctor_set(v___x_3229_, 0, v___x_3422_);
v___x_3424_ = v___x_3229_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_l_3226_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v___x_3410_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
else
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3495_; 
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; lean_object* v_unused_3497_; lean_object* v_unused_3498_; lean_object* v_unused_3499_; lean_object* v_unused_3500_; 
v_unused_3496_ = lean_ctor_get(v___x_3410_, 4);
lean_dec(v_unused_3496_);
v_unused_3497_ = lean_ctor_get(v___x_3410_, 3);
lean_dec(v_unused_3497_);
v_unused_3498_ = lean_ctor_get(v___x_3410_, 2);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v___x_3410_, 1);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v___x_3410_, 0);
lean_dec(v_unused_3500_);
v___x_3427_ = v___x_3410_;
v_isShared_3428_ = v_isSharedCheck_3495_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v___x_3410_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3495_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
if (lean_obj_tag(v_l_3415_) == 0)
{
if (lean_obj_tag(v_r_3416_) == 0)
{
lean_object* v_size_3429_; lean_object* v_k_3430_; lean_object* v_v_3431_; lean_object* v_l_3432_; lean_object* v_r_3433_; lean_object* v_size_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_size_3429_ = lean_ctor_get(v_l_3415_, 0);
v_k_3430_ = lean_ctor_get(v_l_3415_, 1);
v_v_3431_ = lean_ctor_get(v_l_3415_, 2);
v_l_3432_ = lean_ctor_get(v_l_3415_, 3);
v_r_3433_ = lean_ctor_get(v_l_3415_, 4);
v_size_3434_ = lean_ctor_get(v_r_3416_, 0);
v___x_3435_ = lean_unsigned_to_nat(2u);
v___x_3436_ = lean_nat_mul(v___x_3435_, v_size_3434_);
v___x_3437_ = lean_nat_dec_lt(v_size_3429_, v___x_3436_);
lean_dec(v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3466_; 
lean_inc(v_r_3433_);
lean_inc(v_l_3432_);
lean_inc(v_v_3431_);
lean_inc(v_k_3430_);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_l_3415_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; lean_object* v_unused_3469_; lean_object* v_unused_3470_; lean_object* v_unused_3471_; 
v_unused_3467_ = lean_ctor_get(v_l_3415_, 4);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_l_3415_, 3);
lean_dec(v_unused_3468_);
v_unused_3469_ = lean_ctor_get(v_l_3415_, 2);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v_l_3415_, 1);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_l_3415_, 0);
lean_dec(v_unused_3471_);
v___x_3439_ = v_l_3415_;
v_isShared_3440_ = v_isSharedCheck_3466_;
goto v_resetjp_3438_;
}
else
{
lean_dec(v_l_3415_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3466_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3456_; 
v___x_3441_ = lean_unsigned_to_nat(1u);
v___x_3442_ = lean_nat_add(v___x_3441_, v_size_3411_);
v___x_3443_ = lean_nat_add(v___x_3442_, v_size_3412_);
lean_dec(v_size_3412_);
if (lean_obj_tag(v_l_3432_) == 0)
{
lean_object* v_size_3464_; 
v_size_3464_ = lean_ctor_get(v_l_3432_, 0);
lean_inc(v_size_3464_);
v___y_3456_ = v_size_3464_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_unsigned_to_nat(0u);
v___y_3456_ = v___x_3465_;
goto v___jp_3455_;
}
v___jp_3444_:
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3448_ = lean_nat_add(v___y_3445_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec(v___y_3445_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 4, v_r_3416_);
lean_ctor_set(v___x_3439_, 3, v_r_3433_);
lean_ctor_set(v___x_3439_, 2, v_v_3414_);
lean_ctor_set(v___x_3439_, 1, v_k_3413_);
lean_ctor_set(v___x_3439_, 0, v___x_3448_);
v___x_3450_ = v___x_3439_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_k_3413_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_v_3414_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_r_3433_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_r_3416_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3452_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 4, v___x_3450_);
lean_ctor_set(v___x_3427_, 3, v___y_3446_);
lean_ctor_set(v___x_3427_, 2, v_v_3431_);
lean_ctor_set(v___x_3427_, 1, v_k_3430_);
lean_ctor_set(v___x_3427_, 0, v___x_3443_);
v___x_3452_ = v___x_3427_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_k_3430_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_v_3431_);
lean_ctor_set(v_reuseFailAlloc_3453_, 3, v___y_3446_);
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
v___jp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3457_ = lean_nat_add(v___x_3442_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec(v___x_3442_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v_l_3432_);
lean_ctor_set(v___x_3229_, 0, v___x_3457_);
v___x_3459_ = v___x_3229_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_l_3226_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v_l_3432_);
v___x_3459_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_nat_add(v___x_3441_, v_size_3434_);
if (lean_obj_tag(v_r_3433_) == 0)
{
lean_object* v_size_3461_; 
v_size_3461_ = lean_ctor_get(v_r_3433_, 0);
lean_inc(v_size_3461_);
v___y_3445_ = v___x_3460_;
v___y_3446_ = v___x_3459_;
v___y_3447_ = v_size_3461_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_unsigned_to_nat(0u);
v___y_3445_ = v___x_3460_;
v___y_3446_ = v___x_3459_;
v___y_3447_ = v___x_3462_;
goto v___jp_3444_;
}
}
}
}
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
lean_del_object(v___x_3229_);
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_add(v___x_3472_, v_size_3411_);
v___x_3474_ = lean_nat_add(v___x_3473_, v_size_3412_);
lean_dec(v_size_3412_);
v___x_3475_ = lean_nat_add(v___x_3473_, v_size_3429_);
lean_dec(v___x_3473_);
lean_inc_ref(v_l_3226_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 4, v_l_3415_);
lean_ctor_set(v___x_3427_, 3, v_l_3226_);
lean_ctor_set(v___x_3427_, 2, v_v_3225_);
lean_ctor_set(v___x_3427_, 1, v_k_3224_);
lean_ctor_set(v___x_3427_, 0, v___x_3475_);
v___x_3477_ = v___x_3427_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_l_3226_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_l_3415_);
v___x_3477_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v_isSharedCheck_3484_ = !lean_is_exclusive(v_l_3226_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; lean_object* v_unused_3486_; lean_object* v_unused_3487_; lean_object* v_unused_3488_; lean_object* v_unused_3489_; 
v_unused_3485_ = lean_ctor_get(v_l_3226_, 4);
lean_dec(v_unused_3485_);
v_unused_3486_ = lean_ctor_get(v_l_3226_, 3);
lean_dec(v_unused_3486_);
v_unused_3487_ = lean_ctor_get(v_l_3226_, 2);
lean_dec(v_unused_3487_);
v_unused_3488_ = lean_ctor_get(v_l_3226_, 1);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_l_3226_, 0);
lean_dec(v_unused_3489_);
v___x_3479_ = v_l_3226_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v_l_3226_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 4, v_r_3416_);
lean_ctor_set(v___x_3479_, 3, v___x_3477_);
lean_ctor_set(v___x_3479_, 2, v_v_3414_);
lean_ctor_set(v___x_3479_, 1, v_k_3413_);
lean_ctor_set(v___x_3479_, 0, v___x_3474_);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_3413_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_3414_);
lean_ctor_set(v_reuseFailAlloc_3483_, 3, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_r_3416_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref_known(v_l_3415_, 5);
lean_del_object(v___x_3427_);
lean_dec(v_v_3414_);
lean_dec(v_k_3413_);
lean_dec(v_size_3412_);
lean_dec_ref_known(v_l_3226_, 5);
lean_del_object(v___x_3229_);
lean_dec(v_v_3225_);
lean_dec(v_k_3224_);
v___x_3491_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__7);
v___x_3492_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3491_);
return v___x_3492_;
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_del_object(v___x_3427_);
lean_dec(v_r_3416_);
lean_dec(v_v_3414_);
lean_dec(v_k_3413_);
lean_dec(v_size_3412_);
lean_dec_ref_known(v_l_3226_, 5);
lean_del_object(v___x_3229_);
lean_dec(v_v_3225_);
lean_dec(v_k_3224_);
v___x_3493_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg___closed__8);
v___x_3494_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v___x_3493_);
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_size_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3505_; 
v_size_3501_ = lean_ctor_get(v_l_3226_, 0);
v___x_3502_ = lean_unsigned_to_nat(1u);
v___x_3503_ = lean_nat_add(v___x_3502_, v_size_3501_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3410_);
lean_ctor_set(v___x_3229_, 0, v___x_3503_);
v___x_3505_ = v___x_3229_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_l_3226_);
lean_ctor_set(v_reuseFailAlloc_3506_, 4, v___x_3410_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
else
{
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_l_3507_; 
v_l_3507_ = lean_ctor_get(v___x_3410_, 3);
lean_inc(v_l_3507_);
if (lean_obj_tag(v_l_3507_) == 0)
{
lean_object* v_r_3508_; 
v_r_3508_ = lean_ctor_get(v___x_3410_, 4);
lean_inc(v_r_3508_);
if (lean_obj_tag(v_r_3508_) == 0)
{
lean_object* v_size_3509_; lean_object* v_k_3510_; lean_object* v_v_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3525_; 
v_size_3509_ = lean_ctor_get(v___x_3410_, 0);
v_k_3510_ = lean_ctor_get(v___x_3410_, 1);
v_v_3511_ = lean_ctor_get(v___x_3410_, 2);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; lean_object* v_unused_3527_; 
v_unused_3526_ = lean_ctor_get(v___x_3410_, 4);
lean_dec(v_unused_3526_);
v_unused_3527_ = lean_ctor_get(v___x_3410_, 3);
lean_dec(v_unused_3527_);
v___x_3513_ = v___x_3410_;
v_isShared_3514_ = v_isSharedCheck_3525_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_v_3511_);
lean_inc(v_k_3510_);
lean_inc(v_size_3509_);
lean_dec(v___x_3410_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3525_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_size_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v_size_3515_ = lean_ctor_get(v_l_3507_, 0);
v___x_3516_ = lean_unsigned_to_nat(1u);
v___x_3517_ = lean_nat_add(v___x_3516_, v_size_3509_);
lean_dec(v_size_3509_);
v___x_3518_ = lean_nat_add(v___x_3516_, v_size_3515_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 4, v_l_3507_);
lean_ctor_set(v___x_3513_, 3, v_l_3226_);
lean_ctor_set(v___x_3513_, 2, v_v_3225_);
lean_ctor_set(v___x_3513_, 1, v_k_3224_);
lean_ctor_set(v___x_3513_, 0, v___x_3518_);
v___x_3520_ = v___x_3513_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_l_3226_);
lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_l_3507_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v_r_3508_);
lean_ctor_set(v___x_3229_, 3, v___x_3520_);
lean_ctor_set(v___x_3229_, 2, v_v_3511_);
lean_ctor_set(v___x_3229_, 1, v_k_3510_);
lean_ctor_set(v___x_3229_, 0, v___x_3517_);
v___x_3522_ = v___x_3229_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_k_3510_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_v_3511_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v_r_3508_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v_k_3528_; lean_object* v_v_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3553_; 
v_k_3528_ = lean_ctor_get(v___x_3410_, 1);
v_v_3529_ = lean_ctor_get(v___x_3410_, 2);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; lean_object* v_unused_3555_; lean_object* v_unused_3556_; 
v_unused_3554_ = lean_ctor_get(v___x_3410_, 4);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v___x_3410_, 3);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v___x_3410_, 0);
lean_dec(v_unused_3556_);
v___x_3531_ = v___x_3410_;
v_isShared_3532_ = v_isSharedCheck_3553_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_v_3529_);
lean_inc(v_k_3528_);
lean_dec(v___x_3410_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3553_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_k_3533_; lean_object* v_v_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3549_; 
v_k_3533_ = lean_ctor_get(v_l_3507_, 1);
v_v_3534_ = lean_ctor_get(v_l_3507_, 2);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_l_3507_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; lean_object* v_unused_3551_; lean_object* v_unused_3552_; 
v_unused_3550_ = lean_ctor_get(v_l_3507_, 4);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_l_3507_, 3);
lean_dec(v_unused_3551_);
v_unused_3552_ = lean_ctor_get(v_l_3507_, 0);
lean_dec(v_unused_3552_);
v___x_3536_ = v_l_3507_;
v_isShared_3537_ = v_isSharedCheck_3549_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_v_3534_);
lean_inc(v_k_3533_);
lean_dec(v_l_3507_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3549_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3538_ = lean_unsigned_to_nat(3u);
v___x_3539_ = lean_unsigned_to_nat(1u);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 4, v_r_3508_);
lean_ctor_set(v___x_3536_, 3, v_r_3508_);
lean_ctor_set(v___x_3536_, 2, v_v_3225_);
lean_ctor_set(v___x_3536_, 1, v_k_3224_);
lean_ctor_set(v___x_3536_, 0, v___x_3539_);
v___x_3541_ = v___x_3536_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_r_3508_);
lean_ctor_set(v_reuseFailAlloc_3548_, 4, v_r_3508_);
v___x_3541_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 3, v_r_3508_);
lean_ctor_set(v___x_3531_, 0, v___x_3539_);
v___x_3543_ = v___x_3531_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_k_3528_);
lean_ctor_set(v_reuseFailAlloc_3547_, 2, v_v_3529_);
lean_ctor_set(v_reuseFailAlloc_3547_, 3, v_r_3508_);
lean_ctor_set(v_reuseFailAlloc_3547_, 4, v_r_3508_);
v___x_3543_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3543_);
lean_ctor_set(v___x_3229_, 3, v___x_3541_);
lean_ctor_set(v___x_3229_, 2, v_v_3534_);
lean_ctor_set(v___x_3229_, 1, v_k_3533_);
lean_ctor_set(v___x_3229_, 0, v___x_3538_);
v___x_3545_ = v___x_3229_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_k_3533_);
lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_v_3534_);
lean_ctor_set(v_reuseFailAlloc_3546_, 3, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3546_, 4, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3557_; 
v_r_3557_ = lean_ctor_get(v___x_3410_, 4);
lean_inc(v_r_3557_);
if (lean_obj_tag(v_r_3557_) == 0)
{
lean_object* v_k_3558_; lean_object* v_v_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3571_; 
v_k_3558_ = lean_ctor_get(v___x_3410_, 1);
v_v_3559_ = lean_ctor_get(v___x_3410_, 2);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; lean_object* v_unused_3573_; lean_object* v_unused_3574_; 
v_unused_3572_ = lean_ctor_get(v___x_3410_, 4);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v___x_3410_, 3);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v___x_3410_, 0);
lean_dec(v_unused_3574_);
v___x_3561_ = v___x_3410_;
v_isShared_3562_ = v_isSharedCheck_3571_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_v_3559_);
lean_inc(v_k_3558_);
lean_dec(v___x_3410_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3571_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3563_ = lean_unsigned_to_nat(3u);
v___x_3564_ = lean_unsigned_to_nat(1u);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 4, v_l_3507_);
lean_ctor_set(v___x_3561_, 2, v_v_3225_);
lean_ctor_set(v___x_3561_, 1, v_k_3224_);
lean_ctor_set(v___x_3561_, 0, v___x_3564_);
v___x_3566_ = v___x_3561_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3570_, 3, v_l_3507_);
lean_ctor_set(v_reuseFailAlloc_3570_, 4, v_l_3507_);
v___x_3566_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v_r_3557_);
lean_ctor_set(v___x_3229_, 3, v___x_3566_);
lean_ctor_set(v___x_3229_, 2, v_v_3559_);
lean_ctor_set(v___x_3229_, 1, v_k_3558_);
lean_ctor_set(v___x_3229_, 0, v___x_3563_);
v___x_3568_ = v___x_3229_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3558_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3559_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_r_3557_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3575_ = lean_unsigned_to_nat(2u);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3410_);
lean_ctor_set(v___x_3229_, 3, v_r_3557_);
lean_ctor_set(v___x_3229_, 0, v___x_3575_);
v___x_3577_ = v___x_3229_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3578_, 3, v_r_3557_);
lean_ctor_set(v_reuseFailAlloc_3578_, 4, v___x_3410_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3579_ = lean_unsigned_to_nat(1u);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3410_);
lean_ctor_set(v___x_3229_, 3, v___x_3410_);
lean_ctor_set(v___x_3229_, 0, v___x_3579_);
v___x_3581_ = v___x_3229_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_k_3224_);
lean_ctor_set(v_reuseFailAlloc_3582_, 2, v_v_3225_);
lean_ctor_set(v_reuseFailAlloc_3582_, 3, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3582_, 4, v___x_3410_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = lean_unsigned_to_nat(1u);
v___x_3585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
lean_ctor_set(v___x_3585_, 1, v_k_3220_);
lean_ctor_set(v___x_3585_, 2, v_v_3221_);
lean_ctor_set(v___x_3585_, 3, v_t_3222_);
lean_ctor_set(v___x_3585_, 4, v_t_3222_);
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(lean_object* v_init_3586_, lean_object* v_x_3587_){
_start:
{
if (lean_obj_tag(v_x_3587_) == 0)
{
lean_object* v_k_3588_; lean_object* v_v_3589_; lean_object* v_l_3590_; lean_object* v_r_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_k_3588_ = lean_ctor_get(v_x_3587_, 1);
lean_inc(v_k_3588_);
v_v_3589_ = lean_ctor_get(v_x_3587_, 2);
lean_inc(v_v_3589_);
v_l_3590_ = lean_ctor_get(v_x_3587_, 3);
lean_inc(v_l_3590_);
v_r_3591_ = lean_ctor_get(v_x_3587_, 4);
lean_inc(v_r_3591_);
lean_dec_ref_known(v_x_3587_, 5);
v___x_3592_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(v_init_3586_, v_l_3590_);
v___x_3593_ = 1;
v___x_3594_ = l_Lean_Name_toString(v_k_3588_, v___x_3593_);
v___x_3595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_v_3589_);
v___x_3596_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v___x_3594_, v___x_3595_, v___x_3592_);
v_init_3586_ = v___x_3596_;
v_x_3587_ = v_r_3591_;
goto _start;
}
else
{
return v_init_3586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_m_3598_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3599_ = lean_box(1);
v___x_3600_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(v___x_3599_, v_m_3598_);
v___x_3601_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(lean_object* v___x_3604_, uint8_t v_updateToolchain_3605_, lean_object* v_ws_3606_, lean_object* v_dep_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_baseName_3611_; lean_object* v_name_3612_; lean_object* v_opts_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v_baseName_3611_ = lean_ctor_get(v___x_3604_, 1);
v_name_3612_ = lean_ctor_get(v_dep_3607_, 0);
v_opts_3613_ = lean_ctor_get(v_dep_3607_, 4);
v___x_3614_ = 0;
lean_inc(v_baseName_3611_);
v___x_3615_ = l_Lean_Name_toString(v_baseName_3611_, v___x_3614_);
v___x_3616_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__0));
v___x_3617_ = lean_string_append(v___x_3615_, v___x_3616_);
lean_inc(v_name_3612_);
v___x_3618_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3612_, v_updateToolchain_3605_);
v___x_3619_ = lean_string_append(v___x_3617_, v___x_3618_);
lean_dec_ref(v___x_3618_);
v___x_3620_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___closed__1));
v___x_3621_ = lean_string_append(v___x_3619_, v___x_3620_);
lean_inc(v_opts_3613_);
v___x_3622_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_opts_3613_);
v___x_3623_ = lean_unsigned_to_nat(80u);
v___x_3624_ = l_Lean_Json_pretty(v___x_3622_, v___x_3623_);
v___x_3625_ = lean_string_append(v___x_3621_, v___x_3624_);
lean_dec_ref(v___x_3624_);
v___x_3626_ = 0;
v___x_3627_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set_uint8(v___x_3627_, sizeof(void*)*1, v___x_3626_);
lean_inc_ref(v___y_3609_);
v___x_3628_ = lean_apply_2(v___y_3609_, v___x_3627_, lean_box(0));
v___x_3629_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_3606_, v___x_3604_, v_dep_3607_, v___y_3608_, v___y_3609_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed(lean_object* v___x_3630_, lean_object* v_updateToolchain_3631_, lean_object* v_ws_3632_, lean_object* v_dep_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
uint8_t v_updateToolchain_boxed_3637_; lean_object* v_res_3638_; 
v_updateToolchain_boxed_3637_ = lean_unbox(v_updateToolchain_3631_);
v_res_3638_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0(v___x_3630_, v_updateToolchain_boxed_3637_, v_ws_3632_, v_dep_3633_, v___y_3634_, v___y_3635_);
lean_dec_ref(v___y_3635_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_val_3639_, size_t v_sz_3640_, size_t v_i_3641_, lean_object* v_bs_3642_){
_start:
{
uint8_t v___x_3643_; 
v___x_3643_ = lean_usize_dec_lt(v_i_3641_, v_sz_3640_);
if (v___x_3643_ == 0)
{
return v_bs_3642_;
}
else
{
lean_object* v_packages_3644_; lean_object* v_v_3645_; lean_object* v___x_3646_; lean_object* v_bs_x27_3647_; lean_object* v___x_3648_; size_t v___x_3649_; size_t v___x_3650_; lean_object* v___x_3651_; 
v_packages_3644_ = lean_ctor_get(v_val_3639_, 4);
v_v_3645_ = lean_array_uget(v_bs_3642_, v_i_3641_);
v___x_3646_ = lean_unsigned_to_nat(0u);
v_bs_x27_3647_ = lean_array_uset(v_bs_3642_, v_i_3641_, v___x_3646_);
v___x_3648_ = lean_array_fget_borrowed(v_packages_3644_, v_v_3645_);
lean_dec(v_v_3645_);
v___x_3649_ = ((size_t)1ULL);
v___x_3650_ = lean_usize_add(v_i_3641_, v___x_3649_);
lean_inc(v___x_3648_);
v___x_3651_ = lean_array_uset(v_bs_x27_3647_, v_i_3641_, v___x_3648_);
v_i_3641_ = v___x_3650_;
v_bs_3642_ = v___x_3651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_val_3653_, lean_object* v_sz_3654_, lean_object* v_i_3655_, lean_object* v_bs_3656_){
_start:
{
size_t v_sz_boxed_3657_; size_t v_i_boxed_3658_; lean_object* v_res_3659_; 
v_sz_boxed_3657_ = lean_unbox_usize(v_sz_3654_);
lean_dec(v_sz_3654_);
v_i_boxed_3658_ = lean_unbox_usize(v_i_3655_);
lean_dec(v_i_3655_);
v_res_3659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_val_3653_, v_sz_boxed_3657_, v_i_boxed_3658_, v_bs_3656_);
lean_dec_ref(v_val_3653_);
return v_res_3659_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0(lean_object* v___x_3660_, lean_object* v_x_3661_){
_start:
{
lean_object* v_baseName_3662_; lean_object* v_name_3663_; uint8_t v___x_3664_; 
v_baseName_3662_ = lean_ctor_get(v_x_3661_, 1);
v_name_3663_ = lean_ctor_get(v___x_3660_, 0);
v___x_3664_ = lean_name_eq(v_baseName_3662_, v_name_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed(lean_object* v___x_3665_, lean_object* v_x_3666_){
_start:
{
uint8_t v_res_3667_; lean_object* v_r_3668_; 
v_res_3667_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0(v___x_3665_, v_x_3666_);
lean_dec_ref(v_x_3666_);
lean_dec_ref(v___x_3665_);
v_r_3668_ = lean_box(v_res_3667_);
return v_r_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(lean_object* v_pkg_3669_, lean_object* v_leanOpts_3670_, uint8_t v_reconfigure_3671_, lean_object* v_as_3672_, size_t v_i_3673_, size_t v_stop_3674_, lean_object* v_b_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v___x_3682_; 
v___x_3682_ = lean_usize_dec_eq(v_i_3673_, v_stop_3674_);
if (v___x_3682_ == 0)
{
lean_object* v_ws_3683_; lean_object* v_depIdxs_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3799_; 
v_ws_3683_ = lean_ctor_get(v_b_3675_, 0);
v_depIdxs_3684_ = lean_ctor_get(v_b_3675_, 1);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_b_3675_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3686_ = v_b_3675_;
v_isShared_3687_ = v_isSharedCheck_3799_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_depIdxs_3684_);
lean_inc(v_ws_3683_);
lean_dec(v_b_3675_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3799_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_packages_3688_; size_t v___x_3689_; size_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___f_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_packages_3688_ = lean_ctor_get(v_ws_3683_, 4);
v___x_3689_ = ((size_t)1ULL);
v___x_3690_ = lean_usize_sub(v_i_3673_, v___x_3689_);
v___x_3691_ = lean_array_uget_borrowed(v_as_3672_, v___x_3690_);
lean_inc(v___x_3691_);
v___f_3692_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3692_, 0, v___x_3691_);
v___x_3693_ = lean_unsigned_to_nat(0u);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3692_, v_packages_3688_, v___x_3693_);
if (lean_obj_tag(v___x_3694_) == 1)
{
lean_object* v_val_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
v_val_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_val_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v___x_3696_ = lean_array_push(v_depIdxs_3684_, v_val_3695_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___x_3696_);
v___x_3698_ = v___x_3686_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_ws_3683_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
v_i_3673_ = v___x_3690_;
v_b_3675_ = v___x_3698_;
goto _start;
}
}
else
{
lean_object* v_baseName_3701_; lean_object* v_name_3702_; lean_object* v_opts_3703_; uint8_t v___x_3704_; 
lean_inc_ref(v_packages_3688_);
lean_dec(v___x_3694_);
v_baseName_3701_ = lean_ctor_get(v_pkg_3669_, 1);
v_name_3702_ = lean_ctor_get(v___x_3691_, 0);
v_opts_3703_ = lean_ctor_get(v___x_3691_, 4);
v___x_3704_ = lean_name_eq(v_baseName_3701_, v_name_3702_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; 
lean_inc_ref(v___y_3677_);
lean_inc_ref(v_ws_3683_);
lean_inc(v___x_3691_);
lean_inc_ref(v_pkg_3669_);
v___x_3705_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_3669_, v___x_3691_, v_ws_3683_, v___y_3676_, v___y_3677_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3782_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3782_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3782_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v_fst_3710_; lean_object* v_snd_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_fst_3710_ = lean_ctor_get(v_a_3706_, 0);
lean_inc(v_fst_3710_);
v_snd_3711_ = lean_ctor_get(v_a_3706_, 1);
lean_inc(v_snd_3711_);
lean_dec(v_a_3706_);
v___x_3712_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3670_);
lean_inc(v_opts_3703_);
v___x_3713_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_3683_, v_fst_3710_, v_opts_3703_, v_leanOpts_3670_, v_reconfigure_3671_, v___x_3712_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v_a_3715_; lean_object* v_wsIdx_3716_; lean_object* v___x_3717_; lean_object* v___x_3719_; 
lean_del_object(v___x_3708_);
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
v_a_3715_ = lean_ctor_get(v___x_3713_, 1);
lean_inc(v_a_3715_);
lean_dec_ref_known(v___x_3713_, 2);
v_wsIdx_3716_ = lean_array_get_size(v_packages_3688_);
lean_dec_ref(v_packages_3688_);
v___x_3717_ = lean_array_push(v_depIdxs_3684_, v_wsIdx_3716_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___x_3717_);
lean_ctor_set(v___x_3686_, 0, v_a_3714_);
v___x_3719_ = v___x_3686_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3714_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v___x_3717_);
v___x_3719_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3720_ = lean_array_get_size(v_a_3715_);
v___x_3721_ = lean_nat_dec_lt(v___x_3693_, v___x_3720_);
if (v___x_3721_ == 0)
{
lean_dec(v_a_3715_);
v_i_3673_ = v___x_3690_;
v_b_3675_ = v___x_3719_;
v___y_3676_ = v_snd_3711_;
goto _start;
}
else
{
lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_nat_dec_le(v___x_3720_, v___x_3720_);
if (v___x_3724_ == 0)
{
if (v___x_3721_ == 0)
{
lean_dec(v_a_3715_);
v_i_3673_ = v___x_3690_;
v_b_3675_ = v___x_3719_;
v___y_3676_ = v_snd_3711_;
goto _start;
}
else
{
size_t v___x_3726_; size_t v___x_3727_; lean_object* v___x_3728_; 
v___x_3726_ = ((size_t)0ULL);
v___x_3727_ = lean_usize_of_nat(v___x_3720_);
v___x_3728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3715_, v___x_3726_, v___x_3727_, v___x_3723_, v___y_3677_);
lean_dec(v_a_3715_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_dec_ref_known(v___x_3728_, 1);
v_i_3673_ = v___x_3690_;
v_b_3675_ = v___x_3719_;
v___y_3676_ = v_snd_3711_;
goto _start;
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___x_3719_);
lean_dec(v_snd_3711_);
lean_dec_ref(v_leanOpts_3670_);
lean_dec_ref(v_pkg_3669_);
v_a_3730_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3728_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3728_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
else
{
size_t v___x_3738_; size_t v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = ((size_t)0ULL);
v___x_3739_ = lean_usize_of_nat(v___x_3720_);
v___x_3740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3715_, v___x_3738_, v___x_3739_, v___x_3723_, v___y_3677_);
lean_dec(v_a_3715_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_dec_ref_known(v___x_3740_, 1);
v_i_3673_ = v___x_3690_;
v_b_3675_ = v___x_3719_;
v___y_3676_ = v_snd_3711_;
goto _start;
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v___x_3719_);
lean_dec(v_snd_3711_);
lean_dec_ref(v_leanOpts_3670_);
lean_dec_ref(v_pkg_3669_);
v_a_3742_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3740_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3740_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
lean_dec(v_snd_3711_);
lean_dec_ref(v_packages_3688_);
lean_del_object(v___x_3686_);
lean_dec_ref(v_depIdxs_3684_);
lean_dec_ref(v_leanOpts_3670_);
lean_dec_ref(v_pkg_3669_);
v_a_3751_ = lean_ctor_get(v___x_3713_, 1);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3713_, 2);
v___x_3752_ = lean_array_get_size(v_a_3751_);
v___x_3753_ = lean_nat_dec_lt(v___x_3693_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_dec(v_a_3751_);
v___x_3754_ = lean_box(0);
if (v_isShared_3709_ == 0)
{
lean_ctor_set_tag(v___x_3708_, 1);
lean_ctor_set(v___x_3708_, 0, v___x_3754_);
v___x_3756_ = v___x_3708_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
else
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
lean_del_object(v___x_3708_);
v___x_3758_ = lean_box(0);
v___x_3759_ = lean_nat_dec_le(v___x_3752_, v___x_3752_);
if (v___x_3759_ == 0)
{
if (v___x_3753_ == 0)
{
lean_dec(v_a_3751_);
goto v___jp_3679_;
}
else
{
size_t v___x_3760_; size_t v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = ((size_t)0ULL);
v___x_3761_ = lean_usize_of_nat(v___x_3752_);
v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3751_, v___x_3760_, v___x_3761_, v___x_3758_, v___y_3677_);
lean_dec(v_a_3751_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec_ref_known(v___x_3762_, 1);
goto v___jp_3679_;
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
else
{
size_t v___x_3771_; size_t v___x_3772_; lean_object* v___x_3773_; 
v___x_3771_ = ((size_t)0ULL);
v___x_3772_ = lean_usize_of_nat(v___x_3752_);
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3751_, v___x_3771_, v___x_3772_, v___x_3758_, v___y_3677_);
lean_dec(v_a_3751_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_dec_ref_known(v___x_3773_, 1);
goto v___jp_3679_;
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3773_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3773_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
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
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v_packages_3688_);
lean_del_object(v___x_3686_);
lean_dec_ref(v_depIdxs_3684_);
lean_dec_ref(v_ws_3683_);
lean_dec_ref(v_leanOpts_3670_);
lean_dec_ref(v_pkg_3669_);
v_a_3783_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3705_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3705_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
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
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_inc(v_baseName_3701_);
lean_dec_ref(v_packages_3688_);
lean_del_object(v___x_3686_);
lean_dec_ref(v_depIdxs_3684_);
lean_dec_ref(v_ws_3683_);
lean_dec(v___y_3676_);
lean_dec_ref(v_leanOpts_3670_);
lean_dec_ref(v_pkg_3669_);
v___x_3791_ = l_Lean_Name_toString(v_baseName_3701_, v___x_3682_);
v___x_3792_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_3793_ = lean_string_append(v___x_3791_, v___x_3792_);
v___x_3794_ = 3;
v___x_3795_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set_uint8(v___x_3795_, sizeof(void*)*1, v___x_3794_);
lean_inc_ref(v___y_3677_);
v___x_3796_ = lean_apply_2(v___y_3677_, v___x_3795_, lean_box(0));
v___x_3797_ = lean_box(0);
v___x_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
return v___x_3798_;
}
}
}
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec_ref(v_leanOpts_3670_);
lean_dec_ref(v_pkg_3669_);
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v_b_3675_);
lean_ctor_set(v___x_3800_, 1, v___y_3676_);
v___x_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
return v___x_3801_;
}
v___jp_3679_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_box(0);
v___x_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
return v___x_3681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___boxed(lean_object* v_pkg_3802_, lean_object* v_leanOpts_3803_, lean_object* v_reconfigure_3804_, lean_object* v_as_3805_, lean_object* v_i_3806_, lean_object* v_stop_3807_, lean_object* v_b_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
uint8_t v_reconfigure_boxed_3812_; size_t v_i_boxed_3813_; size_t v_stop_boxed_3814_; lean_object* v_res_3815_; 
v_reconfigure_boxed_3812_ = lean_unbox(v_reconfigure_3804_);
v_i_boxed_3813_ = lean_unbox_usize(v_i_3806_);
lean_dec(v_i_3806_);
v_stop_boxed_3814_ = lean_unbox_usize(v_stop_3807_);
lean_dec(v_stop_3807_);
v_res_3815_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3802_, v_leanOpts_3803_, v_reconfigure_boxed_3812_, v_as_3805_, v_i_boxed_3813_, v_stop_boxed_3814_, v_b_3808_, v___y_3809_, v___y_3810_);
lean_dec_ref(v___y_3810_);
lean_dec_ref(v_as_3805_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(lean_object* v_leanOpts_3816_, uint8_t v_reconfigure_3817_, lean_object* v_ws_3818_, lean_object* v_wsIdx_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_packages_3823_; lean_object* v_pkg_3824_; lean_object* v_depConfigs_3825_; lean_object* v_start_3826_; lean_object* v_ws_3828_; lean_object* v_packages_3829_; lean_object* v_depIdxs_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v_____x_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v_s_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v_packages_3823_ = lean_ctor_get(v_ws_3818_, 4);
v_pkg_3824_ = lean_array_fget(v_packages_3823_, v_wsIdx_3819_);
v_depConfigs_3825_ = lean_ctor_get(v_pkg_3824_, 12);
v_start_3826_ = lean_array_get_size(v_packages_3823_);
v___x_3863_ = lean_array_get_size(v_depConfigs_3825_);
v___x_3864_ = lean_mk_empty_array_with_capacity(v___x_3863_);
lean_inc_ref(v___x_3864_);
lean_inc_ref(v_ws_3818_);
v_s_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_3865_, 0, v_ws_3818_);
lean_ctor_set(v_s_3865_, 1, v___x_3864_);
v___x_3866_ = lean_unsigned_to_nat(0u);
v___x_3867_ = lean_nat_dec_le(v___x_3863_, v___x_3863_);
if (v___x_3867_ == 0)
{
uint8_t v___x_3868_; 
v___x_3868_ = lean_nat_dec_lt(v___x_3866_, v___x_3863_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
lean_dec_ref_known(v_s_3865_, 2);
v___x_3869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_start_3826_, v_leanOpts_3816_, v_reconfigure_3817_, v_start_3826_, v_ws_3818_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3890_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3872_ = v___x_3869_;
v_isShared_3873_ = v_isSharedCheck_3890_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3869_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3890_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v_fst_3874_; lean_object* v_snd_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3889_; 
v_fst_3874_ = lean_ctor_get(v_a_3870_, 0);
v_snd_3875_ = lean_ctor_get(v_a_3870_, 1);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_a_3870_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3877_ = v_a_3870_;
v_isShared_3878_ = v_isSharedCheck_3889_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_snd_3875_);
lean_inc(v_fst_3874_);
lean_dec(v_a_3870_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3889_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
size_t v_sz_3879_; size_t v___x_3880_; lean_object* v_depPkgs_3881_; lean_object* v_ws_3882_; lean_object* v___x_3884_; 
v_sz_3879_ = lean_array_size(v___x_3864_);
v___x_3880_ = ((size_t)0ULL);
v_depPkgs_3881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_fst_3874_, v_sz_3879_, v___x_3880_, v___x_3864_);
v_ws_3882_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_3874_, v_pkg_3824_, v_depPkgs_3881_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v_ws_3882_);
v___x_3884_ = v___x_3877_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_ws_3882_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_snd_3875_);
v___x_3884_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3886_; 
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 0, v___x_3884_);
v___x_3886_ = v___x_3872_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3864_);
lean_dec(v_pkg_3824_);
return v___x_3869_;
}
}
else
{
size_t v___x_3891_; size_t v___x_3892_; lean_object* v___x_3893_; 
lean_dec_ref(v___x_3864_);
lean_dec_ref(v_ws_3818_);
v___x_3891_ = lean_usize_of_nat(v___x_3863_);
v___x_3892_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_3816_);
lean_inc(v_pkg_3824_);
v___x_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3824_, v_leanOpts_3816_, v_reconfigure_3817_, v_depConfigs_3825_, v___x_3891_, v___x_3892_, v_s_3865_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v_fst_3895_; lean_object* v_snd_3896_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v_fst_3895_ = lean_ctor_get(v_a_3894_, 0);
lean_inc(v_fst_3895_);
v_snd_3896_ = lean_ctor_get(v_a_3894_, 1);
lean_inc(v_snd_3896_);
lean_dec(v_a_3894_);
v_____x_3857_ = v_fst_3895_;
v___y_3858_ = v_snd_3896_;
v___y_3859_ = v___y_3821_;
goto v___jp_3856_;
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_pkg_3824_);
lean_dec_ref(v_leanOpts_3816_);
v_a_3897_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3893_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3893_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
else
{
uint8_t v___x_3905_; 
lean_inc_ref(v_packages_3823_);
v___x_3905_ = lean_nat_dec_lt(v___x_3866_, v___x_3863_);
if (v___x_3905_ == 0)
{
lean_dec_ref_known(v_s_3865_, 2);
v_ws_3828_ = v_ws_3818_;
v_packages_3829_ = v_packages_3823_;
v_depIdxs_3830_ = v___x_3864_;
v___y_3831_ = v___y_3820_;
v___y_3832_ = v___y_3821_;
goto v___jp_3827_;
}
else
{
size_t v___x_3906_; size_t v___x_3907_; lean_object* v___x_3908_; 
lean_dec_ref(v___x_3864_);
lean_dec_ref(v_packages_3823_);
lean_dec_ref(v_ws_3818_);
v___x_3906_ = lean_usize_of_nat(v___x_3863_);
v___x_3907_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_3816_);
lean_inc(v_pkg_3824_);
v___x_3908_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3824_, v_leanOpts_3816_, v_reconfigure_3817_, v_depConfigs_3825_, v___x_3906_, v___x_3907_, v_s_3865_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v_fst_3910_; lean_object* v_snd_3911_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v_fst_3910_ = lean_ctor_get(v_a_3909_, 0);
lean_inc(v_fst_3910_);
v_snd_3911_ = lean_ctor_get(v_a_3909_, 1);
lean_inc(v_snd_3911_);
lean_dec(v_a_3909_);
v_____x_3857_ = v_fst_3910_;
v___y_3858_ = v_snd_3911_;
v___y_3859_ = v___y_3821_;
goto v___jp_3856_;
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec(v_pkg_3824_);
lean_dec_ref(v_leanOpts_3816_);
v_a_3912_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3908_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3908_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
v___jp_3827_:
{
lean_object* v_stop_3833_; lean_object* v___x_3834_; 
v_stop_3833_ = lean_array_get_size(v_packages_3829_);
lean_dec_ref(v_packages_3829_);
v___x_3834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_stop_3833_, v_leanOpts_3816_, v_reconfigure_3817_, v_start_3826_, v_ws_3828_, v___y_3831_, v___y_3832_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3855_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3837_ = v___x_3834_;
v_isShared_3838_ = v_isSharedCheck_3855_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3834_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3855_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v_fst_3839_; lean_object* v_snd_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3854_; 
v_fst_3839_ = lean_ctor_get(v_a_3835_, 0);
v_snd_3840_ = lean_ctor_get(v_a_3835_, 1);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_a_3835_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3842_ = v_a_3835_;
v_isShared_3843_ = v_isSharedCheck_3854_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_snd_3840_);
lean_inc(v_fst_3839_);
lean_dec(v_a_3835_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3854_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
size_t v_sz_3844_; size_t v___x_3845_; lean_object* v_depPkgs_3846_; lean_object* v_ws_3847_; lean_object* v___x_3849_; 
v_sz_3844_ = lean_array_size(v_depIdxs_3830_);
v___x_3845_ = ((size_t)0ULL);
v_depPkgs_3846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_fst_3839_, v_sz_3844_, v___x_3845_, v_depIdxs_3830_);
v_ws_3847_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_3839_, v_pkg_3824_, v_depPkgs_3846_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v_ws_3847_);
v___x_3849_ = v___x_3842_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_ws_3847_);
lean_ctor_set(v_reuseFailAlloc_3853_, 1, v_snd_3840_);
v___x_3849_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v___x_3849_);
v___x_3851_ = v___x_3837_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
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
}
else
{
lean_dec_ref(v_depIdxs_3830_);
lean_dec(v_pkg_3824_);
return v___x_3834_;
}
}
v___jp_3856_:
{
lean_object* v_ws_3860_; lean_object* v_depIdxs_3861_; lean_object* v_packages_3862_; 
v_ws_3860_ = lean_ctor_get(v_____x_3857_, 0);
lean_inc_ref(v_ws_3860_);
v_depIdxs_3861_ = lean_ctor_get(v_____x_3857_, 1);
lean_inc_ref(v_depIdxs_3861_);
lean_dec_ref(v_____x_3857_);
v_packages_3862_ = lean_ctor_get(v_ws_3860_, 4);
lean_inc_ref(v_packages_3862_);
v_ws_3828_ = v_ws_3860_;
v_packages_3829_ = v_packages_3862_;
v_depIdxs_3830_ = v_depIdxs_3861_;
v___y_3831_ = v___y_3858_;
v___y_3832_ = v___y_3859_;
goto v___jp_3827_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(lean_object* v_upperBound_3920_, lean_object* v_leanOpts_3921_, uint8_t v_reconfigure_3922_, lean_object* v_a_3923_, lean_object* v_b_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_nat_dec_lt(v_a_3923_, v_upperBound_3920_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_dec(v_a_3923_);
lean_dec_ref(v_leanOpts_3921_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v_b_3924_);
lean_ctor_set(v___x_3929_, 1, v___y_3925_);
v___x_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
return v___x_3930_;
}
else
{
lean_object* v___x_3931_; 
lean_inc_ref(v_leanOpts_3921_);
v___x_3931_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_3921_, v_reconfigure_3922_, v_b_3924_, v_a_3923_, v___y_3925_, v___y_3926_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v_fst_3933_; lean_object* v_snd_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v_fst_3933_ = lean_ctor_get(v_a_3932_, 0);
lean_inc(v_fst_3933_);
v_snd_3934_ = lean_ctor_get(v_a_3932_, 1);
lean_inc(v_snd_3934_);
lean_dec(v_a_3932_);
v___x_3935_ = lean_unsigned_to_nat(1u);
v___x_3936_ = lean_nat_add(v_a_3923_, v___x_3935_);
lean_dec(v_a_3923_);
v_a_3923_ = v___x_3936_;
v_b_3924_ = v_fst_3933_;
v___y_3925_ = v_snd_3934_;
goto _start;
}
else
{
lean_dec(v_a_3923_);
lean_dec_ref(v_leanOpts_3921_);
return v___x_3931_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg___boxed(lean_object* v_upperBound_3938_, lean_object* v_leanOpts_3939_, lean_object* v_reconfigure_3940_, lean_object* v_a_3941_, lean_object* v_b_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
uint8_t v_reconfigure_boxed_3946_; lean_object* v_res_3947_; 
v_reconfigure_boxed_3946_ = lean_unbox(v_reconfigure_3940_);
v_res_3947_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_upperBound_3938_, v_leanOpts_3939_, v_reconfigure_boxed_3946_, v_a_3941_, v_b_3942_, v___y_3943_, v___y_3944_);
lean_dec_ref(v___y_3944_);
lean_dec(v_upperBound_3938_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg___boxed(lean_object* v_leanOpts_3948_, lean_object* v_reconfigure_3949_, lean_object* v_ws_3950_, lean_object* v_wsIdx_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
uint8_t v_reconfigure_boxed_3955_; lean_object* v_res_3956_; 
v_reconfigure_boxed_3955_ = lean_unbox(v_reconfigure_3949_);
v_res_3956_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_3948_, v_reconfigure_boxed_3955_, v_ws_3950_, v_wsIdx_3951_, v___y_3952_, v___y_3953_);
lean_dec_ref(v___y_3953_);
lean_dec(v_wsIdx_3951_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(lean_object* v_upperBound_3957_, lean_object* v_leanOpts_3958_, lean_object* v_a_3959_, lean_object* v_b_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
uint8_t v___x_3964_; 
v___x_3964_ = lean_nat_dec_lt(v_a_3959_, v_upperBound_3957_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_dec(v_a_3959_);
lean_dec_ref(v_leanOpts_3958_);
v___x_3965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3965_, 0, v_b_3960_);
lean_ctor_set(v___x_3965_, 1, v___y_3961_);
v___x_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
return v___x_3966_;
}
else
{
lean_object* v___x_3967_; 
lean_inc_ref(v_leanOpts_3958_);
v___x_3967_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_3958_, v___x_3964_, v_b_3960_, v_a_3959_, v___y_3961_, v___y_3962_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v_fst_3969_; lean_object* v_snd_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___x_3967_, 1);
v_fst_3969_ = lean_ctor_get(v_a_3968_, 0);
lean_inc(v_fst_3969_);
v_snd_3970_ = lean_ctor_get(v_a_3968_, 1);
lean_inc(v_snd_3970_);
lean_dec(v_a_3968_);
v___x_3971_ = lean_unsigned_to_nat(1u);
v___x_3972_ = lean_nat_add(v_a_3959_, v___x_3971_);
lean_dec(v_a_3959_);
v_a_3959_ = v___x_3972_;
v_b_3960_ = v_fst_3969_;
v___y_3961_ = v_snd_3970_;
goto _start;
}
else
{
lean_dec(v_a_3959_);
lean_dec_ref(v_leanOpts_3958_);
return v___x_3967_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg___boxed(lean_object* v_upperBound_3974_, lean_object* v_leanOpts_3975_, lean_object* v_a_3976_, lean_object* v_b_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_upperBound_3974_, v_leanOpts_3975_, v_a_3976_, v_b_3977_, v___y_3978_, v___y_3979_);
lean_dec_ref(v___y_3979_);
lean_dec(v_upperBound_3974_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(lean_object* v_n_3982_, lean_object* v_f_3983_, lean_object* v_xs_3984_, lean_object* v_k_3985_, lean_object* v_acc_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
uint8_t v___x_3990_; 
v___x_3990_ = lean_nat_dec_lt(v_k_3985_, v_n_3982_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
lean_dec(v_k_3985_);
lean_dec_ref(v_f_3983_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_acc_3986_);
lean_ctor_set(v___x_3991_, 1, v___y_3987_);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = lean_array_fget_borrowed(v_xs_3984_, v_k_3985_);
lean_inc_ref(v_f_3983_);
lean_inc_ref(v___y_3988_);
lean_inc(v___x_3993_);
v___x_3994_ = lean_apply_4(v_f_3983_, v___x_3993_, v___y_3987_, v___y_3988_, lean_box(0));
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v_fst_3996_; lean_object* v_snd_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3994_, 1);
v_fst_3996_ = lean_ctor_get(v_a_3995_, 0);
lean_inc(v_fst_3996_);
v_snd_3997_ = lean_ctor_get(v_a_3995_, 1);
lean_inc(v_snd_3997_);
lean_dec(v_a_3995_);
v___x_3998_ = lean_unsigned_to_nat(1u);
v___x_3999_ = lean_nat_add(v_k_3985_, v___x_3998_);
lean_dec(v_k_3985_);
v___x_4000_ = lean_array_push(v_acc_3986_, v_fst_3996_);
v_k_3985_ = v___x_3999_;
v_acc_3986_ = v___x_4000_;
v___y_3987_ = v_snd_3997_;
goto _start;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_acc_3986_);
lean_dec(v_k_3985_);
lean_dec_ref(v_f_3983_);
v_a_4002_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3994_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3994_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg___boxed(lean_object* v_n_4010_, lean_object* v_f_4011_, lean_object* v_xs_4012_, lean_object* v_k_4013_, lean_object* v_acc_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4010_, v_f_4011_, v_xs_4012_, v_k_4013_, v_acc_4014_, v___y_4015_, v___y_4016_);
lean_dec_ref(v___y_4016_);
lean_dec_ref(v_xs_4012_);
lean_dec(v_n_4010_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(lean_object* v_upperBound_4019_, lean_object* v_fst_4020_, lean_object* v___x_4021_, lean_object* v_leanOpts_4022_, lean_object* v_a_4023_, lean_object* v_b_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
uint8_t v___x_4031_; 
v___x_4031_ = lean_nat_dec_lt(v_a_4023_, v_upperBound_4019_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_dec(v_a_4023_);
lean_dec_ref(v_leanOpts_4022_);
v___x_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4032_, 0, v_b_4024_);
lean_ctor_set(v___x_4032_, 1, v___y_4025_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_array_fget_borrowed(v_fst_4020_, v_a_4023_);
lean_inc(v___x_4034_);
v___x_4035_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v___x_4034_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4110_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4110_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4110_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v_snd_4040_; lean_object* v___x_4041_; lean_object* v_opts_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v_snd_4040_ = lean_ctor_get(v_a_4036_, 1);
lean_inc(v_snd_4040_);
lean_dec(v_a_4036_);
v___x_4041_ = lean_array_fget_borrowed(v___x_4021_, v_a_4023_);
v_opts_4042_ = lean_ctor_get(v___x_4041_, 4);
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4022_);
lean_inc(v_opts_4042_);
lean_inc(v___x_4034_);
v___x_4045_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_b_4024_, v___x_4034_, v_opts_4042_, v_leanOpts_4022_, v___x_4031_, v___x_4044_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v_a_4047_; lean_object* v_snd_4049_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
lean_del_object(v___x_4038_);
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4046_);
v_a_4047_ = lean_ctor_get(v___x_4045_, 1);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___x_4045_, 2);
v___x_4053_ = lean_array_get_size(v_a_4047_);
v___x_4054_ = lean_nat_dec_lt(v___x_4043_, v___x_4053_);
if (v___x_4054_ == 0)
{
lean_dec(v_a_4047_);
v_snd_4049_ = v_snd_4040_;
goto v___jp_4048_;
}
else
{
lean_object* v___x_4055_; uint8_t v___x_4056_; 
v___x_4055_ = lean_box(0);
v___x_4056_ = lean_nat_dec_le(v___x_4053_, v___x_4053_);
if (v___x_4056_ == 0)
{
if (v___x_4054_ == 0)
{
lean_dec(v_a_4047_);
v_snd_4049_ = v_snd_4040_;
goto v___jp_4048_;
}
else
{
size_t v___x_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
v___x_4057_ = ((size_t)0ULL);
v___x_4058_ = lean_usize_of_nat(v___x_4053_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4047_, v___x_4057_, v___x_4058_, v___x_4055_, v___y_4026_);
lean_dec(v_a_4047_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_dec_ref_known(v___x_4059_, 1);
v_snd_4049_ = v_snd_4040_;
goto v___jp_4048_;
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec(v_a_4046_);
lean_dec(v_snd_4040_);
lean_dec(v_a_4023_);
lean_dec_ref(v_leanOpts_4022_);
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
else
{
size_t v___x_4068_; size_t v___x_4069_; lean_object* v___x_4070_; 
v___x_4068_ = ((size_t)0ULL);
v___x_4069_ = lean_usize_of_nat(v___x_4053_);
v___x_4070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4047_, v___x_4068_, v___x_4069_, v___x_4055_, v___y_4026_);
lean_dec(v_a_4047_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_dec_ref_known(v___x_4070_, 1);
v_snd_4049_ = v_snd_4040_;
goto v___jp_4048_;
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_a_4046_);
lean_dec(v_snd_4040_);
lean_dec(v_a_4023_);
lean_dec_ref(v_leanOpts_4022_);
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4070_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4070_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
v___jp_4048_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = lean_unsigned_to_nat(1u);
v___x_4051_ = lean_nat_add(v_a_4023_, v___x_4050_);
lean_dec(v_a_4023_);
v_a_4023_ = v___x_4051_;
v_b_4024_ = v_a_4046_;
v___y_4025_ = v_snd_4049_;
goto _start;
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
lean_dec(v_snd_4040_);
lean_dec(v_a_4023_);
lean_dec_ref(v_leanOpts_4022_);
v_a_4079_ = lean_ctor_get(v___x_4045_, 1);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___x_4045_, 2);
v___x_4080_ = lean_array_get_size(v_a_4079_);
v___x_4081_ = lean_nat_dec_lt(v___x_4043_, v___x_4080_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; lean_object* v___x_4084_; 
lean_dec(v_a_4079_);
v___x_4082_ = lean_box(0);
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 1);
lean_ctor_set(v___x_4038_, 0, v___x_4082_);
v___x_4084_ = v___x_4038_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
else
{
lean_object* v___x_4086_; uint8_t v___x_4087_; 
lean_del_object(v___x_4038_);
v___x_4086_ = lean_box(0);
v___x_4087_ = lean_nat_dec_le(v___x_4080_, v___x_4080_);
if (v___x_4087_ == 0)
{
if (v___x_4081_ == 0)
{
lean_dec(v_a_4079_);
goto v___jp_4028_;
}
else
{
size_t v___x_4088_; size_t v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = ((size_t)0ULL);
v___x_4089_ = lean_usize_of_nat(v___x_4080_);
v___x_4090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4079_, v___x_4088_, v___x_4089_, v___x_4086_, v___y_4026_);
lean_dec(v_a_4079_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_dec_ref_known(v___x_4090_, 1);
goto v___jp_4028_;
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
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
else
{
size_t v___x_4099_; size_t v___x_4100_; lean_object* v___x_4101_; 
v___x_4099_ = ((size_t)0ULL);
v___x_4100_ = lean_usize_of_nat(v___x_4080_);
v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4079_, v___x_4099_, v___x_4100_, v___x_4086_, v___y_4026_);
lean_dec(v_a_4079_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_dec_ref_known(v___x_4101_, 1);
goto v___jp_4028_;
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_4101_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4101_);
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
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v_b_4024_);
lean_dec(v_a_4023_);
lean_dec_ref(v_leanOpts_4022_);
v_a_4111_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4035_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4035_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
v___jp_4028_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = lean_box(0);
v___x_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg___boxed(lean_object* v_upperBound_4119_, lean_object* v_fst_4120_, lean_object* v___x_4121_, lean_object* v_leanOpts_4122_, lean_object* v_a_4123_, lean_object* v_b_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4119_, v_fst_4120_, v___x_4121_, v_leanOpts_4122_, v_a_4123_, v_b_4124_, v___y_4125_, v___y_4126_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v___x_4121_);
lean_dec_ref(v_fst_4120_);
lean_dec(v_upperBound_4119_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4131_, lean_object* v_toUpdate_4132_, lean_object* v_leanOpts_4133_, uint8_t v_updateToolchain_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_box(1);
v___x_4138_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4135_, v_ws_4131_, v_toUpdate_4132_, v___x_4137_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
if (v_updateToolchain_4134_ == 0)
{
lean_object* v_snd_4140_; lean_object* v_packages_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v_wsIdx_4144_; uint8_t v___x_4145_; lean_object* v___x_4146_; 
v_snd_4140_ = lean_ctor_get(v_a_4139_, 1);
lean_inc(v_snd_4140_);
lean_dec(v_a_4139_);
v_packages_4141_ = lean_ctor_get(v_ws_4131_, 4);
v___x_4142_ = lean_unsigned_to_nat(0u);
v___x_4143_ = lean_array_fget_borrowed(v_packages_4141_, v___x_4142_);
v_wsIdx_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_wsIdx_4144_);
v___x_4145_ = 1;
v___x_4146_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4133_, v___x_4145_, v_ws_4131_, v_wsIdx_4144_, v_snd_4140_, v_a_4135_);
lean_dec(v_wsIdx_4144_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4163_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4149_ = v___x_4146_;
v_isShared_4150_ = v_isSharedCheck_4163_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4146_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4163_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v_fst_4151_; lean_object* v_snd_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4162_; 
v_fst_4151_ = lean_ctor_get(v_a_4147_, 0);
v_snd_4152_ = lean_ctor_get(v_a_4147_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_a_4147_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4154_ = v_a_4147_;
v_isShared_4155_ = v_isSharedCheck_4162_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_snd_4152_);
lean_inc(v_fst_4151_);
lean_dec(v_a_4147_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4162_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_fst_4151_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_snd_4152_);
v___x_4157_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4159_; 
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4157_);
v___x_4159_ = v___x_4149_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
v_a_4164_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4146_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4146_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
lean_object* v_snd_4172_; lean_object* v_packages_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v_depConfigs_4176_; lean_object* v___x_4177_; lean_object* v___f_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v_snd_4172_ = lean_ctor_get(v_a_4139_, 1);
lean_inc(v_snd_4172_);
lean_dec(v_a_4139_);
v_packages_4173_ = lean_ctor_get(v_ws_4131_, 4);
lean_inc_ref(v_packages_4173_);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = lean_array_fget_borrowed(v_packages_4173_, v___x_4174_);
v_depConfigs_4176_ = lean_ctor_get(v___x_4175_, 12);
v___x_4177_ = lean_box(v_updateToolchain_4134_);
lean_inc_ref(v_ws_4131_);
lean_inc(v___x_4175_);
v___f_4178_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4178_, 0, v___x_4175_);
lean_closure_set(v___f_4178_, 1, v___x_4177_);
lean_closure_set(v___f_4178_, 2, v_ws_4131_);
v___x_4179_ = lean_array_get_size(v_depConfigs_4176_);
lean_inc_ref(v_depConfigs_4176_);
v___x_4180_ = l_Array_reverse___redArg(v_depConfigs_4176_);
v___x_4181_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4182_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4179_, v___f_4178_, v___x_4180_, v___x_4174_, v___x_4181_, v_snd_4172_, v_a_4135_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v_fst_4184_; lean_object* v_snd_4185_; lean_object* v___x_4186_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4182_, 1);
v_fst_4184_ = lean_ctor_get(v_a_4183_, 0);
lean_inc(v_fst_4184_);
v_snd_4185_ = lean_ctor_get(v_a_4183_, 1);
lean_inc(v_snd_4185_);
lean_dec(v_a_4183_);
lean_inc_ref(v_ws_4131_);
v___x_4186_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4135_, v_ws_4131_, v_fst_4184_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v___x_4187_; 
lean_dec_ref_known(v___x_4186_, 1);
lean_inc_ref(v_leanOpts_4133_);
v___x_4187_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4179_, v_fst_4184_, v___x_4180_, v_leanOpts_4133_, v___x_4174_, v_ws_4131_, v_snd_4185_, v_a_4135_);
lean_dec_ref(v___x_4180_);
lean_dec(v_fst_4184_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v_fst_4189_; lean_object* v_snd_4190_; lean_object* v_packages_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
v_fst_4189_ = lean_ctor_get(v_a_4188_, 0);
lean_inc(v_fst_4189_);
v_snd_4190_ = lean_ctor_get(v_a_4188_, 1);
lean_inc(v_snd_4190_);
lean_dec(v_a_4188_);
v_packages_4191_ = lean_ctor_get(v_fst_4189_, 4);
v___x_4192_ = lean_array_get_size(v_packages_4173_);
lean_dec_ref(v_packages_4173_);
v___x_4193_ = lean_array_get_size(v_packages_4191_);
v___x_4194_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4193_, v_leanOpts_4133_, v___x_4192_, v_fst_4189_, v_snd_4190_, v_a_4135_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4216_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4216_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4216_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v_fst_4199_; lean_object* v_snd_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4215_; 
v_fst_4199_ = lean_ctor_get(v_a_4195_, 0);
v_snd_4200_ = lean_ctor_get(v_a_4195_, 1);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_a_4195_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4202_ = v_a_4195_;
v_isShared_4203_ = v_isSharedCheck_4215_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_snd_4200_);
lean_inc(v_fst_4199_);
lean_dec(v_a_4195_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4215_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v_packages_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4210_; 
v_packages_4204_ = lean_ctor_get(v_fst_4199_, 4);
v___x_4205_ = lean_array_fget(v_packages_4204_, v___x_4174_);
lean_inc_ref(v_packages_4204_);
v___x_4206_ = l_Array_toSubarray___redArg(v_packages_4204_, v___x_4192_, v___x_4193_);
v___x_4207_ = l_Subarray_copy___redArg(v___x_4206_);
v___x_4208_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_4199_, v___x_4205_, v___x_4207_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4208_);
v___x_4210_ = v___x_4202_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4208_);
lean_ctor_set(v_reuseFailAlloc_4214_, 1, v_snd_4200_);
v___x_4210_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
lean_object* v___x_4212_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4210_);
v___x_4212_ = v___x_4197_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
v_a_4217_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4194_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4194_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec_ref(v_packages_4173_);
lean_dec_ref(v_leanOpts_4133_);
v_a_4225_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4187_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4187_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v_snd_4185_);
lean_dec(v_fst_4184_);
lean_dec_ref(v___x_4180_);
lean_dec_ref(v_packages_4173_);
lean_dec_ref(v_leanOpts_4133_);
lean_dec_ref(v_ws_4131_);
v_a_4233_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4186_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4186_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v___x_4180_);
lean_dec_ref(v_packages_4173_);
lean_dec_ref(v_leanOpts_4133_);
lean_dec_ref(v_ws_4131_);
v_a_4241_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4182_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4182_);
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
lean_dec_ref(v_leanOpts_4133_);
lean_dec_ref(v_ws_4131_);
v_a_4249_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4138_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4138_);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_leanOpts_4265_, uint8_t v_reconfigure_4266_, lean_object* v_ws_4267_, lean_object* v_wsIdx_4268_, lean_object* v_h_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4265_, v_reconfigure_4266_, v_ws_4267_, v_wsIdx_4268_, v___y_4270_, v___y_4271_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_leanOpts_4274_, lean_object* v_reconfigure_4275_, lean_object* v_ws_4276_, lean_object* v_wsIdx_4277_, lean_object* v_h_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
uint8_t v_reconfigure_boxed_4282_; lean_object* v_res_4283_; 
v_reconfigure_boxed_4282_ = lean_unbox(v_reconfigure_4275_);
v_res_4283_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_leanOpts_4274_, v_reconfigure_boxed_4282_, v_ws_4276_, v_wsIdx_4277_, v_h_4278_, v___y_4279_, v___y_4280_);
lean_dec_ref(v___y_4280_);
lean_dec(v_wsIdx_4277_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_00_u03b1_4284_, lean_object* v_00_u03b2_4285_, lean_object* v_n_4286_, lean_object* v_f_4287_, lean_object* v_xs_4288_, lean_object* v_k_4289_, lean_object* v_h_4290_, lean_object* v_acc_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v_n_4286_, v_f_4287_, v_xs_4288_, v_k_4289_, v_acc_4291_, v___y_4292_, v___y_4293_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_00_u03b1_4296_, lean_object* v_00_u03b2_4297_, lean_object* v_n_4298_, lean_object* v_f_4299_, lean_object* v_xs_4300_, lean_object* v_k_4301_, lean_object* v_h_4302_, lean_object* v_acc_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_00_u03b1_4296_, v_00_u03b2_4297_, v_n_4298_, v_f_4299_, v_xs_4300_, v_k_4301_, v_h_4302_, v_acc_4303_, v___y_4304_, v___y_4305_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v_xs_4300_);
lean_dec(v_n_4298_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_upperBound_4308_, lean_object* v_leanOpts_4309_, lean_object* v_inst_4310_, lean_object* v_R_4311_, lean_object* v_a_4312_, lean_object* v_b_4313_, lean_object* v_c_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v_upperBound_4308_, v_leanOpts_4309_, v_a_4312_, v_b_4313_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object* v_upperBound_4319_, lean_object* v_leanOpts_4320_, lean_object* v_inst_4321_, lean_object* v_R_4322_, lean_object* v_a_4323_, lean_object* v_b_4324_, lean_object* v_c_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_upperBound_4319_, v_leanOpts_4320_, v_inst_4321_, v_R_4322_, v_a_4323_, v_b_4324_, v_c_4325_, v___y_4326_, v___y_4327_);
lean_dec_ref(v___y_4327_);
lean_dec(v_upperBound_4319_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_upperBound_4330_, lean_object* v_fst_4331_, lean_object* v___x_4332_, lean_object* v_leanOpts_4333_, lean_object* v_inst_4334_, lean_object* v_R_4335_, lean_object* v_a_4336_, lean_object* v_b_4337_, lean_object* v_c_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v_upperBound_4330_, v_fst_4331_, v___x_4332_, v_leanOpts_4333_, v_a_4336_, v_b_4337_, v___y_4339_, v___y_4340_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_upperBound_4343_, lean_object* v_fst_4344_, lean_object* v___x_4345_, lean_object* v_leanOpts_4346_, lean_object* v_inst_4347_, lean_object* v_R_4348_, lean_object* v_a_4349_, lean_object* v_b_4350_, lean_object* v_c_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_upperBound_4343_, v_fst_4344_, v___x_4345_, v_leanOpts_4346_, v_inst_4347_, v_R_4348_, v_a_4349_, v_b_4350_, v_c_4351_, v___y_4352_, v___y_4353_);
lean_dec_ref(v___y_4353_);
lean_dec_ref(v___x_4345_);
lean_dec_ref(v_fst_4344_);
lean_dec(v_upperBound_4343_);
return v_res_4355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object* v_upperBound_4356_, lean_object* v_leanOpts_4357_, uint8_t v_reconfigure_4358_, lean_object* v_inst_4359_, lean_object* v_R_4360_, lean_object* v_a_4361_, lean_object* v_b_4362_, lean_object* v_c_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___redArg(v_upperBound_4356_, v_leanOpts_4357_, v_reconfigure_4358_, v_a_4361_, v_b_4362_, v___y_4364_, v___y_4365_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___boxed(lean_object* v_upperBound_4368_, lean_object* v_leanOpts_4369_, lean_object* v_reconfigure_4370_, lean_object* v_inst_4371_, lean_object* v_R_4372_, lean_object* v_a_4373_, lean_object* v_b_4374_, lean_object* v_c_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
uint8_t v_reconfigure_boxed_4379_; lean_object* v_res_4380_; 
v_reconfigure_boxed_4379_ = lean_unbox(v_reconfigure_4370_);
v_res_4380_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(v_upperBound_4368_, v_leanOpts_4369_, v_reconfigure_boxed_4379_, v_inst_4371_, v_R_4372_, v_a_4373_, v_b_4374_, v_c_4375_, v___y_4376_, v___y_4377_);
lean_dec_ref(v___y_4377_);
lean_dec(v_upperBound_4368_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(lean_object* v_start_4381_, lean_object* v_pkg_4382_, lean_object* v_leanOpts_4383_, uint8_t v_reconfigure_4384_, lean_object* v_as_4385_, size_t v_i_4386_, size_t v_stop_4387_, lean_object* v_b_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_4382_, v_leanOpts_4383_, v_reconfigure_4384_, v_as_4385_, v_i_4386_, v_stop_4387_, v_b_4388_, v___y_4389_, v___y_4390_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___boxed(lean_object* v_start_4393_, lean_object* v_pkg_4394_, lean_object* v_leanOpts_4395_, lean_object* v_reconfigure_4396_, lean_object* v_as_4397_, lean_object* v_i_4398_, lean_object* v_stop_4399_, lean_object* v_b_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
uint8_t v_reconfigure_boxed_4404_; size_t v_i_boxed_4405_; size_t v_stop_boxed_4406_; lean_object* v_res_4407_; 
v_reconfigure_boxed_4404_ = lean_unbox(v_reconfigure_4396_);
v_i_boxed_4405_ = lean_unbox_usize(v_i_4398_);
lean_dec(v_i_4398_);
v_stop_boxed_4406_ = lean_unbox_usize(v_stop_4399_);
lean_dec(v_stop_4399_);
v_res_4407_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(v_start_4393_, v_pkg_4394_, v_leanOpts_4395_, v_reconfigure_boxed_4404_, v_as_4397_, v_i_boxed_4405_, v_stop_boxed_4406_, v_b_4400_, v___y_4401_, v___y_4402_);
lean_dec_ref(v___y_4402_);
lean_dec_ref(v_as_4397_);
lean_dec(v_start_4393_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_4408_, lean_object* v_msg_4409_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___redArg(v_msg_4409_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8(lean_object* v_00_u03b2_4411_, lean_object* v_k_4412_, lean_object* v_v_4413_, lean_object* v_t_4414_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___redArg(v_k_4412_, v_v_4413_, v_t_4414_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9(lean_object* v_init_4416_, lean_object* v_t_4417_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__9_spec__12(v_init_4416_, v_t_4417_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4419_, lean_object* v_as_4420_, size_t v_i_4421_, size_t v_stop_4422_, lean_object* v_b_4423_){
_start:
{
lean_object* v___y_4425_; uint8_t v___x_4429_; 
v___x_4429_ = lean_usize_dec_eq(v_i_4421_, v_stop_4422_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; lean_object* v_baseName_4431_; lean_object* v_relConfigFile_4432_; lean_object* v_relManifestFile_4433_; lean_object* v___x_4434_; 
v___x_4430_ = lean_array_uget_borrowed(v_as_4420_, v_i_4421_);
v_baseName_4431_ = lean_ctor_get(v___x_4430_, 1);
v_relConfigFile_4432_ = lean_ctor_get(v___x_4430_, 8);
v_relManifestFile_4433_ = lean_ctor_get(v___x_4430_, 9);
v___x_4434_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4419_, v_baseName_4431_);
if (lean_obj_tag(v___x_4434_) == 0)
{
v___y_4425_ = v_b_4423_;
goto v___jp_4424_;
}
else
{
lean_object* v_val_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4456_; 
v_val_4435_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4437_ = v___x_4434_;
v_isShared_4438_ = v_isSharedCheck_4456_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_val_4435_);
lean_dec(v___x_4434_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4456_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v_name_4439_; lean_object* v_scope_4440_; uint8_t v_inherited_4441_; lean_object* v_src_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4453_; 
v_name_4439_ = lean_ctor_get(v_val_4435_, 0);
v_scope_4440_ = lean_ctor_get(v_val_4435_, 1);
v_inherited_4441_ = lean_ctor_get_uint8(v_val_4435_, sizeof(void*)*5);
v_src_4442_ = lean_ctor_get(v_val_4435_, 4);
v_isSharedCheck_4453_ = !lean_is_exclusive(v_val_4435_);
if (v_isSharedCheck_4453_ == 0)
{
lean_object* v_unused_4454_; lean_object* v_unused_4455_; 
v_unused_4454_ = lean_ctor_get(v_val_4435_, 3);
lean_dec(v_unused_4454_);
v_unused_4455_ = lean_ctor_get(v_val_4435_, 2);
lean_dec(v_unused_4455_);
v___x_4444_ = v_val_4435_;
v_isShared_4445_ = v_isSharedCheck_4453_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_src_4442_);
lean_inc(v_scope_4440_);
lean_inc(v_name_4439_);
lean_dec(v_val_4435_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4453_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
lean_inc_ref(v_relManifestFile_4433_);
if (v_isShared_4438_ == 0)
{
lean_ctor_set(v___x_4437_, 0, v_relManifestFile_4433_);
v___x_4447_ = v___x_4437_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_relManifestFile_4433_);
v___x_4447_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
lean_object* v___x_4449_; 
lean_inc_ref(v_relConfigFile_4432_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 3, v___x_4447_);
lean_ctor_set(v___x_4444_, 2, v_relConfigFile_4432_);
v___x_4449_ = v___x_4444_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_name_4439_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v_scope_4440_);
lean_ctor_set(v_reuseFailAlloc_4451_, 2, v_relConfigFile_4432_);
lean_ctor_set(v_reuseFailAlloc_4451_, 3, v___x_4447_);
lean_ctor_set(v_reuseFailAlloc_4451_, 4, v_src_4442_);
lean_ctor_set_uint8(v_reuseFailAlloc_4451_, sizeof(void*)*5, v_inherited_4441_);
v___x_4449_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
lean_object* v___x_4450_; 
v___x_4450_ = lean_array_push(v_b_4423_, v___x_4449_);
v___y_4425_ = v___x_4450_;
goto v___jp_4424_;
}
}
}
}
}
}
else
{
return v_b_4423_;
}
v___jp_4424_:
{
size_t v___x_4426_; size_t v___x_4427_; 
v___x_4426_ = ((size_t)1ULL);
v___x_4427_ = lean_usize_add(v_i_4421_, v___x_4426_);
v_i_4421_ = v___x_4427_;
v_b_4423_ = v___y_4425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4457_, lean_object* v_as_4458_, lean_object* v_i_4459_, lean_object* v_stop_4460_, lean_object* v_b_4461_){
_start:
{
size_t v_i_boxed_4462_; size_t v_stop_boxed_4463_; lean_object* v_res_4464_; 
v_i_boxed_4462_ = lean_unbox_usize(v_i_4459_);
lean_dec(v_i_4459_);
v_stop_boxed_4463_ = lean_unbox_usize(v_stop_4460_);
lean_dec(v_stop_4460_);
v_res_4464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4457_, v_as_4458_, v_i_boxed_4462_, v_stop_boxed_4463_, v_b_4461_);
lean_dec_ref(v_as_4458_);
lean_dec(v_entries_4457_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4465_, lean_object* v_entries_4466_){
_start:
{
lean_object* v_packages_4468_; lean_object* v___y_4470_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; uint8_t v___x_4488_; 
v_packages_4468_ = lean_ctor_get(v_ws_4465_, 4);
v___x_4485_ = lean_unsigned_to_nat(0u);
v___x_4486_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4487_ = lean_array_get_size(v_packages_4468_);
v___x_4488_ = lean_nat_dec_lt(v___x_4485_, v___x_4487_);
if (v___x_4488_ == 0)
{
v___y_4470_ = v___x_4486_;
goto v___jp_4469_;
}
else
{
uint8_t v___x_4489_; 
v___x_4489_ = lean_nat_dec_le(v___x_4487_, v___x_4487_);
if (v___x_4489_ == 0)
{
if (v___x_4488_ == 0)
{
v___y_4470_ = v___x_4486_;
goto v___jp_4469_;
}
else
{
size_t v___x_4490_; size_t v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = ((size_t)0ULL);
v___x_4491_ = lean_usize_of_nat(v___x_4487_);
v___x_4492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4466_, v_packages_4468_, v___x_4490_, v___x_4491_, v___x_4486_);
v___y_4470_ = v___x_4492_;
goto v___jp_4469_;
}
}
else
{
size_t v___x_4493_; size_t v___x_4494_; lean_object* v___x_4495_; 
v___x_4493_ = ((size_t)0ULL);
v___x_4494_ = lean_usize_of_nat(v___x_4487_);
v___x_4495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4466_, v_packages_4468_, v___x_4493_, v___x_4494_, v___x_4486_);
v___y_4470_ = v___x_4495_;
goto v___jp_4469_;
}
}
v___jp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v_config_4473_; lean_object* v_baseName_4474_; lean_object* v_dir_4475_; lean_object* v_relManifestFile_4476_; lean_object* v_toWorkspaceConfig_4477_; uint8_t v_fixedToolchain_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v_manifest_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4471_ = lean_unsigned_to_nat(0u);
v___x_4472_ = lean_array_fget_borrowed(v_packages_4468_, v___x_4471_);
v_config_4473_ = lean_ctor_get(v___x_4472_, 6);
v_baseName_4474_ = lean_ctor_get(v___x_4472_, 1);
v_dir_4475_ = lean_ctor_get(v___x_4472_, 4);
v_relManifestFile_4476_ = lean_ctor_get(v___x_4472_, 9);
v_toWorkspaceConfig_4477_ = lean_ctor_get(v_config_4473_, 0);
v_fixedToolchain_4478_ = lean_ctor_get_uint8(v_config_4473_, sizeof(void*)*27 + 6);
v___x_4479_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_toWorkspaceConfig_4477_);
v___x_4480_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4477_);
v___x_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
lean_inc(v_baseName_4474_);
v_manifest_4482_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4482_, 0, v_baseName_4474_);
lean_ctor_set(v_manifest_4482_, 1, v___x_4479_);
lean_ctor_set(v_manifest_4482_, 2, v___x_4481_);
lean_ctor_set(v_manifest_4482_, 3, v___y_4470_);
lean_ctor_set_uint8(v_manifest_4482_, sizeof(void*)*4, v_fixedToolchain_4478_);
lean_inc_ref(v_relManifestFile_4476_);
lean_inc_ref(v_dir_4475_);
v___x_4483_ = l_Lake_joinRelative(v_dir_4475_, v_relManifestFile_4476_);
v___x_4484_ = l_Lake_Manifest_save(v_manifest_4482_, v___x_4483_);
lean_dec_ref(v___x_4483_);
return v___x_4484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4496_, lean_object* v_entries_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4496_, v_entries_4497_);
lean_dec(v_entries_4497_);
lean_dec_ref(v_ws_4496_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4500_, lean_object* v_as_4501_, size_t v_i_4502_, size_t v_stop_4503_, lean_object* v_b_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v_a_4509_; lean_object* v___y_4514_; uint8_t v___x_4519_; 
v___x_4519_ = lean_usize_dec_eq(v_i_4502_, v_stop_4503_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_9317__overap_4522_; lean_object* v___x_4523_; 
v___x_4520_ = lean_unsigned_to_nat(0u);
v___x_4521_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_9317__overap_4522_ = lean_array_uget_borrowed(v_as_4501_, v_i_4502_);
lean_inc(v___x_9317__overap_4522_);
lean_inc(v___y_4505_);
lean_inc_ref(v_pkg_4500_);
v___x_4523_ = lean_apply_4(v___x_9317__overap_4522_, v_pkg_4500_, v___y_4505_, v___x_4521_, lean_box(0));
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; lean_object* v_a_4525_; lean_object* v___x_4526_; uint8_t v___x_4527_; 
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4524_);
v_a_4525_ = lean_ctor_get(v___x_4523_, 1);
lean_inc(v_a_4525_);
lean_dec_ref_known(v___x_4523_, 2);
v___x_4526_ = lean_array_get_size(v_a_4525_);
v___x_4527_ = lean_nat_dec_lt(v___x_4520_, v___x_4526_);
if (v___x_4527_ == 0)
{
lean_dec(v_a_4525_);
v_a_4509_ = v_a_4524_;
goto v___jp_4508_;
}
else
{
lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4528_ = lean_box(0);
v___x_4529_ = lean_nat_dec_le(v___x_4526_, v___x_4526_);
if (v___x_4529_ == 0)
{
if (v___x_4527_ == 0)
{
lean_dec(v_a_4525_);
v_a_4509_ = v_a_4524_;
goto v___jp_4508_;
}
else
{
size_t v___x_4530_; size_t v___x_4531_; lean_object* v___x_4532_; 
v___x_4530_ = ((size_t)0ULL);
v___x_4531_ = lean_usize_of_nat(v___x_4526_);
v___x_4532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4525_, v___x_4530_, v___x_4531_, v___x_4528_, v___y_4506_);
lean_dec(v_a_4525_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_dec_ref_known(v___x_4532_, 1);
v_a_4509_ = v_a_4524_;
goto v___jp_4508_;
}
else
{
lean_dec(v_a_4524_);
v___y_4514_ = v___x_4532_;
goto v___jp_4513_;
}
}
}
else
{
size_t v___x_4533_; size_t v___x_4534_; lean_object* v___x_4535_; 
v___x_4533_ = ((size_t)0ULL);
v___x_4534_ = lean_usize_of_nat(v___x_4526_);
v___x_4535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4525_, v___x_4533_, v___x_4534_, v___x_4528_, v___y_4506_);
lean_dec(v_a_4525_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_dec_ref_known(v___x_4535_, 1);
v_a_4509_ = v_a_4524_;
goto v___jp_4508_;
}
else
{
lean_dec(v_a_4524_);
v___y_4514_ = v___x_4535_;
goto v___jp_4513_;
}
}
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4537_; uint8_t v___x_4538_; 
v_a_4536_ = lean_ctor_get(v___x_4523_, 1);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4523_, 2);
v___x_4537_ = lean_array_get_size(v_a_4536_);
v___x_4538_ = lean_nat_dec_lt(v___x_4520_, v___x_4537_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
lean_dec(v_a_4536_);
lean_dec_ref(v_pkg_4500_);
v___x_4539_ = lean_box(0);
v___x_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4539_);
return v___x_4540_;
}
else
{
lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_nat_dec_le(v___x_4537_, v___x_4537_);
if (v___x_4542_ == 0)
{
if (v___x_4538_ == 0)
{
lean_dec(v_a_4536_);
lean_dec_ref(v_pkg_4500_);
goto v___jp_4516_;
}
else
{
size_t v___x_4543_; size_t v___x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = ((size_t)0ULL);
v___x_4544_ = lean_usize_of_nat(v___x_4537_);
v___x_4545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4536_, v___x_4543_, v___x_4544_, v___x_4541_, v___y_4506_);
lean_dec(v_a_4536_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_dec_ref_known(v___x_4545_, 1);
lean_dec_ref(v_pkg_4500_);
goto v___jp_4516_;
}
else
{
v___y_4514_ = v___x_4545_;
goto v___jp_4513_;
}
}
}
else
{
size_t v___x_4546_; size_t v___x_4547_; lean_object* v___x_4548_; 
v___x_4546_ = ((size_t)0ULL);
v___x_4547_ = lean_usize_of_nat(v___x_4537_);
v___x_4548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4536_, v___x_4546_, v___x_4547_, v___x_4541_, v___y_4506_);
lean_dec(v_a_4536_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_dec_ref_known(v___x_4548_, 1);
lean_dec_ref(v_pkg_4500_);
goto v___jp_4516_;
}
else
{
v___y_4514_ = v___x_4548_;
goto v___jp_4513_;
}
}
}
}
}
else
{
lean_object* v___x_4549_; 
lean_dec_ref(v_pkg_4500_);
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v_b_4504_);
return v___x_4549_;
}
v___jp_4508_:
{
size_t v___x_4510_; size_t v___x_4511_; 
v___x_4510_ = ((size_t)1ULL);
v___x_4511_ = lean_usize_add(v_i_4502_, v___x_4510_);
v_i_4502_ = v___x_4511_;
v_b_4504_ = v_a_4509_;
goto _start;
}
v___jp_4513_:
{
if (lean_obj_tag(v___y_4514_) == 0)
{
lean_object* v_a_4515_; 
v_a_4515_ = lean_ctor_get(v___y_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___y_4514_, 1);
v_a_4509_ = v_a_4515_;
goto v___jp_4508_;
}
else
{
lean_dec_ref(v_pkg_4500_);
return v___y_4514_;
}
}
v___jp_4516_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_box(0);
v___x_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4550_, lean_object* v_as_4551_, lean_object* v_i_4552_, lean_object* v_stop_4553_, lean_object* v_b_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
size_t v_i_boxed_4558_; size_t v_stop_boxed_4559_; lean_object* v_res_4560_; 
v_i_boxed_4558_ = lean_unbox_usize(v_i_4552_);
lean_dec(v_i_4552_);
v_stop_boxed_4559_ = lean_unbox_usize(v_stop_4553_);
lean_dec(v_stop_4553_);
v_res_4560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4550_, v_as_4551_, v_i_boxed_4558_, v_stop_boxed_4559_, v_b_4554_, v___y_4555_, v___y_4556_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v_as_4551_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
lean_object* v_baseName_4566_; lean_object* v_postUpdateHooks_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; 
v_baseName_4566_ = lean_ctor_get(v_pkg_4562_, 1);
v_postUpdateHooks_4567_ = lean_ctor_get(v_pkg_4562_, 19);
lean_inc_ref(v_postUpdateHooks_4567_);
v___x_4568_ = lean_array_get_size(v_postUpdateHooks_4567_);
v___x_4569_ = lean_unsigned_to_nat(0u);
v___x_4570_ = lean_nat_dec_eq(v___x_4568_, v___x_4569_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; uint8_t v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
lean_inc(v_baseName_4566_);
v___x_4571_ = l_Lean_Name_toString(v_baseName_4566_, v___x_4570_);
v___x_4572_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4573_ = lean_string_append(v___x_4571_, v___x_4572_);
v___x_4574_ = 1;
v___x_4575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4575_, 0, v___x_4573_);
lean_ctor_set_uint8(v___x_4575_, sizeof(void*)*1, v___x_4574_);
lean_inc_ref(v_a_4564_);
v___x_4576_ = lean_apply_2(v_a_4564_, v___x_4575_, lean_box(0));
v___x_4577_ = lean_box(0);
v___x_4578_ = lean_nat_dec_lt(v___x_4569_, v___x_4568_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
lean_dec_ref(v_postUpdateHooks_4567_);
lean_dec_ref(v_pkg_4562_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4577_);
return v___x_4579_;
}
else
{
uint8_t v___x_4580_; 
v___x_4580_ = lean_nat_dec_le(v___x_4568_, v___x_4568_);
if (v___x_4580_ == 0)
{
if (v___x_4578_ == 0)
{
lean_object* v___x_4581_; 
lean_dec_ref(v_postUpdateHooks_4567_);
lean_dec_ref(v_pkg_4562_);
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4577_);
return v___x_4581_;
}
else
{
size_t v___x_4582_; size_t v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = ((size_t)0ULL);
v___x_4583_ = lean_usize_of_nat(v___x_4568_);
v___x_4584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4562_, v_postUpdateHooks_4567_, v___x_4582_, v___x_4583_, v___x_4577_, v_a_4563_, v_a_4564_);
lean_dec_ref(v_postUpdateHooks_4567_);
return v___x_4584_;
}
}
else
{
size_t v___x_4585_; size_t v___x_4586_; lean_object* v___x_4587_; 
v___x_4585_ = ((size_t)0ULL);
v___x_4586_ = lean_usize_of_nat(v___x_4568_);
v___x_4587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4562_, v_postUpdateHooks_4567_, v___x_4585_, v___x_4586_, v___x_4577_, v_a_4563_, v_a_4564_);
lean_dec_ref(v_postUpdateHooks_4567_);
return v___x_4587_;
}
}
}
else
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
lean_dec_ref(v_postUpdateHooks_4567_);
lean_dec_ref(v_pkg_4562_);
v___x_4588_ = lean_box(0);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4590_, v_a_4591_, v_a_4592_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4595_, lean_object* v_ws_4596_, lean_object* v_toUpdate_4597_, lean_object* v_leanOpts_4598_, uint8_t v_updateToolchain_4599_){
_start:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4601_ = lean_box(1);
v___x_4602_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4595_, v_ws_4596_, v_toUpdate_4597_, v___x_4601_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4602_, 1);
if (v_updateToolchain_4599_ == 0)
{
lean_object* v_snd_4604_; lean_object* v_packages_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v_wsIdx_4608_; uint8_t v___x_4609_; lean_object* v___x_4610_; 
v_snd_4604_ = lean_ctor_get(v_a_4603_, 1);
lean_inc(v_snd_4604_);
lean_dec(v_a_4603_);
v_packages_4605_ = lean_ctor_get(v_ws_4596_, 4);
v___x_4606_ = lean_unsigned_to_nat(0u);
v___x_4607_ = lean_array_fget_borrowed(v_packages_4605_, v___x_4606_);
v_wsIdx_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_wsIdx_4608_);
v___x_4609_ = 1;
v___x_4610_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___redArg(v_leanOpts_4598_, v___x_4609_, v_ws_4596_, v_wsIdx_4608_, v_snd_4604_, v_a_4595_);
lean_dec(v_wsIdx_4608_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4627_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4627_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4627_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v_fst_4615_; lean_object* v_snd_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4626_; 
v_fst_4615_ = lean_ctor_get(v_a_4611_, 0);
v_snd_4616_ = lean_ctor_get(v_a_4611_, 1);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_a_4611_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4618_ = v_a_4611_;
v_isShared_4619_ = v_isSharedCheck_4626_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_snd_4616_);
lean_inc(v_fst_4615_);
lean_dec(v_a_4611_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4626_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_fst_4615_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_snd_4616_);
v___x_4621_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4623_; 
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4621_);
v___x_4623_ = v___x_4613_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
v_a_4628_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4610_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4610_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_snd_4636_; lean_object* v_packages_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v_depConfigs_4640_; lean_object* v___x_4641_; lean_object* v___f_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v_snd_4636_ = lean_ctor_get(v_a_4603_, 1);
lean_inc(v_snd_4636_);
lean_dec(v_a_4603_);
v_packages_4637_ = lean_ctor_get(v_ws_4596_, 4);
lean_inc_ref(v_packages_4637_);
v___x_4638_ = lean_unsigned_to_nat(0u);
v___x_4639_ = lean_array_fget_borrowed(v_packages_4637_, v___x_4638_);
v_depConfigs_4640_ = lean_ctor_get(v___x_4639_, 12);
v___x_4641_ = lean_box(v_updateToolchain_4599_);
lean_inc_ref(v_ws_4596_);
lean_inc(v___x_4639_);
v___f_4642_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_4642_, 0, v___x_4639_);
lean_closure_set(v___f_4642_, 1, v___x_4641_);
lean_closure_set(v___f_4642_, 2, v_ws_4596_);
v___x_4643_ = lean_array_get_size(v_depConfigs_4640_);
lean_inc_ref(v_depConfigs_4640_);
v___x_4644_ = l_Array_reverse___redArg(v_depConfigs_4640_);
v___x_4645_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___closed__0));
v___x_4646_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___redArg(v___x_4643_, v___f_4642_, v___x_4644_, v___x_4638_, v___x_4645_, v_snd_4636_, v_a_4595_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v_fst_4648_; lean_object* v_snd_4649_; lean_object* v___x_4650_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v___x_4646_, 1);
v_fst_4648_ = lean_ctor_get(v_a_4647_, 0);
lean_inc(v_fst_4648_);
v_snd_4649_ = lean_ctor_get(v_a_4647_, 1);
lean_inc(v_snd_4649_);
lean_dec(v_a_4647_);
lean_inc_ref(v_ws_4596_);
v___x_4650_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_a_4595_, v_ws_4596_, v_fst_4648_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v___x_4651_; 
lean_dec_ref_known(v___x_4650_, 1);
lean_inc_ref(v_leanOpts_4598_);
v___x_4651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___redArg(v___x_4643_, v_fst_4648_, v___x_4644_, v_leanOpts_4598_, v___x_4638_, v_ws_4596_, v_snd_4649_, v_a_4595_);
lean_dec_ref(v___x_4644_);
lean_dec(v_fst_4648_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v_fst_4653_; lean_object* v_snd_4654_; lean_object* v_packages_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_a_4652_);
lean_dec_ref_known(v___x_4651_, 1);
v_fst_4653_ = lean_ctor_get(v_a_4652_, 0);
lean_inc(v_fst_4653_);
v_snd_4654_ = lean_ctor_get(v_a_4652_, 1);
lean_inc(v_snd_4654_);
lean_dec(v_a_4652_);
v_packages_4655_ = lean_ctor_get(v_fst_4653_, 4);
v___x_4656_ = lean_array_get_size(v_packages_4637_);
lean_dec_ref(v_packages_4637_);
v___x_4657_ = lean_array_get_size(v_packages_4655_);
v___x_4658_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___redArg(v___x_4657_, v_leanOpts_4598_, v___x_4656_, v_fst_4653_, v_snd_4654_, v_a_4595_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4680_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4680_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4680_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v_fst_4663_; lean_object* v_snd_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4679_; 
v_fst_4663_ = lean_ctor_get(v_a_4659_, 0);
v_snd_4664_ = lean_ctor_get(v_a_4659_, 1);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_a_4659_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4666_ = v_a_4659_;
v_isShared_4667_ = v_isSharedCheck_4679_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_snd_4664_);
lean_inc(v_fst_4663_);
lean_dec(v_a_4659_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4679_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v_packages_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4674_; 
v_packages_4668_ = lean_ctor_get(v_fst_4663_, 4);
v___x_4669_ = lean_array_fget(v_packages_4668_, v___x_4638_);
lean_inc_ref(v_packages_4668_);
v___x_4670_ = l_Array_toSubarray___redArg(v_packages_4668_, v___x_4656_, v___x_4657_);
v___x_4671_ = l_Subarray_copy___redArg(v___x_4670_);
v___x_4672_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_fst_4663_, v___x_4669_, v___x_4671_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v___x_4672_);
v___x_4674_ = v___x_4666_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4672_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_snd_4664_);
v___x_4674_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
lean_object* v___x_4676_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4674_);
v___x_4676_ = v___x_4661_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4674_);
v___x_4676_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
return v___x_4676_;
}
}
}
}
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
v_a_4681_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4658_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4658_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec_ref(v_packages_4637_);
lean_dec_ref(v_leanOpts_4598_);
v_a_4689_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4651_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4651_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec(v_snd_4649_);
lean_dec(v_fst_4648_);
lean_dec_ref(v___x_4644_);
lean_dec_ref(v_packages_4637_);
lean_dec_ref(v_leanOpts_4598_);
lean_dec_ref(v_ws_4596_);
v_a_4697_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4650_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4650_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref(v___x_4644_);
lean_dec_ref(v_packages_4637_);
lean_dec_ref(v_leanOpts_4598_);
lean_dec_ref(v_ws_4596_);
v_a_4705_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4646_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4646_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec_ref(v_leanOpts_4598_);
lean_dec_ref(v_ws_4596_);
v_a_4713_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4602_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4602_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_4721_, lean_object* v_ws_4722_, lean_object* v_toUpdate_4723_, lean_object* v_leanOpts_4724_, lean_object* v_updateToolchain_4725_, lean_object* v_a_4726_){
_start:
{
uint8_t v_updateToolchain_boxed_4727_; lean_object* v_res_4728_; 
v_updateToolchain_boxed_4727_ = lean_unbox(v_updateToolchain_4725_);
v_res_4728_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4721_, v_ws_4722_, v_toUpdate_4723_, v_leanOpts_4724_, v_updateToolchain_boxed_4727_);
lean_dec(v_toUpdate_4723_);
lean_dec_ref(v_a_4721_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_4729_, size_t v_i_4730_, size_t v_stop_4731_, lean_object* v_b_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
uint8_t v___x_4736_; 
v___x_4736_ = lean_usize_dec_eq(v_i_4730_, v_stop_4731_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = lean_array_uget_borrowed(v_as_4729_, v_i_4730_);
lean_inc(v___x_4737_);
v___x_4738_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_4737_, v___y_4733_, v___y_4734_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v_a_4739_; size_t v___x_4740_; size_t v___x_4741_; 
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
lean_inc(v_a_4739_);
lean_dec_ref_known(v___x_4738_, 1);
v___x_4740_ = ((size_t)1ULL);
v___x_4741_ = lean_usize_add(v_i_4730_, v___x_4740_);
v_i_4730_ = v___x_4741_;
v_b_4732_ = v_a_4739_;
goto _start;
}
else
{
return v___x_4738_;
}
}
else
{
lean_object* v___x_4743_; 
v___x_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4743_, 0, v_b_4732_);
return v___x_4743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_4744_, lean_object* v_i_4745_, lean_object* v_stop_4746_, lean_object* v_b_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
size_t v_i_boxed_4751_; size_t v_stop_boxed_4752_; lean_object* v_res_4753_; 
v_i_boxed_4751_ = lean_unbox_usize(v_i_4745_);
lean_dec(v_i_4745_);
v_stop_boxed_4752_ = lean_unbox_usize(v_stop_4746_);
lean_dec(v_stop_4746_);
v_res_4753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_4744_, v_i_boxed_4751_, v_stop_boxed_4752_, v_b_4747_, v___y_4748_, v___y_4749_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v_as_4744_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_4754_, lean_object* v_toUpdate_4755_, lean_object* v_leanOpts_4756_, uint8_t v_updateToolchain_4757_, lean_object* v_a_4758_){
_start:
{
lean_object* v___x_4760_; 
v___x_4760_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_4758_, v_ws_4754_, v_toUpdate_4755_, v_leanOpts_4756_, v_updateToolchain_4757_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v_fst_4762_; lean_object* v_snd_4763_; lean_object* v___y_4765_; lean_object* v___x_4782_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v_fst_4762_ = lean_ctor_get(v_a_4761_, 0);
lean_inc(v_fst_4762_);
v_snd_4763_ = lean_ctor_get(v_a_4761_, 1);
lean_inc(v_snd_4763_);
lean_dec(v_a_4761_);
v___x_4782_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_4762_, v_snd_4763_);
lean_dec(v_snd_4763_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4804_; 
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4804_ == 0)
{
lean_object* v_unused_4805_; 
v_unused_4805_ = lean_ctor_get(v___x_4782_, 0);
lean_dec(v_unused_4805_);
v___x_4784_ = v___x_4782_;
v_isShared_4785_ = v_isSharedCheck_4804_;
goto v_resetjp_4783_;
}
else
{
lean_dec(v___x_4782_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4804_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v_packages_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v_packages_4786_ = lean_ctor_get(v_fst_4762_, 4);
v___x_4787_ = lean_unsigned_to_nat(0u);
v___x_4788_ = lean_array_get_size(v_packages_4786_);
v___x_4789_ = lean_nat_dec_lt(v___x_4787_, v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4791_; 
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 0, v_fst_4762_);
v___x_4791_ = v___x_4784_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_fst_4762_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
else
{
lean_object* v___x_4793_; uint8_t v___x_4794_; 
v___x_4793_ = lean_box(0);
v___x_4794_ = lean_nat_dec_le(v___x_4788_, v___x_4788_);
if (v___x_4794_ == 0)
{
if (v___x_4789_ == 0)
{
lean_object* v___x_4796_; 
if (v_isShared_4785_ == 0)
{
lean_ctor_set(v___x_4784_, 0, v_fst_4762_);
v___x_4796_ = v___x_4784_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_fst_4762_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
else
{
size_t v___x_4798_; size_t v___x_4799_; lean_object* v___x_4800_; 
lean_del_object(v___x_4784_);
v___x_4798_ = ((size_t)0ULL);
v___x_4799_ = lean_usize_of_nat(v___x_4788_);
v___x_4800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4786_, v___x_4798_, v___x_4799_, v___x_4793_, v_fst_4762_, v_a_4758_);
v___y_4765_ = v___x_4800_;
goto v___jp_4764_;
}
}
else
{
size_t v___x_4801_; size_t v___x_4802_; lean_object* v___x_4803_; 
lean_del_object(v___x_4784_);
v___x_4801_ = ((size_t)0ULL);
v___x_4802_ = lean_usize_of_nat(v___x_4788_);
v___x_4803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_4786_, v___x_4801_, v___x_4802_, v___x_4793_, v_fst_4762_, v_a_4758_);
v___y_4765_ = v___x_4803_;
goto v___jp_4764_;
}
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4818_; 
lean_dec(v_fst_4762_);
v_a_4806_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4808_ = v___x_4782_;
v_isShared_4809_ = v_isSharedCheck_4818_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4782_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4818_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4810_; uint8_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4816_; 
v___x_4810_ = lean_io_error_to_string(v_a_4806_);
v___x_4811_ = 3;
v___x_4812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4812_, 0, v___x_4810_);
lean_ctor_set_uint8(v___x_4812_, sizeof(void*)*1, v___x_4811_);
lean_inc_ref(v_a_4758_);
v___x_4813_ = lean_apply_2(v_a_4758_, v___x_4812_, lean_box(0));
v___x_4814_ = lean_box(0);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 0, v___x_4814_);
v___x_4816_ = v___x_4808_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4814_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
v___jp_4764_:
{
if (lean_obj_tag(v___y_4765_) == 0)
{
lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
v_isSharedCheck_4772_ = !lean_is_exclusive(v___y_4765_);
if (v_isSharedCheck_4772_ == 0)
{
lean_object* v_unused_4773_; 
v_unused_4773_ = lean_ctor_get(v___y_4765_, 0);
lean_dec(v_unused_4773_);
v___x_4767_ = v___y_4765_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_dec(v___y_4765_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 0, v_fst_4762_);
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_fst_4762_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_dec(v_fst_4762_);
v_a_4774_ = lean_ctor_get(v___y_4765_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___y_4765_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___y_4765_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___y_4765_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
v_a_4819_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4760_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4760_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_4827_, lean_object* v_toUpdate_4828_, lean_object* v_leanOpts_4829_, lean_object* v_updateToolchain_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
uint8_t v_updateToolchain_boxed_4833_; lean_object* v_res_4834_; 
v_updateToolchain_boxed_4833_ = lean_unbox(v_updateToolchain_4830_);
v_res_4834_ = l_Lake_Workspace_updateAndMaterialize(v_ws_4827_, v_toUpdate_4828_, v_leanOpts_4829_, v_updateToolchain_boxed_4833_, v_a_4831_);
lean_dec_ref(v_a_4831_);
lean_dec(v_toUpdate_4828_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_4839_, lean_object* v_what_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v_name_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; uint8_t v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v_name_4843_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_name_4843_);
lean_dec_ref(v___x_4839_);
v___x_4844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_4845_ = lean_string_append(v___x_4844_, v_what_4840_);
v___x_4846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_4847_ = lean_string_append(v___x_4845_, v___x_4846_);
v___x_4848_ = 1;
v___x_4849_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4843_, v___x_4848_);
v___x_4850_ = lean_string_append(v___x_4847_, v___x_4849_);
v___x_4851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_4852_ = lean_string_append(v___x_4850_, v___x_4851_);
v___x_4853_ = lean_string_append(v___x_4852_, v___x_4849_);
lean_dec_ref(v___x_4849_);
v___x_4854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_4855_ = lean_string_append(v___x_4853_, v___x_4854_);
v___x_4856_ = 2;
v___x_4857_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4857_, 0, v___x_4855_);
lean_ctor_set_uint8(v___x_4857_, sizeof(void*)*1, v___x_4856_);
lean_inc_ref(v___y_4841_);
v___x_4858_ = lean_apply_2(v___y_4841_, v___x_4857_, lean_box(0));
v___x_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_4860_, lean_object* v_what_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4860_, v_what_4861_, v___y_4862_);
lean_dec_ref(v___y_4862_);
lean_dec_ref(v_what_4861_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_4868_, lean_object* v_as_4869_, size_t v_i_4870_, size_t v_stop_4871_, lean_object* v_b_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_a_4876_; lean_object* v___y_4881_; uint8_t v___x_4883_; 
v___x_4883_ = lean_usize_dec_eq(v_i_4870_, v_stop_4871_);
if (v___x_4883_ == 0)
{
lean_object* v___x_4884_; lean_object* v_src_x3f_4885_; 
v___x_4884_ = lean_array_uget_borrowed(v_as_4869_, v_i_4870_);
v_src_x3f_4885_ = lean_ctor_get(v___x_4884_, 3);
if (lean_obj_tag(v_src_x3f_4885_) == 1)
{
lean_object* v_name_4886_; lean_object* v_val_4887_; lean_object* v___x_4888_; 
v_name_4886_ = lean_ctor_get(v___x_4884_, 0);
v_val_4887_ = lean_ctor_get(v_src_x3f_4885_, 0);
v___x_4888_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_4868_, v_name_4886_);
if (lean_obj_tag(v___x_4888_) == 1)
{
lean_object* v_val_4889_; lean_object* v___y_4891_; lean_object* v___y_4895_; 
v_val_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_val_4889_);
lean_dec_ref_known(v___x_4888_, 1);
if (lean_obj_tag(v_val_4887_) == 0)
{
lean_object* v_src_4898_; 
v_src_4898_ = lean_ctor_get(v_val_4889_, 4);
lean_inc_ref(v_src_4898_);
lean_dec(v_val_4889_);
if (lean_obj_tag(v_src_4898_) == 0)
{
lean_object* v___x_4899_; 
lean_dec_ref_known(v_src_4898_, 1);
v___x_4899_ = lean_box(0);
v_a_4876_ = v___x_4899_;
goto v___jp_4875_;
}
else
{
lean_dec_ref(v_src_4898_);
v___y_4895_ = v___y_4873_;
goto v___jp_4894_;
}
}
else
{
lean_object* v_src_4900_; 
v_src_4900_ = lean_ctor_get(v_val_4889_, 4);
lean_inc_ref(v_src_4900_);
lean_dec(v_val_4889_);
if (lean_obj_tag(v_src_4900_) == 1)
{
lean_object* v_url_4901_; lean_object* v_rev_4902_; lean_object* v_url_4903_; lean_object* v_inputRev_x3f_4904_; lean_object* v___y_4906_; uint8_t v___x_4913_; 
v_url_4901_ = lean_ctor_get(v_val_4887_, 0);
v_rev_4902_ = lean_ctor_get(v_val_4887_, 1);
v_url_4903_ = lean_ctor_get(v_src_4900_, 0);
lean_inc_ref(v_url_4903_);
v_inputRev_x3f_4904_ = lean_ctor_get(v_src_4900_, 2);
lean_inc(v_inputRev_x3f_4904_);
lean_dec_ref_known(v_src_4900_, 4);
v___x_4913_ = lean_string_dec_eq(v_url_4901_, v_url_4903_);
lean_dec_ref(v_url_4903_);
if (v___x_4913_ == 0)
{
goto v___jp_4910_;
}
else
{
if (v___x_4883_ == 0)
{
v___y_4906_ = v___y_4873_;
goto v___jp_4905_;
}
else
{
goto v___jp_4910_;
}
}
v___jp_4905_:
{
lean_object* v___x_4907_; uint8_t v___x_4908_; 
v___x_4907_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_4902_);
v___x_4908_ = l_Option_instDecidableEq___redArg(v___x_4907_, v_rev_4902_, v_inputRev_x3f_4904_);
if (v___x_4908_ == 0)
{
v___y_4891_ = v___y_4906_;
goto v___jp_4890_;
}
else
{
if (v___x_4883_ == 0)
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_box(0);
v_a_4876_ = v___x_4909_;
goto v___jp_4875_;
}
else
{
v___y_4891_ = v___y_4906_;
goto v___jp_4890_;
}
}
}
v___jp_4910_:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_4884_);
v___x_4912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4884_, v___x_4911_, v___y_4873_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_dec_ref_known(v___x_4912_, 1);
v___y_4906_ = v___y_4873_;
goto v___jp_4905_;
}
else
{
lean_dec(v_inputRev_x3f_4904_);
return v___x_4912_;
}
}
}
else
{
lean_dec_ref(v_src_4900_);
v___y_4895_ = v___y_4873_;
goto v___jp_4894_;
}
}
v___jp_4890_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_4884_);
v___x_4893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4884_, v___x_4892_, v___y_4891_);
v___y_4881_ = v___x_4893_;
goto v___jp_4880_;
}
v___jp_4894_:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_4884_);
v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_4884_, v___x_4896_, v___y_4895_);
v___y_4881_ = v___x_4897_;
goto v___jp_4880_;
}
}
else
{
lean_object* v___x_4914_; 
lean_dec(v___x_4888_);
v___x_4914_ = lean_box(0);
v_a_4876_ = v___x_4914_;
goto v___jp_4875_;
}
}
else
{
lean_object* v___x_4915_; 
v___x_4915_ = lean_box(0);
v_a_4876_ = v___x_4915_;
goto v___jp_4875_;
}
}
else
{
lean_object* v___x_4916_; 
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v_b_4872_);
return v___x_4916_;
}
v___jp_4875_:
{
size_t v___x_4877_; size_t v___x_4878_; 
v___x_4877_ = ((size_t)1ULL);
v___x_4878_ = lean_usize_add(v_i_4870_, v___x_4877_);
v_i_4870_ = v___x_4878_;
v_b_4872_ = v_a_4876_;
goto _start;
}
v___jp_4880_:
{
if (lean_obj_tag(v___y_4881_) == 0)
{
lean_object* v_a_4882_; 
v_a_4882_ = lean_ctor_get(v___y_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___y_4881_, 1);
v_a_4876_ = v_a_4882_;
goto v___jp_4875_;
}
else
{
return v___y_4881_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_4917_, lean_object* v_as_4918_, lean_object* v_i_4919_, lean_object* v_stop_4920_, lean_object* v_b_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
size_t v_i_boxed_4924_; size_t v_stop_boxed_4925_; lean_object* v_res_4926_; 
v_i_boxed_4924_ = lean_unbox_usize(v_i_4919_);
lean_dec(v_i_4919_);
v_stop_boxed_4925_ = lean_unbox_usize(v_stop_4920_);
lean_dec(v_stop_4920_);
v_res_4926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4917_, v_as_4918_, v_i_boxed_4924_, v_stop_boxed_4925_, v_b_4921_, v___y_4922_);
lean_dec_ref(v___y_4922_);
lean_dec_ref(v_as_4918_);
lean_dec(v_pkgEntries_4917_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_4927_, lean_object* v_deps_4928_, lean_object* v_a_4929_){
_start:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; uint8_t v___x_4934_; 
v___x_4931_ = lean_unsigned_to_nat(0u);
v___x_4932_ = lean_array_get_size(v_deps_4928_);
v___x_4933_ = lean_box(0);
v___x_4934_ = lean_nat_dec_lt(v___x_4931_, v___x_4932_);
if (v___x_4934_ == 0)
{
lean_object* v___x_4935_; 
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4933_);
return v___x_4935_;
}
else
{
uint8_t v___x_4936_; 
v___x_4936_ = lean_nat_dec_le(v___x_4932_, v___x_4932_);
if (v___x_4936_ == 0)
{
if (v___x_4934_ == 0)
{
lean_object* v___x_4937_; 
v___x_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4933_);
return v___x_4937_;
}
else
{
size_t v___x_4938_; size_t v___x_4939_; lean_object* v___x_4940_; 
v___x_4938_ = ((size_t)0ULL);
v___x_4939_ = lean_usize_of_nat(v___x_4932_);
v___x_4940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4927_, v_deps_4928_, v___x_4938_, v___x_4939_, v___x_4933_, v_a_4929_);
return v___x_4940_;
}
}
else
{
size_t v___x_4941_; size_t v___x_4942_; lean_object* v___x_4943_; 
v___x_4941_ = ((size_t)0ULL);
v___x_4942_ = lean_usize_of_nat(v___x_4932_);
v___x_4943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_4927_, v_deps_4928_, v___x_4941_, v___x_4942_, v___x_4933_, v_a_4929_);
return v___x_4943_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_4944_, lean_object* v_deps_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_4944_, v_deps_4945_, v_a_4946_);
lean_dec_ref(v_a_4946_);
lean_dec_ref(v_deps_4945_);
lean_dec(v_pkgEntries_4944_);
return v_res_4948_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_x_4949_, lean_object* v_x_4950_){
_start:
{
if (lean_obj_tag(v_x_4949_) == 0)
{
if (lean_obj_tag(v_x_4950_) == 0)
{
uint8_t v___x_4951_; 
v___x_4951_ = 1;
return v___x_4951_;
}
else
{
uint8_t v___x_4952_; 
v___x_4952_ = 0;
return v___x_4952_;
}
}
else
{
if (lean_obj_tag(v_x_4950_) == 0)
{
uint8_t v___x_4953_; 
v___x_4953_ = 0;
return v___x_4953_;
}
else
{
lean_object* v_val_4954_; lean_object* v_val_4955_; uint8_t v___x_4956_; 
v_val_4954_ = lean_ctor_get(v_x_4949_, 0);
v_val_4955_ = lean_ctor_get(v_x_4950_, 0);
v___x_4956_ = lean_string_dec_eq(v_val_4954_, v_val_4955_);
return v___x_4956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_x_4957_, lean_object* v_x_4958_){
_start:
{
uint8_t v_res_4959_; lean_object* v_r_4960_; 
v_res_4959_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_x_4957_, v_x_4958_);
lean_dec(v_x_4958_);
lean_dec(v_x_4957_);
v_r_4960_ = lean_box(v_res_4959_);
return v_r_4960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(lean_object* v_pkg_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v_leanOpts_4969_, uint8_t v_reconfigure_4970_, lean_object* v_as_4971_, size_t v_i_4972_, size_t v_stop_4973_, lean_object* v_b_4974_, lean_object* v___y_4975_){
_start:
{
uint8_t v___x_4980_; 
v___x_4980_ = lean_usize_dec_eq(v_i_4972_, v_stop_4973_);
if (v___x_4980_ == 0)
{
lean_object* v_ws_4981_; lean_object* v_depIdxs_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_5130_; 
v_ws_4981_ = lean_ctor_get(v_b_4974_, 0);
v_depIdxs_4982_ = lean_ctor_get(v_b_4974_, 1);
v_isSharedCheck_5130_ = !lean_is_exclusive(v_b_4974_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_4984_ = v_b_4974_;
v_isShared_4985_ = v_isSharedCheck_5130_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_depIdxs_4982_);
lean_inc(v_ws_4981_);
lean_dec(v_b_4974_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_5130_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v_lakeEnv_4986_; lean_object* v_packages_4987_; size_t v___x_4988_; size_t v___x_4989_; lean_object* v___x_4990_; lean_object* v___f_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v_lakeEnv_4986_ = lean_ctor_get(v_ws_4981_, 0);
v_packages_4987_ = lean_ctor_get(v_ws_4981_, 4);
v___x_4988_ = ((size_t)1ULL);
v___x_4989_ = lean_usize_sub(v_i_4972_, v___x_4988_);
v___x_4990_ = lean_array_uget_borrowed(v_as_4971_, v___x_4989_);
lean_inc(v___x_4990_);
v___f_4991_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4991_, 0, v___x_4990_);
v___x_4992_ = lean_unsigned_to_nat(0u);
v___x_4993_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_4991_, v_packages_4987_, v___x_4992_);
if (lean_obj_tag(v___x_4993_) == 1)
{
lean_object* v_val_4994_; lean_object* v___x_4995_; lean_object* v___x_4997_; 
v_val_4994_ = lean_ctor_get(v___x_4993_, 0);
lean_inc(v_val_4994_);
lean_dec_ref_known(v___x_4993_, 1);
v___x_4995_ = lean_array_push(v_depIdxs_4982_, v_val_4994_);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_4995_);
v___x_4997_ = v___x_4984_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_ws_4981_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
v_i_4972_ = v___x_4989_;
v_b_4974_ = v___x_4997_;
goto _start;
}
}
else
{
lean_object* v_wsIdx_5000_; lean_object* v_baseName_5001_; lean_object* v_name_5002_; lean_object* v_opts_5003_; uint8_t v___x_5004_; 
lean_inc_ref(v_packages_4987_);
lean_dec(v___x_4993_);
v_wsIdx_5000_ = lean_ctor_get(v_pkg_4966_, 0);
v_baseName_5001_ = lean_ctor_get(v_pkg_4966_, 1);
v_name_5002_ = lean_ctor_get(v___x_4990_, 0);
v_opts_5003_ = lean_ctor_get(v___x_4990_, 4);
v___x_5004_ = lean_name_eq(v_baseName_5001_, v_name_5002_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; 
v___x_5005_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_4967_, v_name_5002_);
if (lean_obj_tag(v___x_5005_) == 1)
{
lean_object* v_val_5006_; lean_object* v___x_5007_; lean_object* v_dir_5008_; lean_object* v___x_5009_; 
v_val_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_val_5006_);
lean_dec_ref_known(v___x_5005_, 1);
v___x_5007_ = lean_array_fget_borrowed(v_packages_4987_, v___x_4992_);
v_dir_5008_ = lean_ctor_get(v___x_5007_, 4);
lean_inc_ref(v___y_4968_);
lean_inc_ref(v_dir_5008_);
v___x_5009_ = l_Lake_PackageEntry_materialize(v_val_5006_, v_lakeEnv_4986_, v_dir_5008_, v___y_4968_, v___y_4975_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5084_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5012_ = v___x_5009_;
v_isShared_5013_ = v_isSharedCheck_5084_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_5009_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5084_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5014_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4969_);
lean_inc(v_opts_5003_);
v___x_5015_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_4981_, v_a_5010_, v_opts_5003_, v_leanOpts_4969_, v_reconfigure_4970_, v___x_5014_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v_a_5016_; lean_object* v_a_5017_; lean_object* v_wsIdx_5018_; lean_object* v___x_5019_; lean_object* v___x_5021_; 
lean_del_object(v___x_5012_);
v_a_5016_ = lean_ctor_get(v___x_5015_, 0);
lean_inc(v_a_5016_);
v_a_5017_ = lean_ctor_get(v___x_5015_, 1);
lean_inc(v_a_5017_);
lean_dec_ref_known(v___x_5015_, 2);
v_wsIdx_5018_ = lean_array_get_size(v_packages_4987_);
lean_dec_ref(v_packages_4987_);
v___x_5019_ = lean_array_push(v_depIdxs_4982_, v_wsIdx_5018_);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 1, v___x_5019_);
lean_ctor_set(v___x_4984_, 0, v_a_5016_);
v___x_5021_ = v___x_4984_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5016_);
lean_ctor_set(v_reuseFailAlloc_5052_, 1, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5022_; uint8_t v___x_5023_; 
v___x_5022_ = lean_array_get_size(v_a_5017_);
v___x_5023_ = lean_nat_dec_lt(v___x_4992_, v___x_5022_);
if (v___x_5023_ == 0)
{
lean_dec(v_a_5017_);
v_i_4972_ = v___x_4989_;
v_b_4974_ = v___x_5021_;
goto _start;
}
else
{
lean_object* v___x_5025_; uint8_t v___x_5026_; 
v___x_5025_ = lean_box(0);
v___x_5026_ = lean_nat_dec_le(v___x_5022_, v___x_5022_);
if (v___x_5026_ == 0)
{
if (v___x_5023_ == 0)
{
lean_dec(v_a_5017_);
v_i_4972_ = v___x_4989_;
v_b_4974_ = v___x_5021_;
goto _start;
}
else
{
size_t v___x_5028_; size_t v___x_5029_; lean_object* v___x_5030_; 
v___x_5028_ = ((size_t)0ULL);
v___x_5029_ = lean_usize_of_nat(v___x_5022_);
v___x_5030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5017_, v___x_5028_, v___x_5029_, v___x_5025_, v___y_4975_);
lean_dec(v_a_5017_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_dec_ref_known(v___x_5030_, 1);
v_i_4972_ = v___x_4989_;
v_b_4974_ = v___x_5021_;
goto _start;
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_leanOpts_4969_);
lean_dec_ref(v___y_4968_);
lean_dec_ref(v_pkg_4966_);
v_a_5032_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_5030_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5030_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
}
}
else
{
size_t v___x_5040_; size_t v___x_5041_; lean_object* v___x_5042_; 
v___x_5040_ = ((size_t)0ULL);
v___x_5041_ = lean_usize_of_nat(v___x_5022_);
v___x_5042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5017_, v___x_5040_, v___x_5041_, v___x_5025_, v___y_4975_);
lean_dec(v_a_5017_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_dec_ref_known(v___x_5042_, 1);
v_i_4972_ = v___x_4989_;
v_b_4974_ = v___x_5021_;
goto _start;
}
else
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
lean_dec_ref(v___x_5021_);
lean_dec_ref(v_leanOpts_4969_);
lean_dec_ref(v___y_4968_);
lean_dec_ref(v_pkg_4966_);
v_a_5044_ = lean_ctor_get(v___x_5042_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5042_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___x_5042_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5042_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
lean_dec_ref(v_packages_4987_);
lean_del_object(v___x_4984_);
lean_dec_ref(v_depIdxs_4982_);
lean_dec_ref(v_leanOpts_4969_);
lean_dec_ref(v___y_4968_);
lean_dec_ref(v_pkg_4966_);
v_a_5053_ = lean_ctor_get(v___x_5015_, 1);
lean_inc(v_a_5053_);
lean_dec_ref_known(v___x_5015_, 2);
v___x_5054_ = lean_array_get_size(v_a_5053_);
v___x_5055_ = lean_nat_dec_lt(v___x_4992_, v___x_5054_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
lean_dec(v_a_5053_);
v___x_5056_ = lean_box(0);
if (v_isShared_5013_ == 0)
{
lean_ctor_set_tag(v___x_5012_, 1);
lean_ctor_set(v___x_5012_, 0, v___x_5056_);
v___x_5058_ = v___x_5012_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v___x_5056_);
v___x_5058_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
return v___x_5058_;
}
}
else
{
lean_object* v___x_5060_; uint8_t v___x_5061_; 
lean_del_object(v___x_5012_);
v___x_5060_ = lean_box(0);
v___x_5061_ = lean_nat_dec_le(v___x_5054_, v___x_5054_);
if (v___x_5061_ == 0)
{
if (v___x_5055_ == 0)
{
lean_dec(v_a_5053_);
goto v___jp_4977_;
}
else
{
size_t v___x_5062_; size_t v___x_5063_; lean_object* v___x_5064_; 
v___x_5062_ = ((size_t)0ULL);
v___x_5063_ = lean_usize_of_nat(v___x_5054_);
v___x_5064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5053_, v___x_5062_, v___x_5063_, v___x_5060_, v___y_4975_);
lean_dec(v_a_5053_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_dec_ref_known(v___x_5064_, 1);
goto v___jp_4977_;
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
v_a_5065_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v___x_5064_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v___x_5064_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
else
{
size_t v___x_5073_; size_t v___x_5074_; lean_object* v___x_5075_; 
v___x_5073_ = ((size_t)0ULL);
v___x_5074_ = lean_usize_of_nat(v___x_5054_);
v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5053_, v___x_5073_, v___x_5074_, v___x_5060_, v___y_4975_);
lean_dec(v_a_5053_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_dec_ref_known(v___x_5075_, 1);
goto v___jp_4977_;
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5075_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5075_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
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
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec_ref(v_packages_4987_);
lean_del_object(v___x_4984_);
lean_dec_ref(v_depIdxs_4982_);
lean_dec_ref(v_ws_4981_);
lean_dec_ref(v_leanOpts_4969_);
lean_dec_ref(v___y_4968_);
lean_dec_ref(v_pkg_4966_);
v_a_5085_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5009_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5009_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
else
{
uint8_t v___x_5093_; 
lean_inc(v_baseName_5001_);
lean_inc(v_wsIdx_5000_);
lean_dec(v___x_5005_);
lean_dec_ref(v_packages_4987_);
lean_del_object(v___x_4984_);
lean_dec_ref(v_depIdxs_4982_);
lean_dec_ref(v_ws_4981_);
lean_dec_ref(v_leanOpts_4969_);
lean_dec_ref(v___y_4968_);
lean_dec_ref(v_pkg_4966_);
v___x_5093_ = lean_nat_dec_eq(v_wsIdx_5000_, v___x_4992_);
lean_dec(v_wsIdx_5000_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; uint8_t v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_5095_ = 1;
lean_inc(v_name_5002_);
v___x_5096_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5002_, v___x_5095_);
v___x_5097_ = lean_string_append(v___x_5094_, v___x_5096_);
lean_dec_ref(v___x_5096_);
v___x_5098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1));
v___x_5099_ = lean_string_append(v___x_5097_, v___x_5098_);
v___x_5100_ = l_Lean_Name_toString(v_baseName_5001_, v___x_5093_);
v___x_5101_ = lean_string_append(v___x_5099_, v___x_5100_);
lean_dec_ref(v___x_5100_);
v___x_5102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2));
v___x_5103_ = lean_string_append(v___x_5101_, v___x_5102_);
v___x_5104_ = 3;
v___x_5105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5105_, 0, v___x_5103_);
lean_ctor_set_uint8(v___x_5105_, sizeof(void*)*1, v___x_5104_);
lean_inc_ref(v___y_4975_);
v___x_5106_ = lean_apply_2(v___y_4975_, v___x_5105_, lean_box(0));
v___x_5107_ = lean_box(0);
v___x_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
return v___x_5108_;
}
else
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
lean_dec(v_baseName_5001_);
v___x_5109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
lean_inc(v_name_5002_);
v___x_5110_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5002_, v___x_5093_);
v___x_5111_ = lean_string_append(v___x_5109_, v___x_5110_);
v___x_5112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3));
v___x_5113_ = lean_string_append(v___x_5111_, v___x_5112_);
v___x_5114_ = lean_string_append(v___x_5113_, v___x_5110_);
lean_dec_ref(v___x_5110_);
v___x_5115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4));
v___x_5116_ = lean_string_append(v___x_5114_, v___x_5115_);
v___x_5117_ = 3;
v___x_5118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5118_, 0, v___x_5116_);
lean_ctor_set_uint8(v___x_5118_, sizeof(void*)*1, v___x_5117_);
lean_inc_ref(v___y_4975_);
v___x_5119_ = lean_apply_2(v___y_4975_, v___x_5118_, lean_box(0));
v___x_5120_ = lean_box(0);
v___x_5121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5120_);
return v___x_5121_;
}
}
}
else
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; uint8_t v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
lean_inc(v_baseName_5001_);
lean_dec_ref(v_packages_4987_);
lean_del_object(v___x_4984_);
lean_dec_ref(v_depIdxs_4982_);
lean_dec_ref(v_ws_4981_);
lean_dec_ref(v_leanOpts_4969_);
lean_dec_ref(v___y_4968_);
lean_dec_ref(v_pkg_4966_);
v___x_5122_ = l_Lean_Name_toString(v_baseName_5001_, v___x_4980_);
v___x_5123_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_5124_ = lean_string_append(v___x_5122_, v___x_5123_);
v___x_5125_ = 3;
v___x_5126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5126_, 0, v___x_5124_);
lean_ctor_set_uint8(v___x_5126_, sizeof(void*)*1, v___x_5125_);
lean_inc_ref(v___y_4975_);
v___x_5127_ = lean_apply_2(v___y_4975_, v___x_5126_, lean_box(0));
v___x_5128_ = lean_box(0);
v___x_5129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
return v___x_5129_;
}
}
}
}
else
{
lean_object* v___x_5131_; 
lean_dec_ref(v_leanOpts_4969_);
lean_dec_ref(v___y_4968_);
lean_dec_ref(v_pkg_4966_);
v___x_5131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5131_, 0, v_b_4974_);
return v___x_5131_;
}
v___jp_4977_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = lean_box(0);
v___x_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
return v___x_4979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_pkg_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v_leanOpts_5135_, lean_object* v_reconfigure_5136_, lean_object* v_as_5137_, lean_object* v_i_5138_, lean_object* v_stop_5139_, lean_object* v_b_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
uint8_t v_reconfigure_boxed_5143_; size_t v_i_boxed_5144_; size_t v_stop_boxed_5145_; lean_object* v_res_5146_; 
v_reconfigure_boxed_5143_ = lean_unbox(v_reconfigure_5136_);
v_i_boxed_5144_ = lean_unbox_usize(v_i_5138_);
lean_dec(v_i_5138_);
v_stop_boxed_5145_ = lean_unbox_usize(v_stop_5139_);
lean_dec(v_stop_5139_);
v_res_5146_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5132_, v___y_5133_, v___y_5134_, v_leanOpts_5135_, v_reconfigure_boxed_5143_, v_as_5137_, v_i_boxed_5144_, v_stop_boxed_5145_, v_b_5140_, v___y_5141_);
lean_dec_ref(v___y_5141_);
lean_dec_ref(v_as_5137_);
lean_dec(v___y_5133_);
return v_res_5146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(lean_object* v_start_5147_, lean_object* v_pkg_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v_leanOpts_5151_, uint8_t v_reconfigure_5152_, lean_object* v_as_5153_, size_t v_i_5154_, size_t v_stop_5155_, lean_object* v_b_5156_, lean_object* v___y_5157_){
_start:
{
uint8_t v___x_5162_; 
v___x_5162_ = lean_usize_dec_eq(v_i_5154_, v_stop_5155_);
if (v___x_5162_ == 0)
{
lean_object* v_ws_5163_; lean_object* v_depIdxs_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5312_; 
v_ws_5163_ = lean_ctor_get(v_b_5156_, 0);
v_depIdxs_5164_ = lean_ctor_get(v_b_5156_, 1);
v_isSharedCheck_5312_ = !lean_is_exclusive(v_b_5156_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5166_ = v_b_5156_;
v_isShared_5167_ = v_isSharedCheck_5312_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_depIdxs_5164_);
lean_inc(v_ws_5163_);
lean_dec(v_b_5156_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5312_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v_lakeEnv_5168_; lean_object* v_packages_5169_; size_t v___x_5170_; size_t v___x_5171_; lean_object* v___x_5172_; lean_object* v___f_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; 
v_lakeEnv_5168_ = lean_ctor_get(v_ws_5163_, 0);
v_packages_5169_ = lean_ctor_get(v_ws_5163_, 4);
v___x_5170_ = ((size_t)1ULL);
v___x_5171_ = lean_usize_sub(v_i_5154_, v___x_5170_);
v___x_5172_ = lean_array_uget_borrowed(v_as_5153_, v___x_5171_);
lean_inc(v___x_5172_);
v___f_5173_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5173_, 0, v___x_5172_);
v___x_5174_ = lean_unsigned_to_nat(0u);
v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_5173_, v_packages_5169_, v___x_5174_);
if (lean_obj_tag(v___x_5175_) == 1)
{
lean_object* v_val_5176_; lean_object* v___x_5177_; lean_object* v___x_5179_; 
v_val_5176_ = lean_ctor_get(v___x_5175_, 0);
lean_inc(v_val_5176_);
lean_dec_ref_known(v___x_5175_, 1);
v___x_5177_ = lean_array_push(v_depIdxs_5164_, v_val_5176_);
if (v_isShared_5167_ == 0)
{
lean_ctor_set(v___x_5166_, 1, v___x_5177_);
v___x_5179_ = v___x_5166_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_ws_5163_);
lean_ctor_set(v_reuseFailAlloc_5181_, 1, v___x_5177_);
v___x_5179_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5180_; 
v___x_5180_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5148_, v___y_5149_, v___y_5150_, v_leanOpts_5151_, v_reconfigure_5152_, v_as_5153_, v___x_5171_, v_stop_5155_, v___x_5179_, v___y_5157_);
return v___x_5180_;
}
}
else
{
lean_object* v_wsIdx_5182_; lean_object* v_baseName_5183_; lean_object* v_name_5184_; lean_object* v_opts_5185_; uint8_t v___x_5186_; 
lean_inc_ref(v_packages_5169_);
lean_dec(v___x_5175_);
v_wsIdx_5182_ = lean_ctor_get(v_pkg_5148_, 0);
v_baseName_5183_ = lean_ctor_get(v_pkg_5148_, 1);
v_name_5184_ = lean_ctor_get(v___x_5172_, 0);
v_opts_5185_ = lean_ctor_get(v___x_5172_, 4);
v___x_5186_ = lean_name_eq(v_baseName_5183_, v_name_5184_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5149_, v_name_5184_);
if (lean_obj_tag(v___x_5187_) == 1)
{
lean_object* v_val_5188_; lean_object* v___x_5189_; lean_object* v_dir_5190_; lean_object* v___x_5191_; 
v_val_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_val_5188_);
lean_dec_ref_known(v___x_5187_, 1);
v___x_5189_ = lean_array_fget_borrowed(v_packages_5169_, v___x_5174_);
v_dir_5190_ = lean_ctor_get(v___x_5189_, 4);
lean_inc_ref(v___y_5150_);
lean_inc_ref(v_dir_5190_);
v___x_5191_ = l_Lake_PackageEntry_materialize(v_val_5188_, v_lakeEnv_5168_, v_dir_5190_, v___y_5150_, v___y_5157_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5266_; 
v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5194_ = v___x_5191_;
v_isShared_5195_ = v_isSharedCheck_5266_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_5191_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5266_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5196_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5151_);
lean_inc(v_opts_5185_);
v___x_5197_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addDepPackage_x27(v_ws_5163_, v_a_5192_, v_opts_5185_, v_leanOpts_5151_, v_reconfigure_5152_, v___x_5196_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v_a_5199_; lean_object* v_wsIdx_5200_; lean_object* v___x_5201_; lean_object* v___x_5203_; 
lean_del_object(v___x_5194_);
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
v_a_5199_ = lean_ctor_get(v___x_5197_, 1);
lean_inc(v_a_5199_);
lean_dec_ref_known(v___x_5197_, 2);
v_wsIdx_5200_ = lean_array_get_size(v_packages_5169_);
lean_dec_ref(v_packages_5169_);
v___x_5201_ = lean_array_push(v_depIdxs_5164_, v_wsIdx_5200_);
if (v_isShared_5167_ == 0)
{
lean_ctor_set(v___x_5166_, 1, v___x_5201_);
lean_ctor_set(v___x_5166_, 0, v_a_5198_);
v___x_5203_ = v___x_5166_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5198_);
lean_ctor_set(v_reuseFailAlloc_5234_, 1, v___x_5201_);
v___x_5203_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
lean_object* v___x_5204_; uint8_t v___x_5205_; 
v___x_5204_ = lean_array_get_size(v_a_5199_);
v___x_5205_ = lean_nat_dec_lt(v___x_5174_, v___x_5204_);
if (v___x_5205_ == 0)
{
lean_object* v___x_5206_; 
lean_dec(v_a_5199_);
v___x_5206_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5148_, v___y_5149_, v___y_5150_, v_leanOpts_5151_, v_reconfigure_5152_, v_as_5153_, v___x_5171_, v_stop_5155_, v___x_5203_, v___y_5157_);
return v___x_5206_;
}
else
{
lean_object* v___x_5207_; uint8_t v___x_5208_; 
v___x_5207_ = lean_box(0);
v___x_5208_ = lean_nat_dec_le(v___x_5204_, v___x_5204_);
if (v___x_5208_ == 0)
{
if (v___x_5205_ == 0)
{
lean_object* v___x_5209_; 
lean_dec(v_a_5199_);
v___x_5209_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5148_, v___y_5149_, v___y_5150_, v_leanOpts_5151_, v_reconfigure_5152_, v_as_5153_, v___x_5171_, v_stop_5155_, v___x_5203_, v___y_5157_);
return v___x_5209_;
}
else
{
size_t v___x_5210_; size_t v___x_5211_; lean_object* v___x_5212_; 
v___x_5210_ = ((size_t)0ULL);
v___x_5211_ = lean_usize_of_nat(v___x_5204_);
v___x_5212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5199_, v___x_5210_, v___x_5211_, v___x_5207_, v___y_5157_);
lean_dec(v_a_5199_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v___x_5213_; 
lean_dec_ref_known(v___x_5212_, 1);
v___x_5213_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5148_, v___y_5149_, v___y_5150_, v_leanOpts_5151_, v_reconfigure_5152_, v_as_5153_, v___x_5171_, v_stop_5155_, v___x_5203_, v___y_5157_);
return v___x_5213_;
}
else
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
lean_dec_ref(v___x_5203_);
lean_dec_ref(v_leanOpts_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_pkg_5148_);
v_a_5214_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v___x_5212_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5212_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5219_; 
if (v_isShared_5217_ == 0)
{
v___x_5219_ = v___x_5216_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_a_5214_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
}
}
}
else
{
size_t v___x_5222_; size_t v___x_5223_; lean_object* v___x_5224_; 
v___x_5222_ = ((size_t)0ULL);
v___x_5223_ = lean_usize_of_nat(v___x_5204_);
v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5199_, v___x_5222_, v___x_5223_, v___x_5207_, v___y_5157_);
lean_dec(v_a_5199_);
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v___x_5225_; 
lean_dec_ref_known(v___x_5224_, 1);
v___x_5225_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5148_, v___y_5149_, v___y_5150_, v_leanOpts_5151_, v_reconfigure_5152_, v_as_5153_, v___x_5171_, v_stop_5155_, v___x_5203_, v___y_5157_);
return v___x_5225_;
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
lean_dec_ref(v___x_5203_);
lean_dec_ref(v_leanOpts_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_pkg_5148_);
v_a_5226_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5224_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5224_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5236_; uint8_t v___x_5237_; 
lean_dec_ref(v_packages_5169_);
lean_del_object(v___x_5166_);
lean_dec_ref(v_depIdxs_5164_);
lean_dec_ref(v_leanOpts_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_pkg_5148_);
v_a_5235_ = lean_ctor_get(v___x_5197_, 1);
lean_inc(v_a_5235_);
lean_dec_ref_known(v___x_5197_, 2);
v___x_5236_ = lean_array_get_size(v_a_5235_);
v___x_5237_ = lean_nat_dec_lt(v___x_5174_, v___x_5236_);
if (v___x_5237_ == 0)
{
lean_object* v___x_5238_; lean_object* v___x_5240_; 
lean_dec(v_a_5235_);
v___x_5238_ = lean_box(0);
if (v_isShared_5195_ == 0)
{
lean_ctor_set_tag(v___x_5194_, 1);
lean_ctor_set(v___x_5194_, 0, v___x_5238_);
v___x_5240_ = v___x_5194_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v___x_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
else
{
lean_object* v___x_5242_; uint8_t v___x_5243_; 
lean_del_object(v___x_5194_);
v___x_5242_ = lean_box(0);
v___x_5243_ = lean_nat_dec_le(v___x_5236_, v___x_5236_);
if (v___x_5243_ == 0)
{
if (v___x_5237_ == 0)
{
lean_dec(v_a_5235_);
goto v___jp_5159_;
}
else
{
size_t v___x_5244_; size_t v___x_5245_; lean_object* v___x_5246_; 
v___x_5244_ = ((size_t)0ULL);
v___x_5245_ = lean_usize_of_nat(v___x_5236_);
v___x_5246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5235_, v___x_5244_, v___x_5245_, v___x_5242_, v___y_5157_);
lean_dec(v_a_5235_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_dec_ref_known(v___x_5246_, 1);
goto v___jp_5159_;
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
else
{
size_t v___x_5255_; size_t v___x_5256_; lean_object* v___x_5257_; 
v___x_5255_ = ((size_t)0ULL);
v___x_5256_ = lean_usize_of_nat(v___x_5236_);
v___x_5257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5235_, v___x_5255_, v___x_5256_, v___x_5242_, v___y_5157_);
lean_dec(v_a_5235_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_dec_ref_known(v___x_5257_, 1);
goto v___jp_5159_;
}
else
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5265_; 
v_a_5258_ = lean_ctor_get(v___x_5257_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5260_ = v___x_5257_;
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_5257_);
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
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
lean_dec_ref(v_packages_5169_);
lean_del_object(v___x_5166_);
lean_dec_ref(v_depIdxs_5164_);
lean_dec_ref(v_ws_5163_);
lean_dec_ref(v_leanOpts_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_pkg_5148_);
v_a_5267_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5191_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5191_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
else
{
uint8_t v___x_5275_; 
lean_inc(v_baseName_5183_);
lean_inc(v_wsIdx_5182_);
lean_dec(v___x_5187_);
lean_dec_ref(v_packages_5169_);
lean_del_object(v___x_5166_);
lean_dec_ref(v_depIdxs_5164_);
lean_dec_ref(v_ws_5163_);
lean_dec_ref(v_leanOpts_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_pkg_5148_);
v___x_5275_ = lean_nat_dec_eq(v_wsIdx_5182_, v___x_5174_);
lean_dec(v_wsIdx_5182_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; uint8_t v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; uint8_t v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_5277_ = 1;
lean_inc(v_name_5184_);
v___x_5278_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5184_, v___x_5277_);
v___x_5279_ = lean_string_append(v___x_5276_, v___x_5278_);
lean_dec_ref(v___x_5278_);
v___x_5280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__1));
v___x_5281_ = lean_string_append(v___x_5279_, v___x_5280_);
v___x_5282_ = l_Lean_Name_toString(v_baseName_5183_, v___x_5275_);
v___x_5283_ = lean_string_append(v___x_5281_, v___x_5282_);
lean_dec_ref(v___x_5282_);
v___x_5284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__2));
v___x_5285_ = lean_string_append(v___x_5283_, v___x_5284_);
v___x_5286_ = 3;
v___x_5287_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5287_, 0, v___x_5285_);
lean_ctor_set_uint8(v___x_5287_, sizeof(void*)*1, v___x_5286_);
lean_inc_ref(v___y_5157_);
v___x_5288_ = lean_apply_2(v___y_5157_, v___x_5287_, lean_box(0));
v___x_5289_ = lean_box(0);
v___x_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
return v___x_5290_;
}
else
{
lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; uint8_t v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; 
lean_dec(v_baseName_5183_);
v___x_5291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__0));
lean_inc(v_name_5184_);
v___x_5292_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5184_, v___x_5275_);
v___x_5293_ = lean_string_append(v___x_5291_, v___x_5292_);
v___x_5294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__3));
v___x_5295_ = lean_string_append(v___x_5293_, v___x_5294_);
v___x_5296_ = lean_string_append(v___x_5295_, v___x_5292_);
lean_dec_ref(v___x_5292_);
v___x_5297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg___closed__4));
v___x_5298_ = lean_string_append(v___x_5296_, v___x_5297_);
v___x_5299_ = 3;
v___x_5300_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5300_, 0, v___x_5298_);
lean_ctor_set_uint8(v___x_5300_, sizeof(void*)*1, v___x_5299_);
lean_inc_ref(v___y_5157_);
v___x_5301_ = lean_apply_2(v___y_5157_, v___x_5300_, lean_box(0));
v___x_5302_ = lean_box(0);
v___x_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5303_, 0, v___x_5302_);
return v___x_5303_;
}
}
}
else
{
lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; uint8_t v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
lean_inc(v_baseName_5183_);
lean_dec_ref(v_packages_5169_);
lean_del_object(v___x_5166_);
lean_dec_ref(v_depIdxs_5164_);
lean_dec_ref(v_ws_5163_);
lean_dec_ref(v_leanOpts_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_pkg_5148_);
v___x_5304_ = l_Lean_Name_toString(v_baseName_5183_, v___x_5162_);
v___x_5305_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13___closed__0));
v___x_5306_ = lean_string_append(v___x_5304_, v___x_5305_);
v___x_5307_ = 3;
v___x_5308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5308_, 0, v___x_5306_);
lean_ctor_set_uint8(v___x_5308_, sizeof(void*)*1, v___x_5307_);
lean_inc_ref(v___y_5157_);
v___x_5309_ = lean_apply_2(v___y_5157_, v___x_5308_, lean_box(0));
v___x_5310_ = lean_box(0);
v___x_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5310_);
return v___x_5311_;
}
}
}
}
else
{
lean_object* v___x_5313_; 
lean_dec_ref(v_leanOpts_5151_);
lean_dec_ref(v___y_5150_);
lean_dec_ref(v_pkg_5148_);
v___x_5313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5313_, 0, v_b_5156_);
return v___x_5313_;
}
v___jp_5159_:
{
lean_object* v___x_5160_; lean_object* v___x_5161_; 
v___x_5160_ = lean_box(0);
v___x_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5160_);
return v___x_5161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___boxed(lean_object* v_start_5314_, lean_object* v_pkg_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v_leanOpts_5318_, lean_object* v_reconfigure_5319_, lean_object* v_as_5320_, lean_object* v_i_5321_, lean_object* v_stop_5322_, lean_object* v_b_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
uint8_t v_reconfigure_boxed_5326_; size_t v_i_boxed_5327_; size_t v_stop_boxed_5328_; lean_object* v_res_5329_; 
v_reconfigure_boxed_5326_ = lean_unbox(v_reconfigure_5319_);
v_i_boxed_5327_ = lean_unbox_usize(v_i_5321_);
lean_dec(v_i_5321_);
v_stop_boxed_5328_ = lean_unbox_usize(v_stop_5322_);
lean_dec(v_stop_5322_);
v_res_5329_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_start_5314_, v_pkg_5315_, v___y_5316_, v___y_5317_, v_leanOpts_5318_, v_reconfigure_boxed_5326_, v_as_5320_, v_i_boxed_5327_, v_stop_boxed_5328_, v_b_5323_, v___y_5324_);
lean_dec_ref(v___y_5324_);
lean_dec_ref(v_as_5320_);
lean_dec(v___y_5316_);
lean_dec(v_start_5314_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v_leanOpts_5332_, uint8_t v_reconfigure_5333_, lean_object* v_ws_5334_, lean_object* v_wsIdx_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v_packages_5338_; lean_object* v_pkg_5339_; lean_object* v_depConfigs_5340_; lean_object* v_start_5341_; lean_object* v_ws_5343_; lean_object* v_packages_5344_; lean_object* v_depIdxs_5345_; lean_object* v___y_5346_; lean_object* v_____x_5362_; lean_object* v___y_5363_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v_s_5369_; lean_object* v___x_5370_; uint8_t v___x_5371_; 
v_packages_5338_ = lean_ctor_get(v_ws_5334_, 4);
v_pkg_5339_ = lean_array_fget(v_packages_5338_, v_wsIdx_5335_);
v_depConfigs_5340_ = lean_ctor_get(v_pkg_5339_, 12);
v_start_5341_ = lean_array_get_size(v_packages_5338_);
v___x_5367_ = lean_array_get_size(v_depConfigs_5340_);
v___x_5368_ = lean_mk_empty_array_with_capacity(v___x_5367_);
lean_inc_ref(v___x_5368_);
lean_inc_ref(v_ws_5334_);
v_s_5369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_s_5369_, 0, v_ws_5334_);
lean_ctor_set(v_s_5369_, 1, v___x_5368_);
v___x_5370_ = lean_unsigned_to_nat(0u);
v___x_5371_ = lean_nat_dec_le(v___x_5367_, v___x_5367_);
if (v___x_5371_ == 0)
{
uint8_t v___x_5372_; 
v___x_5372_ = lean_nat_dec_lt(v___x_5370_, v___x_5367_);
if (v___x_5372_ == 0)
{
lean_object* v___x_5373_; 
lean_dec_ref_known(v_s_5369_, 2);
v___x_5373_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_start_5341_, v___y_5330_, v___y_5331_, v_leanOpts_5332_, v_reconfigure_5333_, v_start_5341_, v_ws_5334_, v___y_5336_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5385_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5385_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5385_ == 0)
{
v___x_5376_ = v___x_5373_;
v_isShared_5377_ = v_isSharedCheck_5385_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5373_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5385_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
size_t v_sz_5378_; size_t v___x_5379_; lean_object* v_depPkgs_5380_; lean_object* v_ws_5381_; lean_object* v___x_5383_; 
v_sz_5378_ = lean_array_size(v___x_5368_);
v___x_5379_ = ((size_t)0ULL);
v_depPkgs_5380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_a_5374_, v_sz_5378_, v___x_5379_, v___x_5368_);
v_ws_5381_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_a_5374_, v_pkg_5339_, v_depPkgs_5380_);
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v_ws_5381_);
v___x_5383_ = v___x_5376_;
goto v_reusejp_5382_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_ws_5381_);
v___x_5383_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5382_;
}
v_reusejp_5382_:
{
return v___x_5383_;
}
}
}
else
{
lean_dec_ref(v___x_5368_);
lean_dec(v_pkg_5339_);
return v___x_5373_;
}
}
else
{
size_t v___x_5386_; size_t v___x_5387_; lean_object* v___x_5388_; 
lean_dec_ref(v___x_5368_);
lean_dec_ref(v_ws_5334_);
v___x_5386_ = lean_usize_of_nat(v___x_5367_);
v___x_5387_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5332_);
lean_inc_ref(v___y_5331_);
lean_inc(v_pkg_5339_);
v___x_5388_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_start_5341_, v_pkg_5339_, v___y_5330_, v___y_5331_, v_leanOpts_5332_, v_reconfigure_5333_, v_depConfigs_5340_, v___x_5386_, v___x_5387_, v_s_5369_, v___y_5336_);
if (lean_obj_tag(v___x_5388_) == 0)
{
lean_object* v_a_5389_; 
v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
lean_inc(v_a_5389_);
lean_dec_ref_known(v___x_5388_, 1);
v_____x_5362_ = v_a_5389_;
v___y_5363_ = v___y_5336_;
goto v___jp_5361_;
}
else
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5397_; 
lean_dec(v_pkg_5339_);
lean_dec_ref(v_leanOpts_5332_);
lean_dec_ref(v___y_5331_);
v_a_5390_ = lean_ctor_get(v___x_5388_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5388_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5392_ = v___x_5388_;
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5388_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5395_; 
if (v_isShared_5393_ == 0)
{
v___x_5395_ = v___x_5392_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v_a_5390_);
v___x_5395_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
return v___x_5395_;
}
}
}
}
}
else
{
uint8_t v___x_5398_; 
lean_inc_ref(v_packages_5338_);
v___x_5398_ = lean_nat_dec_lt(v___x_5370_, v___x_5367_);
if (v___x_5398_ == 0)
{
lean_dec_ref_known(v_s_5369_, 2);
v_ws_5343_ = v_ws_5334_;
v_packages_5344_ = v_packages_5338_;
v_depIdxs_5345_ = v___x_5368_;
v___y_5346_ = v___y_5336_;
goto v___jp_5342_;
}
else
{
size_t v___x_5399_; size_t v___x_5400_; lean_object* v___x_5401_; 
lean_dec_ref(v___x_5368_);
lean_dec_ref(v_packages_5338_);
lean_dec_ref(v_ws_5334_);
v___x_5399_ = lean_usize_of_nat(v___x_5367_);
v___x_5400_ = ((size_t)0ULL);
lean_inc_ref(v_leanOpts_5332_);
lean_inc_ref(v___y_5331_);
lean_inc(v_pkg_5339_);
v___x_5401_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_start_5341_, v_pkg_5339_, v___y_5330_, v___y_5331_, v_leanOpts_5332_, v_reconfigure_5333_, v_depConfigs_5340_, v___x_5399_, v___x_5400_, v_s_5369_, v___y_5336_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v_a_5402_; 
v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc(v_a_5402_);
lean_dec_ref_known(v___x_5401_, 1);
v_____x_5362_ = v_a_5402_;
v___y_5363_ = v___y_5336_;
goto v___jp_5361_;
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_dec(v_pkg_5339_);
lean_dec_ref(v_leanOpts_5332_);
lean_dec_ref(v___y_5331_);
v_a_5403_ = lean_ctor_get(v___x_5401_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5401_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5401_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
}
v___jp_5342_:
{
lean_object* v_stop_5347_; lean_object* v___x_5348_; 
v_stop_5347_ = lean_array_get_size(v_packages_5344_);
lean_dec_ref(v_packages_5344_);
v___x_5348_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_stop_5347_, v___y_5330_, v___y_5331_, v_leanOpts_5332_, v_reconfigure_5333_, v_start_5341_, v_ws_5343_, v___y_5346_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5360_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5351_ = v___x_5348_;
v_isShared_5352_ = v_isSharedCheck_5360_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5348_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5360_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
size_t v_sz_5353_; size_t v___x_5354_; lean_object* v_depPkgs_5355_; lean_object* v_ws_5356_; lean_object* v___x_5358_; 
v_sz_5353_ = lean_array_size(v_depIdxs_5345_);
v___x_5354_ = ((size_t)0ULL);
v_depPkgs_5355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_a_5349_, v_sz_5353_, v___x_5354_, v_depIdxs_5345_);
v_ws_5356_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_setDepPkgs___redArg(v_a_5349_, v_pkg_5339_, v_depPkgs_5355_);
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 0, v_ws_5356_);
v___x_5358_ = v___x_5351_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_ws_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
else
{
lean_dec_ref(v_depIdxs_5345_);
lean_dec(v_pkg_5339_);
return v___x_5348_;
}
}
v___jp_5361_:
{
lean_object* v_ws_5364_; lean_object* v_depIdxs_5365_; lean_object* v_packages_5366_; 
v_ws_5364_ = lean_ctor_get(v_____x_5362_, 0);
lean_inc_ref(v_ws_5364_);
v_depIdxs_5365_ = lean_ctor_get(v_____x_5362_, 1);
lean_inc_ref(v_depIdxs_5365_);
lean_dec_ref(v_____x_5362_);
v_packages_5366_ = lean_ctor_get(v_ws_5364_, 4);
lean_inc_ref(v_packages_5366_);
v_ws_5343_ = v_ws_5364_;
v_packages_5344_ = v_packages_5366_;
v_depIdxs_5345_ = v_depIdxs_5365_;
v___y_5346_ = v___y_5363_;
goto v___jp_5342_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(lean_object* v_upperBound_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v_leanOpts_5414_, uint8_t v_reconfigure_5415_, lean_object* v_a_5416_, lean_object* v_b_5417_, lean_object* v___y_5418_){
_start:
{
uint8_t v___x_5420_; 
v___x_5420_ = lean_nat_dec_lt(v_a_5416_, v_upperBound_5411_);
if (v___x_5420_ == 0)
{
lean_object* v___x_5421_; 
lean_dec(v_a_5416_);
lean_dec_ref(v_leanOpts_5414_);
lean_dec_ref(v___y_5413_);
v___x_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5421_, 0, v_b_5417_);
return v___x_5421_;
}
else
{
lean_object* v___x_5422_; 
lean_inc_ref(v_leanOpts_5414_);
lean_inc_ref(v___y_5413_);
v___x_5422_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5412_, v___y_5413_, v_leanOpts_5414_, v_reconfigure_5415_, v_b_5417_, v_a_5416_, v___y_5418_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
lean_inc(v_a_5423_);
lean_dec_ref_known(v___x_5422_, 1);
v___x_5424_ = lean_unsigned_to_nat(1u);
v___x_5425_ = lean_nat_add(v_a_5416_, v___x_5424_);
lean_dec(v_a_5416_);
v_a_5416_ = v___x_5425_;
v_b_5417_ = v_a_5423_;
goto _start;
}
else
{
lean_dec(v_a_5416_);
lean_dec_ref(v_leanOpts_5414_);
lean_dec_ref(v___y_5413_);
return v___x_5422_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg___boxed(lean_object* v_upperBound_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v_leanOpts_5430_, lean_object* v_reconfigure_5431_, lean_object* v_a_5432_, lean_object* v_b_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_){
_start:
{
uint8_t v_reconfigure_boxed_5436_; lean_object* v_res_5437_; 
v_reconfigure_boxed_5436_ = lean_unbox(v_reconfigure_5431_);
v_res_5437_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_upperBound_5427_, v___y_5428_, v___y_5429_, v_leanOpts_5430_, v_reconfigure_boxed_5436_, v_a_5432_, v_b_5433_, v___y_5434_);
lean_dec_ref(v___y_5434_);
lean_dec(v___y_5428_);
lean_dec(v_upperBound_5427_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg___boxed(lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v_leanOpts_5440_, lean_object* v_reconfigure_5441_, lean_object* v_ws_5442_, lean_object* v_wsIdx_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
uint8_t v_reconfigure_boxed_5446_; lean_object* v_res_5447_; 
v_reconfigure_boxed_5446_ = lean_unbox(v_reconfigure_5441_);
v_res_5447_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5438_, v___y_5439_, v_leanOpts_5440_, v_reconfigure_boxed_5446_, v_ws_5442_, v_wsIdx_5443_, v___y_5444_);
lean_dec_ref(v___y_5444_);
lean_dec(v_wsIdx_5443_);
lean_dec(v___y_5438_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(lean_object* v_as_5448_, size_t v_i_5449_, size_t v_stop_5450_, lean_object* v_b_5451_){
_start:
{
uint8_t v___x_5452_; 
v___x_5452_ = lean_usize_dec_eq(v_i_5449_, v_stop_5450_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; lean_object* v_name_5454_; lean_object* v___x_5455_; size_t v___x_5456_; size_t v___x_5457_; 
v___x_5453_ = lean_array_uget_borrowed(v_as_5448_, v_i_5449_);
v_name_5454_ = lean_ctor_get(v___x_5453_, 0);
lean_inc(v___x_5453_);
lean_inc(v_name_5454_);
v___x_5455_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5454_, v___x_5453_, v_b_5451_);
v___x_5456_ = ((size_t)1ULL);
v___x_5457_ = lean_usize_add(v_i_5449_, v___x_5456_);
v_i_5449_ = v___x_5457_;
v_b_5451_ = v___x_5455_;
goto _start;
}
else
{
return v_b_5451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3___boxed(lean_object* v_as_5459_, lean_object* v_i_5460_, lean_object* v_stop_5461_, lean_object* v_b_5462_){
_start:
{
size_t v_i_boxed_5463_; size_t v_stop_boxed_5464_; lean_object* v_res_5465_; 
v_i_boxed_5463_ = lean_unbox_usize(v_i_5460_);
lean_dec(v_i_5460_);
v_stop_boxed_5464_ = lean_unbox_usize(v_stop_5461_);
lean_dec(v_stop_5461_);
v_res_5465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(v_as_5459_, v_i_boxed_5463_, v_stop_boxed_5464_, v_b_5462_);
lean_dec_ref(v_as_5459_);
return v_res_5465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v_as_5466_, size_t v_i_5467_, size_t v_stop_5468_, lean_object* v_b_5469_){
_start:
{
uint8_t v___x_5470_; 
v___x_5470_ = lean_usize_dec_eq(v_i_5467_, v_stop_5468_);
if (v___x_5470_ == 0)
{
lean_object* v___x_5471_; lean_object* v_name_5472_; lean_object* v___x_5473_; size_t v___x_5474_; size_t v___x_5475_; lean_object* v___x_5476_; 
v___x_5471_ = lean_array_uget_borrowed(v_as_5466_, v_i_5467_);
v_name_5472_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v___x_5471_);
lean_inc(v_name_5472_);
v___x_5473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5472_, v___x_5471_, v_b_5469_);
v___x_5474_ = ((size_t)1ULL);
v___x_5475_ = lean_usize_add(v_i_5467_, v___x_5474_);
v___x_5476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(v_as_5466_, v___x_5475_, v_stop_5468_, v___x_5473_);
return v___x_5476_;
}
else
{
return v_b_5469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v_as_5477_, lean_object* v_i_5478_, lean_object* v_stop_5479_, lean_object* v_b_5480_){
_start:
{
size_t v_i_boxed_5481_; size_t v_stop_boxed_5482_; lean_object* v_res_5483_; 
v_i_boxed_5481_ = lean_unbox_usize(v_i_5478_);
lean_dec(v_i_5478_);
v_stop_boxed_5482_ = lean_unbox_usize(v_stop_5479_);
lean_dec(v_stop_5479_);
v_res_5483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_as_5477_, v_i_boxed_5481_, v_stop_boxed_5482_, v_b_5480_);
lean_dec_ref(v_as_5477_);
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5493_, lean_object* v_manifest_5494_, lean_object* v_leanOpts_5495_, uint8_t v_reconfigure_5496_, lean_object* v_overrides_5497_, lean_object* v_a_5498_){
_start:
{
lean_object* v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; lean_object* v___y_5504_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5536_; lean_object* v___y_5537_; lean_object* v___y_5538_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5552_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v_packagesDir_x3f_5598_; lean_object* v_packages_5599_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v___y_5615_; lean_object* v___x_5623_; lean_object* v___x_5624_; uint8_t v___x_5625_; 
v_packagesDir_x3f_5598_ = lean_ctor_get(v_manifest_5494_, 2);
lean_inc(v_packagesDir_x3f_5598_);
v_packages_5599_ = lean_ctor_get(v_manifest_5494_, 3);
lean_inc_ref(v_packages_5599_);
lean_dec_ref(v_manifest_5494_);
v___x_5623_ = lean_array_get_size(v_packages_5599_);
v___x_5624_ = lean_unsigned_to_nat(0u);
v___x_5625_ = lean_nat_dec_eq(v___x_5623_, v___x_5624_);
if (v___x_5625_ == 0)
{
lean_object* v_packages_5626_; lean_object* v___x_5627_; lean_object* v_config_5628_; lean_object* v_toWorkspaceConfig_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; uint8_t v___x_5633_; 
v_packages_5626_ = lean_ctor_get(v_ws_5493_, 4);
v___x_5627_ = lean_array_fget_borrowed(v_packages_5626_, v___x_5624_);
v_config_5628_ = lean_ctor_get(v___x_5627_, 6);
v_toWorkspaceConfig_5629_ = lean_ctor_get(v_config_5628_, 0);
lean_inc_ref(v_toWorkspaceConfig_5629_);
v___x_5630_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5629_);
v___x_5631_ = l_Lake_mkRelPathString(v___x_5630_);
v___x_5632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
v___x_5633_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__2(v_packagesDir_x3f_5598_, v___x_5632_);
lean_dec_ref_known(v___x_5632_, 1);
if (v___x_5633_ == 0)
{
lean_object* v___x_5634_; lean_object* v___x_5635_; 
v___x_5634_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5498_);
v___x_5635_ = lean_apply_2(v_a_5498_, v___x_5634_, lean_box(0));
v___y_5615_ = v_a_5498_;
goto v___jp_5614_;
}
else
{
v___y_5615_ = v_a_5498_;
goto v___jp_5614_;
}
}
else
{
v___y_5615_ = v_a_5498_;
goto v___jp_5614_;
}
v___jp_5500_:
{
lean_object* v___x_5505_; 
v___x_5505_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5503_, v___y_5501_, v_leanOpts_5495_, v_reconfigure_5496_, v_ws_5493_, v___y_5502_, v___y_5504_);
lean_dec(v___y_5502_);
lean_dec(v___y_5503_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5513_; 
v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5508_ = v___x_5505_;
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v___x_5505_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v___x_5511_; 
if (v_isShared_5509_ == 0)
{
v___x_5511_ = v___x_5508_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
else
{
lean_object* v_a_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5521_; 
v_a_5514_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5516_ = v___x_5505_;
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_a_5514_);
lean_dec(v___x_5505_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5519_; 
if (v_isShared_5517_ == 0)
{
v___x_5519_ = v___x_5516_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5514_);
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
v___jp_5522_:
{
if (lean_obj_tag(v___y_5528_) == 0)
{
lean_dec_ref(v___y_5524_);
v___y_5501_ = v___y_5525_;
v___y_5502_ = v___y_5526_;
v___y_5503_ = v___y_5528_;
v___y_5504_ = v___y_5527_;
goto v___jp_5500_;
}
else
{
lean_object* v___x_5529_; uint8_t v___x_5530_; 
v___x_5529_ = lean_array_get_size(v___y_5524_);
lean_dec_ref(v___y_5524_);
v___x_5530_ = lean_nat_dec_eq(v___x_5529_, v___y_5523_);
if (v___x_5530_ == 0)
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; 
lean_dec(v___y_5526_);
lean_dec_ref(v___y_5525_);
lean_dec_ref(v_leanOpts_5495_);
lean_dec_ref(v_ws_5493_);
v___x_5531_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5527_);
v___x_5532_ = lean_apply_2(v___y_5527_, v___x_5531_, lean_box(0));
v___x_5533_ = lean_box(0);
v___x_5534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5533_);
return v___x_5534_;
}
else
{
v___y_5501_ = v___y_5525_;
v___y_5502_ = v___y_5526_;
v___y_5503_ = v___y_5528_;
v___y_5504_ = v___y_5527_;
goto v___jp_5500_;
}
}
}
v___jp_5535_:
{
lean_object* v___x_5542_; uint8_t v___x_5543_; 
v___x_5542_ = lean_array_get_size(v_overrides_5497_);
v___x_5543_ = lean_nat_dec_lt(v___y_5536_, v___x_5542_);
if (v___x_5543_ == 0)
{
v___y_5523_ = v___y_5536_;
v___y_5524_ = v___y_5538_;
v___y_5525_ = v___y_5537_;
v___y_5526_ = v___y_5539_;
v___y_5527_ = v___y_5540_;
v___y_5528_ = v___y_5541_;
goto v___jp_5522_;
}
else
{
uint8_t v___x_5544_; 
v___x_5544_ = lean_nat_dec_le(v___x_5542_, v___x_5542_);
if (v___x_5544_ == 0)
{
if (v___x_5543_ == 0)
{
v___y_5523_ = v___y_5536_;
v___y_5524_ = v___y_5538_;
v___y_5525_ = v___y_5537_;
v___y_5526_ = v___y_5539_;
v___y_5527_ = v___y_5540_;
v___y_5528_ = v___y_5541_;
goto v___jp_5522_;
}
else
{
size_t v___x_5545_; size_t v___x_5546_; lean_object* v___x_5547_; 
v___x_5545_ = ((size_t)0ULL);
v___x_5546_ = lean_usize_of_nat(v___x_5542_);
v___x_5547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5497_, v___x_5545_, v___x_5546_, v___y_5541_);
v___y_5523_ = v___y_5536_;
v___y_5524_ = v___y_5538_;
v___y_5525_ = v___y_5537_;
v___y_5526_ = v___y_5539_;
v___y_5527_ = v___y_5540_;
v___y_5528_ = v___x_5547_;
goto v___jp_5522_;
}
}
else
{
size_t v___x_5548_; size_t v___x_5549_; lean_object* v___x_5550_; 
v___x_5548_ = ((size_t)0ULL);
v___x_5549_ = lean_usize_of_nat(v___x_5542_);
v___x_5550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_overrides_5497_, v___x_5548_, v___x_5549_, v___y_5541_);
v___y_5523_ = v___y_5536_;
v___y_5524_ = v___y_5538_;
v___y_5525_ = v___y_5537_;
v___y_5526_ = v___y_5539_;
v___y_5527_ = v___y_5540_;
v___y_5528_ = v___x_5550_;
goto v___jp_5522_;
}
}
}
v___jp_5551_:
{
lean_object* v_packages_5556_; lean_object* v___x_5557_; lean_object* v_wsIdx_5558_; lean_object* v_dir_5559_; lean_object* v_depConfigs_5560_; lean_object* v___x_5561_; 
v_packages_5556_ = lean_ctor_get(v_ws_5493_, 4);
v___x_5557_ = lean_array_fget_borrowed(v_packages_5556_, v___y_5552_);
v_wsIdx_5558_ = lean_ctor_get(v___x_5557_, 0);
v_dir_5559_ = lean_ctor_get(v___x_5557_, 4);
v_depConfigs_5560_ = lean_ctor_get(v___x_5557_, 12);
v___x_5561_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5555_, v_depConfigs_5560_, v___y_5554_);
if (lean_obj_tag(v___x_5561_) == 0)
{
lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; 
lean_dec_ref_known(v___x_5561_, 1);
v___x_5562_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5559_);
v___x_5563_ = l_Lake_joinRelative(v_dir_5559_, v___x_5562_);
v___x_5564_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5565_ = l_Lake_joinRelative(v___x_5563_, v___x_5564_);
v___x_5566_ = l_Lake_Manifest_tryLoadEntries(v___x_5565_);
if (lean_obj_tag(v___x_5566_) == 0)
{
lean_object* v_a_5567_; lean_object* v___x_5568_; uint8_t v___x_5569_; 
v_a_5567_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_a_5567_);
lean_dec_ref_known(v___x_5566_, 1);
v___x_5568_ = lean_array_get_size(v_a_5567_);
v___x_5569_ = lean_nat_dec_lt(v___y_5552_, v___x_5568_);
if (v___x_5569_ == 0)
{
lean_dec(v_a_5567_);
lean_inc(v_wsIdx_5558_);
lean_inc_ref(v_depConfigs_5560_);
v___y_5536_ = v___y_5552_;
v___y_5537_ = v___y_5553_;
v___y_5538_ = v_depConfigs_5560_;
v___y_5539_ = v_wsIdx_5558_;
v___y_5540_ = v___y_5554_;
v___y_5541_ = v___y_5555_;
goto v___jp_5535_;
}
else
{
uint8_t v___x_5570_; 
v___x_5570_ = lean_nat_dec_le(v___x_5568_, v___x_5568_);
if (v___x_5570_ == 0)
{
if (v___x_5569_ == 0)
{
lean_dec(v_a_5567_);
lean_inc(v_wsIdx_5558_);
lean_inc_ref(v_depConfigs_5560_);
v___y_5536_ = v___y_5552_;
v___y_5537_ = v___y_5553_;
v___y_5538_ = v_depConfigs_5560_;
v___y_5539_ = v_wsIdx_5558_;
v___y_5540_ = v___y_5554_;
v___y_5541_ = v___y_5555_;
goto v___jp_5535_;
}
else
{
size_t v___x_5571_; size_t v___x_5572_; lean_object* v___x_5573_; 
v___x_5571_ = ((size_t)0ULL);
v___x_5572_ = lean_usize_of_nat(v___x_5568_);
v___x_5573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5567_, v___x_5571_, v___x_5572_, v___y_5555_);
lean_dec(v_a_5567_);
lean_inc(v_wsIdx_5558_);
lean_inc_ref(v_depConfigs_5560_);
v___y_5536_ = v___y_5552_;
v___y_5537_ = v___y_5553_;
v___y_5538_ = v_depConfigs_5560_;
v___y_5539_ = v_wsIdx_5558_;
v___y_5540_ = v___y_5554_;
v___y_5541_ = v___x_5573_;
goto v___jp_5535_;
}
}
else
{
size_t v___x_5574_; size_t v___x_5575_; lean_object* v___x_5576_; 
v___x_5574_ = ((size_t)0ULL);
v___x_5575_ = lean_usize_of_nat(v___x_5568_);
v___x_5576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_a_5567_, v___x_5574_, v___x_5575_, v___y_5555_);
lean_dec(v_a_5567_);
lean_inc(v_wsIdx_5558_);
lean_inc_ref(v_depConfigs_5560_);
v___y_5536_ = v___y_5552_;
v___y_5537_ = v___y_5553_;
v___y_5538_ = v_depConfigs_5560_;
v___y_5539_ = v_wsIdx_5558_;
v___y_5540_ = v___y_5554_;
v___y_5541_ = v___x_5576_;
goto v___jp_5535_;
}
}
}
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5589_; 
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5553_);
lean_dec_ref(v_leanOpts_5495_);
lean_dec_ref(v_ws_5493_);
v_a_5577_ = lean_ctor_get(v___x_5566_, 0);
v_isSharedCheck_5589_ = !lean_is_exclusive(v___x_5566_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5579_ = v___x_5566_;
v_isShared_5580_ = v_isSharedCheck_5589_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5566_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5589_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5581_; uint8_t v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___x_5581_ = lean_io_error_to_string(v_a_5577_);
v___x_5582_ = 3;
v___x_5583_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5583_, 0, v___x_5581_);
lean_ctor_set_uint8(v___x_5583_, sizeof(void*)*1, v___x_5582_);
lean_inc_ref(v___y_5554_);
v___x_5584_ = lean_apply_2(v___y_5554_, v___x_5583_, lean_box(0));
v___x_5585_ = lean_box(0);
if (v_isShared_5580_ == 0)
{
lean_ctor_set(v___x_5579_, 0, v___x_5585_);
v___x_5587_ = v___x_5579_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5585_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
}
}
else
{
lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5597_; 
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5553_);
lean_dec_ref(v_leanOpts_5495_);
lean_dec_ref(v_ws_5493_);
v_a_5590_ = lean_ctor_get(v___x_5561_, 0);
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5561_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5592_ = v___x_5561_;
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_dec(v___x_5561_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5597_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5595_; 
if (v_isShared_5593_ == 0)
{
v___x_5595_ = v___x_5592_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_a_5590_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
}
v___jp_5600_:
{
lean_object* v_pkgEntries_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; uint8_t v___x_5606_; 
v_pkgEntries_5603_ = lean_box(1);
v___x_5604_ = lean_unsigned_to_nat(0u);
v___x_5605_ = lean_array_get_size(v_packages_5599_);
v___x_5606_ = lean_nat_dec_lt(v___x_5604_, v___x_5605_);
if (v___x_5606_ == 0)
{
lean_dec_ref(v_packages_5599_);
v___y_5552_ = v___x_5604_;
v___y_5553_ = v___y_5602_;
v___y_5554_ = v___y_5601_;
v___y_5555_ = v_pkgEntries_5603_;
goto v___jp_5551_;
}
else
{
uint8_t v___x_5607_; 
v___x_5607_ = lean_nat_dec_le(v___x_5605_, v___x_5605_);
if (v___x_5607_ == 0)
{
if (v___x_5606_ == 0)
{
lean_dec_ref(v_packages_5599_);
v___y_5552_ = v___x_5604_;
v___y_5553_ = v___y_5602_;
v___y_5554_ = v___y_5601_;
v___y_5555_ = v_pkgEntries_5603_;
goto v___jp_5551_;
}
else
{
size_t v___x_5608_; size_t v___x_5609_; lean_object* v___x_5610_; 
v___x_5608_ = ((size_t)0ULL);
v___x_5609_ = lean_usize_of_nat(v___x_5605_);
v___x_5610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5599_, v___x_5608_, v___x_5609_, v_pkgEntries_5603_);
lean_dec_ref(v_packages_5599_);
v___y_5552_ = v___x_5604_;
v___y_5553_ = v___y_5602_;
v___y_5554_ = v___y_5601_;
v___y_5555_ = v___x_5610_;
goto v___jp_5551_;
}
}
else
{
size_t v___x_5611_; size_t v___x_5612_; lean_object* v___x_5613_; 
v___x_5611_ = ((size_t)0ULL);
v___x_5612_ = lean_usize_of_nat(v___x_5605_);
v___x_5613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__1(v_packages_5599_, v___x_5611_, v___x_5612_, v_pkgEntries_5603_);
lean_dec_ref(v_packages_5599_);
v___y_5552_ = v___x_5604_;
v___y_5553_ = v___y_5602_;
v___y_5554_ = v___y_5601_;
v___y_5555_ = v___x_5613_;
goto v___jp_5551_;
}
}
}
v___jp_5614_:
{
if (lean_obj_tag(v_packagesDir_x3f_5598_) == 0)
{
lean_object* v_packages_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v_config_5619_; lean_object* v_toWorkspaceConfig_5620_; lean_object* v___x_5621_; 
v_packages_5616_ = lean_ctor_get(v_ws_5493_, 4);
v___x_5617_ = lean_unsigned_to_nat(0u);
v___x_5618_ = lean_array_fget_borrowed(v_packages_5616_, v___x_5617_);
v_config_5619_ = lean_ctor_get(v___x_5618_, 6);
v_toWorkspaceConfig_5620_ = lean_ctor_get(v_config_5619_, 0);
lean_inc_ref(v_toWorkspaceConfig_5620_);
v___x_5621_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5620_);
v___y_5601_ = v___y_5615_;
v___y_5602_ = v___x_5621_;
goto v___jp_5600_;
}
else
{
lean_object* v_val_5622_; 
v_val_5622_ = lean_ctor_get(v_packagesDir_x3f_5598_, 0);
lean_inc(v_val_5622_);
lean_dec_ref_known(v_packagesDir_x3f_5598_, 1);
v___y_5601_ = v___y_5615_;
v___y_5602_ = v_val_5622_;
goto v___jp_5600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5636_, lean_object* v_manifest_5637_, lean_object* v_leanOpts_5638_, lean_object* v_reconfigure_5639_, lean_object* v_overrides_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_){
_start:
{
uint8_t v_reconfigure_boxed_5643_; lean_object* v_res_5644_; 
v_reconfigure_boxed_5643_ = lean_unbox(v_reconfigure_5639_);
v_res_5644_ = l_Lake_Workspace_materializeDeps(v_ws_5636_, v_manifest_5637_, v_leanOpts_5638_, v_reconfigure_boxed_5643_, v_overrides_5640_, v_a_5641_);
lean_dec_ref(v_a_5641_);
lean_dec_ref(v_overrides_5640_);
return v_res_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v_leanOpts_5647_, uint8_t v_reconfigure_5648_, lean_object* v_ws_5649_, lean_object* v_wsIdx_5650_, lean_object* v_h_5651_, lean_object* v___y_5652_){
_start:
{
lean_object* v___x_5654_; 
v___x_5654_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___redArg(v___y_5645_, v___y_5646_, v_leanOpts_5647_, v_reconfigure_5648_, v_ws_5649_, v_wsIdx_5650_, v___y_5652_);
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v_leanOpts_5657_, lean_object* v_reconfigure_5658_, lean_object* v_ws_5659_, lean_object* v_wsIdx_5660_, lean_object* v_h_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
uint8_t v_reconfigure_boxed_5664_; lean_object* v_res_5665_; 
v_reconfigure_boxed_5664_ = lean_unbox(v_reconfigure_5658_);
v_res_5665_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5655_, v___y_5656_, v_leanOpts_5657_, v_reconfigure_boxed_5664_, v_ws_5659_, v_wsIdx_5660_, v_h_5661_, v___y_5662_);
lean_dec_ref(v___y_5662_);
lean_dec(v_wsIdx_5660_);
lean_dec(v___y_5655_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v_upperBound_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v_leanOpts_5669_, uint8_t v_reconfigure_5670_, lean_object* v_inst_5671_, lean_object* v_R_5672_, lean_object* v_a_5673_, lean_object* v_b_5674_, lean_object* v_c_5675_, lean_object* v___y_5676_){
_start:
{
lean_object* v___x_5678_; 
v___x_5678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___redArg(v_upperBound_5666_, v___y_5667_, v___y_5668_, v_leanOpts_5669_, v_reconfigure_5670_, v_a_5673_, v_b_5674_, v___y_5676_);
return v___x_5678_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v_upperBound_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v_leanOpts_5682_, lean_object* v_reconfigure_5683_, lean_object* v_inst_5684_, lean_object* v_R_5685_, lean_object* v_a_5686_, lean_object* v_b_5687_, lean_object* v_c_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
uint8_t v_reconfigure_boxed_5691_; lean_object* v_res_5692_; 
v_reconfigure_boxed_5691_ = lean_unbox(v_reconfigure_5683_);
v_res_5692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v_upperBound_5679_, v___y_5680_, v___y_5681_, v_leanOpts_5682_, v_reconfigure_boxed_5691_, v_inst_5684_, v_R_5685_, v_a_5686_, v_b_5687_, v_c_5688_, v___y_5689_);
lean_dec_ref(v___y_5689_);
lean_dec(v___y_5680_);
lean_dec(v_upperBound_5679_);
return v_res_5692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3(lean_object* v_start_5693_, lean_object* v_pkg_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v_leanOpts_5697_, uint8_t v_reconfigure_5698_, lean_object* v_as_5699_, size_t v_i_5700_, size_t v_stop_5701_, lean_object* v_b_5702_, lean_object* v___y_5703_){
_start:
{
lean_object* v___x_5705_; 
v___x_5705_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___redArg(v_pkg_5694_, v___y_5695_, v___y_5696_, v_leanOpts_5697_, v_reconfigure_5698_, v_as_5699_, v_i_5700_, v_stop_5701_, v_b_5702_, v___y_5703_);
return v___x_5705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3___boxed(lean_object* v_start_5706_, lean_object* v_pkg_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v_leanOpts_5710_, lean_object* v_reconfigure_5711_, lean_object* v_as_5712_, lean_object* v_i_5713_, lean_object* v_stop_5714_, lean_object* v_b_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_){
_start:
{
uint8_t v_reconfigure_boxed_5718_; size_t v_i_boxed_5719_; size_t v_stop_boxed_5720_; lean_object* v_res_5721_; 
v_reconfigure_boxed_5718_ = lean_unbox(v_reconfigure_5711_);
v_i_boxed_5719_ = lean_unbox_usize(v_i_5713_);
lean_dec(v_i_5713_);
v_stop_boxed_5720_ = lean_unbox_usize(v_stop_5714_);
lean_dec(v_stop_5714_);
v_res_5721_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1_spec__3(v_start_5706_, v_pkg_5707_, v___y_5708_, v___y_5709_, v_leanOpts_5710_, v_reconfigure_boxed_5718_, v_as_5712_, v_i_boxed_5719_, v_stop_boxed_5720_, v_b_5715_, v___y_5716_);
lean_dec_ref(v___y_5716_);
lean_dec_ref(v_as_5712_);
lean_dec(v___y_5708_);
lean_dec(v_start_5706_);
return v_res_5721_;
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
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
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
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
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
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
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

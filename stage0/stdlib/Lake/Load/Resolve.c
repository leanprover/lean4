// Lean compiler output
// Module: Lake.Load.Resolve
// Imports: public import Lake.Config.Workspace public import Lake.Load.Manifest import Lake.Util.IO import Lake.Util.StoreInsts import Lake.Config.Monad import Lake.Build.Topological import Lake.Load.Materialize import Lake.Load.Lean.Eval import Lake.Load.Package
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
extern lean_object* l_Lake_defaultManifestFile;
lean_object* l_Lake_resolveConfigFile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadConfigFile___redArg(lean_object*, lean_object*);
lean_object* l_Lake_mkPackage(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
lean_object* l_Lake_formatCycle___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadCycleOfMonadCycleOf___redArg(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lake_recFetchAcyclic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_save(lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDepPackage(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDepPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_DepStackT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_DepStackT_run(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "dependency cycle detected:\n"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveT_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = ": package requires itself (or a package with the same name)"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__0_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__1_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__2_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__3_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__4_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__5_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__6 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__6_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__7 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__7_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__1_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__2_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__8_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__3_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__4_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__5_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__6_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__9_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__9_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__7_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__10 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__12(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19_spec__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19_spec__23___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19_spec__23___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19_spec__23(lean_object*, lean_object*);
static const lean_string_object l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19___closed__0 = (const lean_object*)&l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg___closed__0 = (const lean_object*)&l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__11_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": updating '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' with "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dependency '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "' of '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "' not in manifest; this suggests that the manifest is corrupt; use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "' not in manifest; use `lake update "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` to add it"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(lean_object* v_ws_3_, lean_object* v_dep_4_, lean_object* v_lakeOpts_5_, lean_object* v_leanOpts_6_, uint8_t v_reconfigure_7_){
_start:
{
lean_object* v_root_8_; lean_object* v_manifestEntry_9_; lean_object* v_lakeEnv_10_; lean_object* v_packages_11_; lean_object* v_dir_12_; lean_object* v_pkgDir_13_; lean_object* v_relPkgDir_14_; lean_object* v_remoteUrl_15_; lean_object* v_name_16_; lean_object* v_scope_17_; lean_object* v_configFile_18_; lean_object* v_manifestFile_x3f_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___y_24_; 
v_root_8_ = lean_ctor_get(v_ws_3_, 0);
v_manifestEntry_9_ = lean_ctor_get(v_dep_4_, 4);
lean_inc_ref(v_manifestEntry_9_);
v_lakeEnv_10_ = lean_ctor_get(v_ws_3_, 1);
v_packages_11_ = lean_ctor_get(v_ws_3_, 5);
v_dir_12_ = lean_ctor_get(v_root_8_, 4);
v_pkgDir_13_ = lean_ctor_get(v_dep_4_, 0);
lean_inc_ref_n(v_pkgDir_13_, 2);
v_relPkgDir_14_ = lean_ctor_get(v_dep_4_, 1);
lean_inc_ref(v_relPkgDir_14_);
v_remoteUrl_15_ = lean_ctor_get(v_dep_4_, 2);
lean_inc_ref(v_remoteUrl_15_);
lean_dec_ref(v_dep_4_);
v_name_16_ = lean_ctor_get(v_manifestEntry_9_, 0);
lean_inc(v_name_16_);
v_scope_17_ = lean_ctor_get(v_manifestEntry_9_, 1);
lean_inc_ref(v_scope_17_);
v_configFile_18_ = lean_ctor_get(v_manifestEntry_9_, 2);
lean_inc_ref_n(v_configFile_18_, 2);
v_manifestFile_x3f_19_ = lean_ctor_get(v_manifestEntry_9_, 3);
lean_inc(v_manifestFile_x3f_19_);
lean_dec_ref(v_manifestEntry_9_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_array_get_size(v_packages_11_);
v___x_22_ = l_Lake_joinRelative(v_pkgDir_13_, v_configFile_18_);
if (lean_obj_tag(v_manifestFile_x3f_19_) == 0)
{
lean_object* v___x_29_; 
v___x_29_ = l_Lake_defaultManifestFile;
v___y_24_ = v___x_29_;
goto v___jp_23_;
}
else
{
lean_object* v_val_30_; 
v_val_30_ = lean_ctor_get(v_manifestFile_x3f_19_, 0);
lean_inc(v_val_30_);
lean_dec_ref(v_manifestFile_x3f_19_);
v___y_24_ = v_val_30_;
goto v___jp_23_;
}
v___jp_23_:
{
lean_object* v___x_25_; uint8_t v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; 
v___x_25_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_26_ = 0;
v___x_27_ = 1;
lean_inc_ref(v_dir_12_);
lean_inc_ref(v_lakeEnv_10_);
v___x_28_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_28_, 0, v_lakeEnv_10_);
lean_ctor_set(v___x_28_, 1, v___x_20_);
lean_ctor_set(v___x_28_, 2, v_dir_12_);
lean_ctor_set(v___x_28_, 3, v___x_21_);
lean_ctor_set(v___x_28_, 4, v_name_16_);
lean_ctor_set(v___x_28_, 5, v_relPkgDir_14_);
lean_ctor_set(v___x_28_, 6, v_pkgDir_13_);
lean_ctor_set(v___x_28_, 7, v_configFile_18_);
lean_ctor_set(v___x_28_, 8, v___x_22_);
lean_ctor_set(v___x_28_, 9, v___x_20_);
lean_ctor_set(v___x_28_, 10, v___y_24_);
lean_ctor_set(v___x_28_, 11, v___x_25_);
lean_ctor_set(v___x_28_, 12, v_lakeOpts_5_);
lean_ctor_set(v___x_28_, 13, v_leanOpts_6_);
lean_ctor_set(v___x_28_, 14, v_scope_17_);
lean_ctor_set(v___x_28_, 15, v_remoteUrl_15_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*16, v_reconfigure_7_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*16 + 1, v___x_26_);
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*16 + 2, v___x_27_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___boxed(lean_object* v_ws_31_, lean_object* v_dep_32_, lean_object* v_lakeOpts_33_, lean_object* v_leanOpts_34_, lean_object* v_reconfigure_35_){
_start:
{
uint8_t v_reconfigure_boxed_36_; lean_object* v_res_37_; 
v_reconfigure_boxed_36_ = lean_unbox(v_reconfigure_35_);
v_res_37_ = l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig(v_ws_31_, v_dep_32_, v_lakeOpts_33_, v_leanOpts_34_, v_reconfigure_boxed_36_);
lean_dec_ref(v_ws_31_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls_spec__0(lean_object* v_as_38_, size_t v_i_39_, size_t v_stop_40_, lean_object* v_b_41_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = lean_usize_dec_eq(v_i_39_, v_stop_40_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v_name_44_; lean_object* v_config_45_; lean_object* v_root_46_; lean_object* v_lakeEnv_47_; lean_object* v_lakeConfig_48_; lean_object* v_lakeCache_49_; lean_object* v_lakeArgs_x3f_50_; lean_object* v_packages_51_; lean_object* v_packageMap_52_; lean_object* v_facetConfigs_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_64_; 
v___x_43_ = lean_array_uget_borrowed(v_as_38_, v_i_39_);
v_name_44_ = lean_ctor_get(v___x_43_, 0);
v_config_45_ = lean_ctor_get(v___x_43_, 1);
v_root_46_ = lean_ctor_get(v_b_41_, 0);
v_lakeEnv_47_ = lean_ctor_get(v_b_41_, 1);
v_lakeConfig_48_ = lean_ctor_get(v_b_41_, 2);
v_lakeCache_49_ = lean_ctor_get(v_b_41_, 3);
v_lakeArgs_x3f_50_ = lean_ctor_get(v_b_41_, 4);
v_packages_51_ = lean_ctor_get(v_b_41_, 5);
v_packageMap_52_ = lean_ctor_get(v_b_41_, 6);
v_facetConfigs_53_ = lean_ctor_get(v_b_41_, 7);
v_isSharedCheck_64_ = !lean_is_exclusive(v_b_41_);
if (v_isSharedCheck_64_ == 0)
{
v___x_55_ = v_b_41_;
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
lean_inc(v_root_46_);
lean_dec(v_b_41_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_64_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_57_; lean_object* v___x_59_; 
lean_inc(v_config_45_);
lean_inc(v_name_44_);
v___x_57_ = l_Lake_FacetConfigMap_insert(v_name_44_, v_config_45_, v_facetConfigs_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 7, v___x_57_);
v___x_59_ = v___x_55_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_root_46_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_lakeEnv_47_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_lakeConfig_48_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v_lakeCache_49_);
lean_ctor_set(v_reuseFailAlloc_63_, 4, v_lakeArgs_x3f_50_);
lean_ctor_set(v_reuseFailAlloc_63_, 5, v_packages_51_);
lean_ctor_set(v_reuseFailAlloc_63_, 6, v_packageMap_52_);
lean_ctor_set(v_reuseFailAlloc_63_, 7, v___x_57_);
v___x_59_ = v_reuseFailAlloc_63_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
size_t v___x_60_; size_t v___x_61_; 
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_39_, v___x_60_);
v_i_39_ = v___x_61_;
v_b_41_ = v___x_59_;
goto _start;
}
}
}
else
{
return v_b_41_;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0___redArg(lean_object* v_k_87_, lean_object* v_v_88_, lean_object* v_t_89_){
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
v_impl_99_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0___redArg(v_k_87_, v_v_88_, v_l_93_);
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
v_impl_239_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0___redArg(v_k_87_, v_v_88_, v_r_94_);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDepPackage(lean_object* v_dep_377_, lean_object* v_lakeOpts_378_, lean_object* v_leanOpts_379_, uint8_t v_reconfigure_380_, lean_object* v_ws_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_root_384_; lean_object* v_manifestEntry_385_; lean_object* v_lakeEnv_386_; lean_object* v_lakeConfig_387_; lean_object* v_lakeCache_388_; lean_object* v_lakeArgs_x3f_389_; lean_object* v_packages_390_; lean_object* v_packageMap_391_; lean_object* v_facetConfigs_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_457_; 
v_root_384_ = lean_ctor_get(v_ws_381_, 0);
lean_inc_ref(v_root_384_);
v_manifestEntry_385_ = lean_ctor_get(v_dep_377_, 4);
lean_inc_ref(v_manifestEntry_385_);
v_lakeEnv_386_ = lean_ctor_get(v_ws_381_, 1);
v_lakeConfig_387_ = lean_ctor_get(v_ws_381_, 2);
v_lakeCache_388_ = lean_ctor_get(v_ws_381_, 3);
v_lakeArgs_x3f_389_ = lean_ctor_get(v_ws_381_, 4);
v_packages_390_ = lean_ctor_get(v_ws_381_, 5);
v_packageMap_391_ = lean_ctor_get(v_ws_381_, 6);
v_facetConfigs_392_ = lean_ctor_get(v_ws_381_, 7);
v_isSharedCheck_457_ = !lean_is_exclusive(v_ws_381_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v_ws_381_, 0);
lean_dec(v_unused_458_);
v___x_394_ = v_ws_381_;
v_isShared_395_ = v_isSharedCheck_457_;
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
lean_dec(v_ws_381_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_457_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_dir_396_; lean_object* v_pkgDir_397_; lean_object* v_relPkgDir_398_; lean_object* v_remoteUrl_399_; lean_object* v_name_400_; lean_object* v_scope_401_; lean_object* v_configFile_402_; lean_object* v_manifestFile_x3f_403_; lean_object* v_wsIdx_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___y_408_; 
v_dir_396_ = lean_ctor_get(v_root_384_, 4);
v_pkgDir_397_ = lean_ctor_get(v_dep_377_, 0);
lean_inc_ref_n(v_pkgDir_397_, 2);
v_relPkgDir_398_ = lean_ctor_get(v_dep_377_, 1);
lean_inc_ref(v_relPkgDir_398_);
v_remoteUrl_399_ = lean_ctor_get(v_dep_377_, 2);
lean_inc_ref(v_remoteUrl_399_);
lean_dec_ref(v_dep_377_);
v_name_400_ = lean_ctor_get(v_manifestEntry_385_, 0);
lean_inc(v_name_400_);
v_scope_401_ = lean_ctor_get(v_manifestEntry_385_, 1);
lean_inc_ref(v_scope_401_);
v_configFile_402_ = lean_ctor_get(v_manifestEntry_385_, 2);
lean_inc_ref_n(v_configFile_402_, 2);
v_manifestFile_x3f_403_ = lean_ctor_get(v_manifestEntry_385_, 3);
lean_inc(v_manifestFile_x3f_403_);
lean_dec_ref(v_manifestEntry_385_);
v_wsIdx_404_ = lean_array_get_size(v_packages_390_);
v___x_405_ = lean_box(0);
v___x_406_ = l_Lake_joinRelative(v_pkgDir_397_, v_configFile_402_);
if (lean_obj_tag(v_manifestFile_x3f_403_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = l_Lake_defaultManifestFile;
v___y_408_ = v___x_455_;
goto v___jp_407_;
}
else
{
lean_object* v_val_456_; 
v_val_456_ = lean_ctor_get(v_manifestFile_x3f_403_, 0);
lean_inc(v_val_456_);
lean_dec_ref(v_manifestFile_x3f_403_);
v___y_408_ = v_val_456_;
goto v___jp_407_;
}
v___jp_407_:
{
lean_object* v___x_409_; uint8_t v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_409_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_410_ = 0;
v___x_411_ = 1;
lean_inc(v_name_400_);
lean_inc_ref(v_dir_396_);
lean_inc_ref(v_lakeEnv_386_);
v___x_412_ = lean_alloc_ctor(0, 16, 3);
lean_ctor_set(v___x_412_, 0, v_lakeEnv_386_);
lean_ctor_set(v___x_412_, 1, v___x_405_);
lean_ctor_set(v___x_412_, 2, v_dir_396_);
lean_ctor_set(v___x_412_, 3, v_wsIdx_404_);
lean_ctor_set(v___x_412_, 4, v_name_400_);
lean_ctor_set(v___x_412_, 5, v_relPkgDir_398_);
lean_ctor_set(v___x_412_, 6, v_pkgDir_397_);
lean_ctor_set(v___x_412_, 7, v_configFile_402_);
lean_ctor_set(v___x_412_, 8, v___x_406_);
lean_ctor_set(v___x_412_, 9, v___x_405_);
lean_ctor_set(v___x_412_, 10, v___y_408_);
lean_ctor_set(v___x_412_, 11, v___x_409_);
lean_ctor_set(v___x_412_, 12, v_lakeOpts_378_);
lean_ctor_set(v___x_412_, 13, v_leanOpts_379_);
lean_ctor_set(v___x_412_, 14, v_scope_401_);
lean_ctor_set(v___x_412_, 15, v_remoteUrl_399_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*16, v_reconfigure_380_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*16 + 1, v___x_410_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*16 + 2, v___x_411_);
v___x_413_ = l_Lean_Name_toString(v_name_400_, v___x_410_);
v___x_414_ = l_Lake_resolveConfigFile(v___x_413_, v___x_412_, v_a_382_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v_a_416_; lean_object* v___x_417_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_n(v_a_415_, 2);
v_a_416_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_a_416_);
lean_dec_ref(v___x_414_);
v___x_417_ = l_Lake_loadConfigFile___redArg(v_a_415_, v_a_416_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_436_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_a_419_ = lean_ctor_get(v___x_417_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_421_ = v___x_417_;
v_isShared_422_ = v_isSharedCheck_436_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_436_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v_keyName_424_; lean_object* v_facetDecls_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
lean_inc(v_a_418_);
v___x_423_ = l_Lake_mkPackage(v_a_415_, v_a_418_, v_wsIdx_404_);
lean_dec(v_a_415_);
v_keyName_424_ = lean_ctor_get(v___x_423_, 2);
lean_inc(v_keyName_424_);
v_facetDecls_425_ = lean_ctor_get(v_a_418_, 2);
lean_inc_ref(v_facetDecls_425_);
lean_dec(v_a_418_);
lean_inc_ref_n(v___x_423_, 2);
v___x_426_ = lean_array_push(v_packages_390_, v___x_423_);
v___x_427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0___redArg(v_keyName_424_, v___x_423_, v_packageMap_391_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 6, v___x_427_);
lean_ctor_set(v___x_394_, 5, v___x_426_);
v___x_429_ = v___x_394_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_root_384_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_lakeEnv_386_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_lakeConfig_387_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_lakeCache_388_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_lakeArgs_x3f_389_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_facetConfigs_392_);
v___x_429_ = v_reuseFailAlloc_435_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_addFacetDecls(v_facetDecls_425_, v___x_429_);
lean_dec_ref(v_facetDecls_425_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_423_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_431_);
v___x_433_ = v___x_421_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_a_419_);
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
lean_dec(v_a_415_);
lean_del_object(v___x_394_);
lean_dec(v_facetConfigs_392_);
lean_dec(v_packageMap_391_);
lean_dec_ref(v_packages_390_);
lean_dec(v_lakeArgs_x3f_389_);
lean_dec_ref(v_lakeCache_388_);
lean_dec_ref(v_lakeConfig_387_);
lean_dec_ref(v_lakeEnv_386_);
lean_dec_ref(v_root_384_);
v_a_437_ = lean_ctor_get(v___x_417_, 0);
v_a_438_ = lean_ctor_get(v___x_417_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_417_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_inc(v_a_437_);
lean_dec(v___x_417_);
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
lean_del_object(v___x_394_);
lean_dec(v_facetConfigs_392_);
lean_dec(v_packageMap_391_);
lean_dec_ref(v_packages_390_);
lean_dec(v_lakeArgs_x3f_389_);
lean_dec_ref(v_lakeCache_388_);
lean_dec_ref(v_lakeConfig_387_);
lean_dec_ref(v_lakeEnv_386_);
lean_dec_ref(v_root_384_);
v_a_446_ = lean_ctor_get(v___x_414_, 0);
v_a_447_ = lean_ctor_get(v___x_414_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_414_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_inc(v_a_446_);
lean_dec(v___x_414_);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDepPackage___boxed(lean_object* v_dep_459_, lean_object* v_lakeOpts_460_, lean_object* v_leanOpts_461_, lean_object* v_reconfigure_462_, lean_object* v_ws_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
uint8_t v_reconfigure_boxed_466_; lean_object* v_res_467_; 
v_reconfigure_boxed_466_ = lean_unbox(v_reconfigure_462_);
v_res_467_ = l___private_Lake_Load_Resolve_0__Lake_addDepPackage(v_dep_459_, v_lakeOpts_460_, v_leanOpts_461_, v_reconfigure_boxed_466_, v_ws_463_, v_a_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0(lean_object* v_00_u03b2_468_, lean_object* v_k_469_, lean_object* v_v_470_, lean_object* v_t_471_, lean_object* v_hl_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lake_Load_Resolve_0__Lake_addDepPackage_spec__0___redArg(v_k_469_, v_v_470_, v_t_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_DepStackT_run___redArg(lean_object* v_x_474_, lean_object* v_stack_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_apply_1(v_x_474_, v_stack_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_DepStackT_run(lean_object* v_m_477_, lean_object* v_00_u03b1_478_, lean_object* v_x_479_, lean_object* v_stack_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = lean_apply_1(v_x_479_, v_stack_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg(lean_object* v_inst_484_, lean_object* v_cycle_485_){
_start:
{
lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___f_486_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__0));
v___x_487_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1));
v___x_488_ = l_Lake_formatCycle___redArg(v___f_486_, v_cycle_485_);
v___x_489_ = lean_string_append(v___x_487_, v___x_488_);
lean_dec_ref(v___x_488_);
v___x_490_ = lean_apply_2(v_inst_484_, lean_box(0), v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError(lean_object* v_m_491_, lean_object* v_00_u03b1_492_, lean_object* v_inst_493_, lean_object* v_cycle_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg(v_inst_493_, v_cycle_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0(lean_object* v___f_496_, lean_object* v_00_u03b1_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_23__overap_500_; lean_object* v___x_501_; 
v___x_23__overap_500_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg(v___f_496_, v___y_498_);
lean_inc(v___y_499_);
v___x_501_ = lean_apply_1(v___x_23__overap_500_, v___y_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0___boxed(lean_object* v___f_502_, lean_object* v_00_u03b1_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0(v___f_502_, v_00_u03b1_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(lean_object* v_inst_508_, lean_object* v_inst_509_){
_start:
{
lean_object* v___x_510_; lean_object* v___f_511_; lean_object* v___f_512_; lean_object* v___f_513_; lean_object* v___x_514_; 
v___x_510_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v_inst_508_);
v___f_511_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0));
v___f_512_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_512_, 0, v_inst_509_);
lean_closure_set(v___f_512_, 1, v___f_511_);
v___f_513_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_513_, 0, v___f_512_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_510_);
lean_ctor_set(v___x_514_, 1, v___f_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError(lean_object* v_m_515_, lean_object* v_inst_516_, lean_object* v_inst_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(v_inst_516_, v_inst_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveT_run___redArg(lean_object* v_ws_519_, lean_object* v_x_520_, lean_object* v_stack_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_apply_2(v_x_520_, v_stack_521_, v_ws_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveT_run(lean_object* v_m_523_, lean_object* v_00_u03b1_524_, lean_object* v_ws_525_, lean_object* v_x_526_, lean_object* v_stack_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_apply_2(v_x_526_, v_stack_527_, v_ws_525_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(lean_object* v_x_529_){
_start:
{
lean_object* v_baseName_530_; 
v_baseName_530_ = lean_ctor_get(v_x_529_, 1);
lean_inc(v_baseName_530_);
return v_baseName_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0___boxed(lean_object* v_x_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(v_x_531_);
lean_dec_ref(v_x_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1(lean_object* v_toPure_533_, lean_object* v_____x_534_){
_start:
{
lean_object* v_snd_535_; lean_object* v___x_536_; 
v_snd_535_ = lean_ctor_get(v_____x_534_, 1);
lean_inc(v_snd_535_);
lean_dec_ref(v_____x_534_);
v___x_536_ = lean_apply_2(v_toPure_533_, lean_box(0), v_snd_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_ws_541_, lean_object* v_go_542_, lean_object* v_root_543_, lean_object* v_stack_544_){
_start:
{
lean_object* v_toApplicative_545_; lean_object* v_toBind_546_; lean_object* v___f_547_; lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___f_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_toPure_562_; lean_object* v___f_563_; lean_object* v___x_564_; lean_object* v___f_565_; lean_object* v___x_32__overap_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_toApplicative_545_ = lean_ctor_get(v_inst_539_, 0);
lean_inc_ref(v_toApplicative_545_);
v_toBind_546_ = lean_ctor_get(v_inst_539_, 1);
lean_inc(v_toBind_546_);
lean_inc_ref_n(v_inst_539_, 7);
v___f_547_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_547_, 0, v_inst_539_);
v___f_548_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_548_, 0, v_inst_539_);
v___f_549_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_549_, 0, v_inst_539_);
v___f_550_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_550_, 0, v_inst_539_);
v___x_551_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_551_, 0, lean_box(0));
lean_closure_set(v___x_551_, 1, lean_box(0));
lean_closure_set(v___x_551_, 2, v_inst_539_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v___f_547_);
v___x_553_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_553_, 0, lean_box(0));
lean_closure_set(v___x_553_, 1, lean_box(0));
lean_closure_set(v___x_553_, 2, v_inst_539_);
v___x_554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
lean_ctor_set(v___x_554_, 2, v___f_548_);
lean_ctor_set(v___x_554_, 3, v___f_549_);
lean_ctor_set(v___x_554_, 4, v___f_550_);
v___x_555_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_555_, 0, lean_box(0));
lean_closure_set(v___x_555_, 1, lean_box(0));
lean_closure_set(v___x_555_, 2, v_inst_539_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
lean_inc_ref(v___x_556_);
v___x_557_ = l_ReaderT_instMonad___redArg(v___x_556_);
v___x_558_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_558_, 0, lean_box(0));
lean_closure_set(v___x_558_, 1, lean_box(0));
lean_closure_set(v___x_558_, 2, v_inst_539_);
v___f_559_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_559_, 0, v_inst_540_);
lean_closure_set(v___f_559_, 1, v___x_558_);
v___x_560_ = l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(v___x_556_, v___f_559_);
v___x_561_ = l_Lake_instMonadCycleOfMonadCycleOf___redArg(v___x_560_);
v_toPure_562_ = lean_ctor_get(v_toApplicative_545_, 1);
lean_inc(v_toPure_562_);
lean_dec_ref(v_toApplicative_545_);
v___f_563_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0));
v___x_564_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__1));
v___f_565_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1), 2, 1);
lean_closure_set(v___f_565_, 0, v_toPure_562_);
v___x_32__overap_566_ = l_Lake_recFetchAcyclic___redArg(v___x_564_, v___x_557_, v___x_561_, v___f_563_, v_go_542_, v_root_543_);
v___x_567_ = lean_apply_2(v___x_32__overap_566_, v_stack_544_, v_ws_541_);
v___x_568_ = lean_apply_4(v_toBind_546_, lean_box(0), lean_box(0), v___x_567_, v___f_565_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT(lean_object* v_m_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_ws_572_, lean_object* v_go_573_, lean_object* v_root_574_, lean_object* v_stack_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(v_inst_570_, v_inst_571_, v_ws_572_, v_go_573_, v_root_574_, v_stack_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_fst_577_, lean_object* v_toPure_578_, lean_object* v_____x_579_){
_start:
{
lean_object* v_snd_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
v_snd_580_ = lean_ctor_get(v_____x_579_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_____x_579_);
if (v_isSharedCheck_588_ == 0)
{
lean_object* v_unused_589_; 
v_unused_589_ = lean_ctor_get(v_____x_579_, 0);
lean_dec(v_unused_589_);
v___x_582_ = v_____x_579_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_snd_580_);
lean_dec(v_____x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_fst_577_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_fst_577_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_580_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_apply_2(v_toPure_578_, lean_box(0), v___x_585_);
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_toPure_590_, lean_object* v_toBind_591_, lean_object* v_____x_592_){
_start:
{
lean_object* v_fst_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_606_; 
v_fst_593_ = lean_ctor_get(v_____x_592_, 0);
lean_inc(v_fst_593_);
lean_dec_ref(v_____x_592_);
v_fst_594_ = lean_ctor_get(v_fst_593_, 0);
v_snd_595_ = lean_ctor_get(v_fst_593_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v_fst_593_);
if (v_isSharedCheck_606_ == 0)
{
v___x_597_ = v_fst_593_;
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snd_595_);
lean_inc(v_fst_594_);
lean_dec(v_fst_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
lean_inc(v_toPure_590_);
v___f_599_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0), 3, 2);
lean_closure_set(v___f_599_, 0, v_fst_594_);
lean_closure_set(v___f_599_, 1, v_toPure_590_);
v___x_600_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_600_);
v___x_602_ = v___x_597_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_snd_595_);
v___x_602_ = v_reuseFailAlloc_605_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_apply_2(v_toPure_590_, lean_box(0), v___x_602_);
v___x_604_ = lean_apply_4(v_toBind_591_, lean_box(0), lean_box(0), v___x_603_, v___f_599_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_a_607_, lean_object* v_x_608_){
_start:
{
lean_object* v_baseName_609_; lean_object* v_name_610_; uint8_t v___x_611_; 
v_baseName_609_ = lean_ctor_get(v_x_608_, 1);
v_name_610_ = lean_ctor_get(v_a_607_, 0);
v___x_611_ = lean_name_eq(v_baseName_609_, v_name_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object* v_a_612_, lean_object* v_x_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_a_612_, v_x_613_);
lean_dec_ref(v_x_613_);
lean_dec_ref(v_a_612_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v_snd_616_, lean_object* v_toPure_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v_a_618_);
lean_ctor_set(v___x_619_, 1, v_snd_616_);
v___x_620_ = lean_apply_2(v_toPure_617_, lean_box(0), v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_fst_621_, lean_object* v_opts_622_, lean_object* v_leanOpts_623_, uint8_t v_reconfigure_624_, lean_object* v_inst_625_, lean_object* v_toPure_626_, lean_object* v_toBind_627_, lean_object* v___f_628_, lean_object* v_____x_629_){
_start:
{
lean_object* v_fst_630_; lean_object* v_snd_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_fst_630_ = lean_ctor_get(v_____x_629_, 0);
lean_inc(v_fst_630_);
v_snd_631_ = lean_ctor_get(v_____x_629_, 1);
lean_inc(v_snd_631_);
lean_dec_ref(v_____x_629_);
v___x_632_ = lean_box(v_reconfigure_624_);
v___x_633_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_addDepPackage___boxed), 7, 5);
lean_closure_set(v___x_633_, 0, v_fst_621_);
lean_closure_set(v___x_633_, 1, v_opts_622_);
lean_closure_set(v___x_633_, 2, v_leanOpts_623_);
lean_closure_set(v___x_633_, 3, v___x_632_);
lean_closure_set(v___x_633_, 4, v_fst_630_);
v___x_634_ = lean_apply_2(v_inst_625_, lean_box(0), v___x_633_);
v___f_635_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3), 3, 2);
lean_closure_set(v___f_635_, 0, v_snd_631_);
lean_closure_set(v___f_635_, 1, v_toPure_626_);
lean_inc(v_toBind_627_);
v___x_636_ = lean_apply_4(v_toBind_627_, lean_box(0), lean_box(0), v___x_634_, v___f_635_);
v___x_637_ = lean_apply_4(v_toBind_627_, lean_box(0), lean_box(0), v___x_636_, v___f_628_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___boxed(lean_object* v_fst_638_, lean_object* v_opts_639_, lean_object* v_leanOpts_640_, lean_object* v_reconfigure_641_, lean_object* v_inst_642_, lean_object* v_toPure_643_, lean_object* v_toBind_644_, lean_object* v___f_645_, lean_object* v_____x_646_){
_start:
{
uint8_t v_reconfigure_boxed_647_; lean_object* v_res_648_; 
v_reconfigure_boxed_647_ = lean_unbox(v_reconfigure_641_);
v_res_648_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(v_fst_638_, v_opts_639_, v_leanOpts_640_, v_reconfigure_boxed_647_, v_inst_642_, v_toPure_643_, v_toBind_644_, v___f_645_, v_____x_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v___x_649_, lean_object* v_toPure_650_, lean_object* v_____x_651_){
_start:
{
lean_object* v_snd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_snd_652_ = lean_ctor_get(v_____x_651_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_____x_651_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v_____x_651_, 0);
lean_dec(v_unused_661_);
v___x_654_ = v_____x_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_652_);
lean_dec(v_____x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_649_);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_snd_652_);
v___x_657_ = v_reuseFailAlloc_659_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_apply_2(v_toPure_650_, lean_box(0), v___x_657_);
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_a_662_, lean_object* v_leanOpts_663_, uint8_t v_reconfigure_664_, lean_object* v_inst_665_, lean_object* v_toPure_666_, lean_object* v_toBind_667_, lean_object* v___f_668_, lean_object* v_____x_669_){
_start:
{
lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_686_; 
v_fst_670_ = lean_ctor_get(v_____x_669_, 0);
v_snd_671_ = lean_ctor_get(v_____x_669_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_____x_669_);
if (v_isSharedCheck_686_ == 0)
{
v___x_673_ = v_____x_669_;
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_671_);
lean_inc(v_fst_670_);
lean_dec(v_____x_669_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_686_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_opts_675_; lean_object* v___x_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___f_679_; lean_object* v___x_681_; 
v_opts_675_ = lean_ctor_get(v_a_662_, 4);
lean_inc(v_opts_675_);
lean_dec_ref(v_a_662_);
v___x_676_ = lean_box(v_reconfigure_664_);
lean_inc(v_toBind_667_);
lean_inc_n(v_toPure_666_, 2);
v___f_677_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_677_, 0, v_fst_670_);
lean_closure_set(v___f_677_, 1, v_opts_675_);
lean_closure_set(v___f_677_, 2, v_leanOpts_663_);
lean_closure_set(v___f_677_, 3, v___x_676_);
lean_closure_set(v___f_677_, 4, v_inst_665_);
lean_closure_set(v___f_677_, 5, v_toPure_666_);
lean_closure_set(v___f_677_, 6, v_toBind_667_);
lean_closure_set(v___f_677_, 7, v___f_668_);
v___x_678_ = lean_box(0);
v___f_679_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5), 3, 2);
lean_closure_set(v___f_679_, 0, v___x_678_);
lean_closure_set(v___f_679_, 1, v_toPure_666_);
lean_inc(v_snd_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_snd_671_);
v___x_681_ = v___x_673_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_snd_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_snd_671_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_apply_2(v_toPure_666_, lean_box(0), v___x_681_);
lean_inc(v_toBind_667_);
v___x_683_ = lean_apply_4(v_toBind_667_, lean_box(0), lean_box(0), v___x_682_, v___f_677_);
v___x_684_ = lean_apply_4(v_toBind_667_, lean_box(0), lean_box(0), v___x_683_, v___f_679_);
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed(lean_object* v_a_687_, lean_object* v_leanOpts_688_, lean_object* v_reconfigure_689_, lean_object* v_inst_690_, lean_object* v_toPure_691_, lean_object* v_toBind_692_, lean_object* v___f_693_, lean_object* v_____x_694_){
_start:
{
uint8_t v_reconfigure_boxed_695_; lean_object* v_res_696_; 
v_reconfigure_boxed_695_ = lean_unbox(v_reconfigure_689_);
v_res_696_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(v_a_687_, v_leanOpts_688_, v_reconfigure_boxed_695_, v_inst_690_, v_toPure_691_, v_toBind_692_, v___f_693_, v_____x_694_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object* v_snd_697_, lean_object* v_toPure_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_a_699_);
lean_ctor_set(v___x_700_, 1, v_snd_697_);
v___x_701_ = lean_apply_2(v_toPure_698_, lean_box(0), v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object* v_resolve_702_, lean_object* v_pkg_703_, lean_object* v_a_704_, lean_object* v_toPure_705_, lean_object* v_toBind_706_, lean_object* v___f_707_, lean_object* v_____x_708_){
_start:
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_fst_709_ = lean_ctor_get(v_____x_708_, 0);
lean_inc(v_fst_709_);
v_snd_710_ = lean_ctor_get(v_____x_708_, 1);
lean_inc(v_snd_710_);
lean_dec_ref(v_____x_708_);
v___x_711_ = lean_apply_3(v_resolve_702_, v_pkg_703_, v_a_704_, v_fst_709_);
v___f_712_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 3, 2);
lean_closure_set(v___f_712_, 0, v_snd_710_);
lean_closure_set(v___f_712_, 1, v_toPure_705_);
lean_inc(v_toBind_706_);
v___x_713_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_711_, v___f_712_);
v___x_714_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_713_, v___f_707_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object* v_toPure_715_, lean_object* v_____x_716_){
_start:
{
lean_object* v_fst_717_; lean_object* v_snd_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_fst_717_ = lean_ctor_get(v_____x_716_, 0);
v_snd_718_ = lean_ctor_get(v_____x_716_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_____x_716_);
if (v_isSharedCheck_726_ == 0)
{
v___x_720_ = v_____x_716_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_snd_718_);
lean_inc(v_fst_717_);
lean_dec(v_____x_716_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_717_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_snd_718_);
v___x_723_ = v_reuseFailAlloc_725_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; 
v___x_724_ = lean_apply_2(v_toPure_715_, lean_box(0), v___x_723_);
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object* v_toPure_727_, lean_object* v_____x_728_){
_start:
{
lean_object* v_fst_729_; lean_object* v_snd_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
v_fst_729_ = lean_ctor_get(v_____x_728_, 0);
v_snd_730_ = lean_ctor_get(v_____x_728_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_____x_728_);
if (v_isSharedCheck_738_ == 0)
{
v___x_732_ = v_____x_728_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_730_);
lean_inc(v_fst_729_);
lean_dec(v_____x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_fst_729_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_snd_730_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; 
v___x_736_ = lean_apply_2(v_toPure_727_, lean_box(0), v___x_735_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object* v_toPure_739_, lean_object* v_toBind_740_, lean_object* v___f_741_, lean_object* v_____r_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc_n(v_toPure_739_, 2);
v___f_745_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9), 2, 1);
lean_closure_set(v___f_745_, 0, v_toPure_739_);
v___f_746_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10), 2, 1);
lean_closure_set(v___f_746_, 0, v_toPure_739_);
lean_inc_ref(v___y_744_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___y_744_);
lean_ctor_set(v___x_747_, 1, v___y_744_);
v___x_748_ = lean_apply_2(v_toPure_739_, lean_box(0), v___x_747_);
lean_inc_n(v_toBind_740_, 2);
v___x_749_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_748_, v___f_746_);
v___x_750_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_749_, v___f_745_);
v___x_751_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_750_, v___f_741_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11___boxed(lean_object* v_toPure_752_, lean_object* v_toBind_753_, lean_object* v___f_754_, lean_object* v_____r_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(v_toPure_752_, v_toBind_753_, v___f_754_, v_____r_755_, v___y_756_, v___y_757_);
lean_dec(v___y_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12(lean_object* v___f_759_, lean_object* v___y_760_, lean_object* v_____x_761_){
_start:
{
lean_object* v_fst_762_; lean_object* v_snd_763_; lean_object* v___x_764_; 
v_fst_762_ = lean_ctor_get(v_____x_761_, 0);
lean_inc(v_fst_762_);
v_snd_763_ = lean_ctor_get(v_____x_761_, 1);
lean_inc(v_snd_763_);
lean_dec_ref(v_____x_761_);
lean_inc(v___y_760_);
v___x_764_ = lean_apply_3(v___f_759_, v_fst_762_, v___y_760_, v_snd_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12___boxed(lean_object* v___f_765_, lean_object* v___y_766_, lean_object* v_____x_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12(v___f_765_, v___y_766_, v_____x_767_);
lean_dec(v___y_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object* v_snd_769_, lean_object* v_toPure_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_a_771_);
lean_ctor_set(v___x_772_, 1, v_snd_769_);
v___x_773_ = lean_apply_2(v_toPure_770_, lean_box(0), v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14(lean_object* v_pkg_794_, lean_object* v_a_795_, lean_object* v___f_796_, lean_object* v___y_797_, lean_object* v_inst_798_, lean_object* v_toPure_799_, lean_object* v_toBind_800_, lean_object* v___f_801_, lean_object* v___f_802_, lean_object* v_____x_803_){
_start:
{
lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_838_; 
v_fst_804_ = lean_ctor_get(v_____x_803_, 0);
v_snd_805_ = lean_ctor_get(v_____x_803_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_____x_803_);
if (v_isSharedCheck_838_ == 0)
{
v___x_807_ = v_____x_803_;
v_isShared_808_ = v_isSharedCheck_838_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_inc(v_fst_804_);
lean_dec(v_____x_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_838_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint8_t v___y_810_; lean_object* v_packages_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_packages_823_ = lean_ctor_get(v_fst_804_, 5);
lean_inc_ref(v_packages_823_);
lean_dec(v_fst_804_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_array_get_size(v_packages_823_);
v___x_826_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__10));
v___x_827_ = lean_nat_dec_lt(v___x_824_, v___x_825_);
if (v___x_827_ == 0)
{
lean_dec_ref(v_packages_823_);
lean_del_object(v___x_807_);
lean_dec_ref(v___f_802_);
v___y_810_ = v___x_827_;
goto v___jp_809_;
}
else
{
if (v___x_827_ == 0)
{
lean_dec_ref(v_packages_823_);
lean_del_object(v___x_807_);
lean_dec_ref(v___f_802_);
v___y_810_ = v___x_827_;
goto v___jp_809_;
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_828_ = ((size_t)0ULL);
v___x_829_ = lean_usize_of_nat(v___x_825_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_826_, v___f_802_, v_packages_823_, v___x_828_, v___x_829_);
v___x_831_ = lean_unbox(v___x_830_);
if (v___x_831_ == 0)
{
uint8_t v___x_832_; 
lean_del_object(v___x_807_);
v___x_832_ = lean_unbox(v___x_830_);
lean_dec(v___x_830_);
v___y_810_ = v___x_832_;
goto v___jp_809_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v___x_830_);
lean_dec(v___f_801_);
lean_dec(v_toBind_800_);
lean_dec(v_inst_798_);
lean_dec(v___f_796_);
lean_dec_ref(v_pkg_794_);
v___x_833_ = lean_box(0);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_833_);
v___x_835_ = v___x_807_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_snd_805_);
v___x_835_ = v_reuseFailAlloc_837_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; 
v___x_836_ = lean_apply_2(v_toPure_799_, lean_box(0), v___x_835_);
return v___x_836_;
}
}
}
}
v___jp_809_:
{
lean_object* v_baseName_811_; lean_object* v_name_812_; uint8_t v___x_813_; 
v_baseName_811_ = lean_ctor_get(v_pkg_794_, 1);
lean_inc(v_baseName_811_);
lean_dec_ref(v_pkg_794_);
v_name_812_ = lean_ctor_get(v_a_795_, 0);
v___x_813_ = lean_name_eq(v_baseName_811_, v_name_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v_baseName_811_);
lean_dec(v___f_801_);
lean_dec(v_toBind_800_);
lean_dec(v_toPure_799_);
lean_dec(v_inst_798_);
v___x_814_ = lean_box(0);
lean_inc(v___y_797_);
v___x_815_ = lean_apply_3(v___f_796_, v___x_814_, v___y_797_, v_snd_805_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v___f_796_);
v___x_816_ = l_Lean_Name_toString(v_baseName_811_, v___y_810_);
v___x_817_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__0));
v___x_818_ = lean_string_append(v___x_816_, v___x_817_);
v___x_819_ = lean_apply_2(v_inst_798_, lean_box(0), v___x_818_);
v___f_820_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13), 3, 2);
lean_closure_set(v___f_820_, 0, v_snd_805_);
lean_closure_set(v___f_820_, 1, v_toPure_799_);
lean_inc(v_toBind_800_);
v___x_821_ = lean_apply_4(v_toBind_800_, lean_box(0), lean_box(0), v___x_819_, v___f_820_);
v___x_822_ = lean_apply_4(v_toBind_800_, lean_box(0), lean_box(0), v___x_821_, v___f_801_);
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___boxed(lean_object* v_pkg_839_, lean_object* v_a_840_, lean_object* v___f_841_, lean_object* v___y_842_, lean_object* v_inst_843_, lean_object* v_toPure_844_, lean_object* v_toBind_845_, lean_object* v___f_846_, lean_object* v___f_847_, lean_object* v_____x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14(v_pkg_839_, v_a_840_, v___f_841_, v___y_842_, v_inst_843_, v_toPure_844_, v_toBind_845_, v___f_846_, v___f_847_, v_____x_848_);
lean_dec(v___y_842_);
lean_dec_ref(v_a_840_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__17(lean_object* v_leanOpts_850_, uint8_t v_reconfigure_851_, lean_object* v_inst_852_, lean_object* v_toPure_853_, lean_object* v_toBind_854_, lean_object* v___f_855_, lean_object* v_resolve_856_, lean_object* v_pkg_857_, lean_object* v_inst_858_, lean_object* v_a_859_, lean_object* v_x_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_inc_ref_n(v_a_859_, 3);
v___f_863_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_863_, 0, v_a_859_);
v___x_864_ = lean_box(v_reconfigure_851_);
lean_inc_n(v_toBind_854_, 6);
lean_inc_n(v_toPure_853_, 6);
v___f_865_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_865_, 0, v_a_859_);
lean_closure_set(v___f_865_, 1, v_leanOpts_850_);
lean_closure_set(v___f_865_, 2, v___x_864_);
lean_closure_set(v___f_865_, 3, v_inst_852_);
lean_closure_set(v___f_865_, 4, v_toPure_853_);
lean_closure_set(v___f_865_, 5, v_toBind_854_);
lean_closure_set(v___f_865_, 6, v___f_855_);
lean_inc_ref(v_pkg_857_);
v___f_866_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8), 7, 6);
lean_closure_set(v___f_866_, 0, v_resolve_856_);
lean_closure_set(v___f_866_, 1, v_pkg_857_);
lean_closure_set(v___f_866_, 2, v_a_859_);
lean_closure_set(v___f_866_, 3, v_toPure_853_);
lean_closure_set(v___f_866_, 4, v_toBind_854_);
lean_closure_set(v___f_866_, 5, v___f_865_);
v___f_867_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11___boxed), 6, 3);
lean_closure_set(v___f_867_, 0, v_toPure_853_);
lean_closure_set(v___f_867_, 1, v_toBind_854_);
lean_closure_set(v___f_867_, 2, v___f_866_);
lean_inc_n(v___y_861_, 2);
lean_inc_ref(v___f_867_);
v___f_868_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__12___boxed), 3, 2);
lean_closure_set(v___f_868_, 0, v___f_867_);
lean_closure_set(v___f_868_, 1, v___y_861_);
v___f_869_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___boxed), 10, 9);
lean_closure_set(v___f_869_, 0, v_pkg_857_);
lean_closure_set(v___f_869_, 1, v_a_859_);
lean_closure_set(v___f_869_, 2, v___f_867_);
lean_closure_set(v___f_869_, 3, v___y_861_);
lean_closure_set(v___f_869_, 4, v_inst_858_);
lean_closure_set(v___f_869_, 5, v_toPure_853_);
lean_closure_set(v___f_869_, 6, v_toBind_854_);
lean_closure_set(v___f_869_, 7, v___f_868_);
lean_closure_set(v___f_869_, 8, v___f_863_);
v___f_870_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9), 2, 1);
lean_closure_set(v___f_870_, 0, v_toPure_853_);
v___f_871_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10), 2, 1);
lean_closure_set(v___f_871_, 0, v_toPure_853_);
lean_inc_ref(v___y_862_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___y_862_);
lean_ctor_set(v___x_872_, 1, v___y_862_);
v___x_873_ = lean_apply_2(v_toPure_853_, lean_box(0), v___x_872_);
v___x_874_ = lean_apply_4(v_toBind_854_, lean_box(0), lean_box(0), v___x_873_, v___f_871_);
v___x_875_ = lean_apply_4(v_toBind_854_, lean_box(0), lean_box(0), v___x_874_, v___f_870_);
v___x_876_ = lean_apply_4(v_toBind_854_, lean_box(0), lean_box(0), v___x_875_, v___f_869_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__17___boxed(lean_object* v_leanOpts_877_, lean_object* v_reconfigure_878_, lean_object* v_inst_879_, lean_object* v_toPure_880_, lean_object* v_toBind_881_, lean_object* v___f_882_, lean_object* v_resolve_883_, lean_object* v_pkg_884_, lean_object* v_inst_885_, lean_object* v_a_886_, lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v_reconfigure_boxed_890_; lean_object* v_res_891_; 
v_reconfigure_boxed_890_ = lean_unbox(v_reconfigure_878_);
v_res_891_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__17(v_leanOpts_877_, v_reconfigure_boxed_890_, v_inst_879_, v_toPure_880_, v_toBind_881_, v___f_882_, v_resolve_883_, v_pkg_884_, v_inst_885_, v_a_886_, v_x_887_, v___y_888_, v___y_889_);
lean_dec(v___y_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__15(lean_object* v_recurse_892_, lean_object* v_x_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_897_; 
lean_inc(v___y_895_);
v___x_897_ = lean_apply_3(v_recurse_892_, v___y_894_, v___y_895_, v___y_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__15___boxed(lean_object* v_recurse_898_, lean_object* v_x_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__15(v_recurse_898_, v_x_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__16(lean_object* v___x_904_, lean_object* v_toPure_905_, lean_object* v___x_906_, lean_object* v___f_907_, lean_object* v_a_908_, lean_object* v_____x_909_){
_start:
{
lean_object* v_fst_910_; lean_object* v_snd_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_936_; 
v_fst_910_ = lean_ctor_get(v_____x_909_, 0);
v_snd_911_ = lean_ctor_get(v_____x_909_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_____x_909_);
if (v_isSharedCheck_936_ == 0)
{
v___x_913_ = v_____x_909_;
v_isShared_914_ = v_isSharedCheck_936_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snd_911_);
lean_inc(v_fst_910_);
lean_dec(v_____x_909_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_936_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_packages_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_packages_915_ = lean_ctor_get(v_fst_910_, 5);
lean_inc_ref(v_packages_915_);
lean_dec(v_fst_910_);
v___x_916_ = lean_array_get_size(v_packages_915_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_nat_dec_lt(v___x_904_, v___x_916_);
if (v___x_918_ == 0)
{
lean_object* v___x_920_; 
lean_dec_ref(v_packages_915_);
lean_dec(v___f_907_);
lean_dec_ref(v___x_906_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_917_);
v___x_920_ = v___x_913_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_snd_911_);
v___x_920_ = v_reuseFailAlloc_922_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_apply_2(v_toPure_905_, lean_box(0), v___x_920_);
return v___x_921_;
}
}
else
{
uint8_t v___x_923_; 
v___x_923_ = lean_nat_dec_le(v___x_916_, v___x_916_);
if (v___x_923_ == 0)
{
if (v___x_918_ == 0)
{
lean_object* v___x_925_; 
lean_dec_ref(v_packages_915_);
lean_dec(v___f_907_);
lean_dec_ref(v___x_906_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_917_);
v___x_925_ = v___x_913_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_snd_911_);
v___x_925_ = v_reuseFailAlloc_927_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; 
v___x_926_ = lean_apply_2(v_toPure_905_, lean_box(0), v___x_925_);
return v___x_926_;
}
}
else
{
size_t v___x_928_; size_t v___x_929_; lean_object* v___x_8416__overap_930_; lean_object* v___x_931_; 
lean_del_object(v___x_913_);
lean_dec(v_toPure_905_);
v___x_928_ = lean_usize_of_nat(v___x_904_);
v___x_929_ = lean_usize_of_nat(v___x_916_);
v___x_8416__overap_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_906_, v___f_907_, v_packages_915_, v___x_928_, v___x_929_, v___x_917_);
lean_inc(v_a_908_);
v___x_931_ = lean_apply_2(v___x_8416__overap_930_, v_a_908_, v_snd_911_);
return v___x_931_;
}
}
else
{
size_t v___x_932_; size_t v___x_933_; lean_object* v___x_8419__overap_934_; lean_object* v___x_935_; 
lean_del_object(v___x_913_);
lean_dec(v_toPure_905_);
v___x_932_ = lean_usize_of_nat(v___x_904_);
v___x_933_ = lean_usize_of_nat(v___x_916_);
v___x_8419__overap_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_906_, v___f_907_, v_packages_915_, v___x_932_, v___x_933_, v___x_917_);
lean_inc(v_a_908_);
v___x_935_ = lean_apply_2(v___x_8419__overap_934_, v_a_908_, v_snd_911_);
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__16___boxed(lean_object* v___x_937_, lean_object* v_toPure_938_, lean_object* v___x_939_, lean_object* v___f_940_, lean_object* v_a_941_, lean_object* v_____x_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__16(v___x_937_, v_toPure_938_, v___x_939_, v___f_940_, v_a_941_, v_____x_942_);
lean_dec(v_a_941_);
lean_dec(v___x_937_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__20(lean_object* v_toPure_944_, lean_object* v_toBind_945_, lean_object* v___f_946_, lean_object* v_____x_947_){
_start:
{
lean_object* v_snd_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_961_; 
v_snd_948_ = lean_ctor_get(v_____x_947_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_____x_947_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_____x_947_, 0);
lean_dec(v_unused_962_);
v___x_950_ = v_____x_947_;
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_948_);
lean_dec(v_____x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___x_955_; 
lean_inc_n(v_toPure_944_, 2);
v___f_952_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9), 2, 1);
lean_closure_set(v___f_952_, 0, v_toPure_944_);
v___f_953_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10), 2, 1);
lean_closure_set(v___f_953_, 0, v_toPure_944_);
lean_inc(v_snd_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_snd_948_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_snd_948_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_snd_948_);
v___x_955_ = v_reuseFailAlloc_960_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_956_ = lean_apply_2(v_toPure_944_, lean_box(0), v___x_955_);
lean_inc_n(v_toBind_945_, 2);
v___x_957_ = lean_apply_4(v_toBind_945_, lean_box(0), lean_box(0), v___x_956_, v___f_953_);
v___x_958_ = lean_apply_4(v_toBind_945_, lean_box(0), lean_box(0), v___x_957_, v___f_952_);
v___x_959_ = lean_apply_4(v_toBind_945_, lean_box(0), lean_box(0), v___x_958_, v___f_946_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__18(lean_object* v_pkg_963_, lean_object* v_toPure_964_, lean_object* v___x_965_, lean_object* v___f_966_, lean_object* v_a_967_, lean_object* v_toBind_968_, lean_object* v___f_969_, lean_object* v_____x_970_){
_start:
{
lean_object* v_fst_971_; lean_object* v_snd_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_995_; 
v_fst_971_ = lean_ctor_get(v_____x_970_, 0);
v_snd_972_ = lean_ctor_get(v_____x_970_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_____x_970_);
if (v_isSharedCheck_995_ == 0)
{
v___x_974_ = v_____x_970_;
v_isShared_975_ = v_isSharedCheck_995_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snd_972_);
lean_inc(v_fst_971_);
lean_dec(v_____x_970_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_995_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_packages_976_; lean_object* v_depConfigs_977_; lean_object* v___x_978_; lean_object* v___f_979_; lean_object* v___f_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_packages_976_ = lean_ctor_get(v_fst_971_, 5);
lean_inc_ref(v_packages_976_);
lean_dec(v_fst_971_);
v_depConfigs_977_ = lean_ctor_get(v_pkg_963_, 12);
lean_inc_ref(v_depConfigs_977_);
lean_dec_ref(v_pkg_963_);
v___x_978_ = lean_array_get_size(v_packages_976_);
lean_dec_ref(v_packages_976_);
lean_inc(v_a_967_);
lean_inc_ref(v___x_965_);
lean_inc_n(v_toPure_964_, 2);
v___f_979_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__16___boxed), 6, 5);
lean_closure_set(v___f_979_, 0, v___x_978_);
lean_closure_set(v___f_979_, 1, v_toPure_964_);
lean_closure_set(v___f_979_, 2, v___x_965_);
lean_closure_set(v___f_979_, 3, v___f_966_);
lean_closure_set(v___f_979_, 4, v_a_967_);
lean_inc(v_toBind_968_);
v___f_980_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__20), 4, 3);
lean_closure_set(v___f_980_, 0, v_toPure_964_);
lean_closure_set(v___f_980_, 1, v_toBind_968_);
lean_closure_set(v___f_980_, 2, v___f_979_);
v___x_981_ = lean_array_get_size(v_depConfigs_977_);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = lean_box(0);
v___x_984_ = lean_nat_dec_lt(v___x_982_, v___x_981_);
if (v___x_984_ == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_depConfigs_977_);
lean_dec(v___f_969_);
lean_dec_ref(v___x_965_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_983_);
v___x_986_ = v___x_974_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_snd_972_);
v___x_986_ = v_reuseFailAlloc_989_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_apply_2(v_toPure_964_, lean_box(0), v___x_986_);
v___x_988_ = lean_apply_4(v_toBind_968_, lean_box(0), lean_box(0), v___x_987_, v___f_980_);
return v___x_988_;
}
}
else
{
size_t v___x_990_; size_t v___x_991_; lean_object* v___x_8459__overap_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_del_object(v___x_974_);
lean_dec(v_toPure_964_);
v___x_990_ = lean_usize_of_nat(v___x_981_);
v___x_991_ = ((size_t)0ULL);
v___x_8459__overap_992_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_965_, v___f_969_, v_depConfigs_977_, v___x_990_, v___x_991_, v___x_983_);
lean_inc(v_a_967_);
v___x_993_ = lean_apply_2(v___x_8459__overap_992_, v_a_967_, v_snd_972_);
v___x_994_ = lean_apply_4(v_toBind_968_, lean_box(0), lean_box(0), v___x_993_, v___f_980_);
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__18___boxed(lean_object* v_pkg_996_, lean_object* v_toPure_997_, lean_object* v___x_998_, lean_object* v___f_999_, lean_object* v_a_1000_, lean_object* v_toBind_1001_, lean_object* v___f_1002_, lean_object* v_____x_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__18(v_pkg_996_, v_toPure_997_, v___x_998_, v___f_999_, v_a_1000_, v_toBind_1001_, v___f_1002_, v_____x_1003_);
lean_dec(v_a_1000_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_resolve_1008_, lean_object* v_leanOpts_1009_, uint8_t v_reconfigure_1010_, lean_object* v_pkg_1011_, lean_object* v_recurse_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_toApplicative_1026_; lean_object* v_toBind_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1046_; 
lean_inc_ref_n(v_inst_1005_, 7);
v___f_1015_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1015_, 0, v_inst_1005_);
v___f_1016_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1016_, 0, v_inst_1005_);
v___f_1017_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1017_, 0, v_inst_1005_);
v___f_1018_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1018_, 0, v_inst_1005_);
v___x_1019_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1019_, 0, lean_box(0));
lean_closure_set(v___x_1019_, 1, lean_box(0));
lean_closure_set(v___x_1019_, 2, v_inst_1005_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___f_1015_);
v___x_1021_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1021_, 0, lean_box(0));
lean_closure_set(v___x_1021_, 1, lean_box(0));
lean_closure_set(v___x_1021_, 2, v_inst_1005_);
v___x_1022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
lean_ctor_set(v___x_1022_, 2, v___f_1016_);
lean_ctor_set(v___x_1022_, 3, v___f_1017_);
lean_ctor_set(v___x_1022_, 4, v___f_1018_);
v___x_1023_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1023_, 0, lean_box(0));
lean_closure_set(v___x_1023_, 1, lean_box(0));
lean_closure_set(v___x_1023_, 2, v_inst_1005_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_ReaderT_instMonad___redArg(v___x_1024_);
v_toApplicative_1026_ = lean_ctor_get(v_inst_1005_, 0);
v_toBind_1027_ = lean_ctor_get(v_inst_1005_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_inst_1005_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1029_ = v_inst_1005_;
v_isShared_1030_ = v_isSharedCheck_1046_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_toBind_1027_);
lean_inc(v_toApplicative_1026_);
lean_dec(v_inst_1005_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1046_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_toPure_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1040_; 
v_toPure_1031_ = lean_ctor_get(v_toApplicative_1026_, 1);
lean_inc_n(v_toPure_1031_, 6);
lean_dec_ref(v_toApplicative_1026_);
lean_inc_n(v_toBind_1027_, 3);
v___f_1032_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1032_, 0, v_toPure_1031_);
lean_closure_set(v___f_1032_, 1, v_toBind_1027_);
v___x_1033_ = lean_box(v_reconfigure_1010_);
lean_inc_ref(v_pkg_1011_);
v___f_1034_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__17___boxed), 13, 9);
lean_closure_set(v___f_1034_, 0, v_leanOpts_1009_);
lean_closure_set(v___f_1034_, 1, v___x_1033_);
lean_closure_set(v___f_1034_, 2, v_inst_1007_);
lean_closure_set(v___f_1034_, 3, v_toPure_1031_);
lean_closure_set(v___f_1034_, 4, v_toBind_1027_);
lean_closure_set(v___f_1034_, 5, v___f_1032_);
lean_closure_set(v___f_1034_, 6, v_resolve_1008_);
lean_closure_set(v___f_1034_, 7, v_pkg_1011_);
lean_closure_set(v___f_1034_, 8, v_inst_1006_);
v___f_1035_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__15___boxed), 5, 1);
lean_closure_set(v___f_1035_, 0, v_recurse_1012_);
lean_inc(v_a_1013_);
v___f_1036_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__18___boxed), 8, 7);
lean_closure_set(v___f_1036_, 0, v_pkg_1011_);
lean_closure_set(v___f_1036_, 1, v_toPure_1031_);
lean_closure_set(v___f_1036_, 2, v___x_1025_);
lean_closure_set(v___f_1036_, 3, v___f_1035_);
lean_closure_set(v___f_1036_, 4, v_a_1013_);
lean_closure_set(v___f_1036_, 5, v_toBind_1027_);
lean_closure_set(v___f_1036_, 6, v___f_1034_);
v___f_1037_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1037_, 0, v_toPure_1031_);
v___f_1038_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10), 2, 1);
lean_closure_set(v___f_1038_, 0, v_toPure_1031_);
lean_inc_ref(v_a_1014_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 1, v_a_1014_);
lean_ctor_set(v___x_1029_, 0, v_a_1014_);
v___x_1040_ = v___x_1029_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1014_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_a_1014_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = lean_apply_2(v_toPure_1031_, lean_box(0), v___x_1040_);
lean_inc_n(v_toBind_1027_, 2);
v___x_1042_ = lean_apply_4(v_toBind_1027_, lean_box(0), lean_box(0), v___x_1041_, v___f_1038_);
v___x_1043_ = lean_apply_4(v_toBind_1027_, lean_box(0), lean_box(0), v___x_1042_, v___f_1037_);
v___x_1044_ = lean_apply_4(v_toBind_1027_, lean_box(0), lean_box(0), v___x_1043_, v___f_1036_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_resolve_1050_, lean_object* v_leanOpts_1051_, lean_object* v_reconfigure_1052_, lean_object* v_pkg_1053_, lean_object* v_recurse_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
uint8_t v_reconfigure_boxed_1057_; lean_object* v_res_1058_; 
v_reconfigure_boxed_1057_ = lean_unbox(v_reconfigure_1052_);
v_res_1058_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1047_, v_inst_1048_, v_inst_1049_, v_resolve_1050_, v_leanOpts_1051_, v_reconfigure_boxed_1057_, v_pkg_1053_, v_recurse_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v_resolve_1063_, lean_object* v_leanOpts_1064_, uint8_t v_reconfigure_1065_, lean_object* v_pkg_1066_, lean_object* v_recurse_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_1060_, v_inst_1061_, v_inst_1062_, v_resolve_1063_, v_leanOpts_1064_, v_reconfigure_1065_, v_pkg_1066_, v_recurse_1067_, v_a_1068_, v_a_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_resolve_1075_, lean_object* v_leanOpts_1076_, lean_object* v_reconfigure_1077_, lean_object* v_pkg_1078_, lean_object* v_recurse_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
uint8_t v_reconfigure_boxed_1082_; lean_object* v_res_1083_; 
v_reconfigure_boxed_1082_ = lean_unbox(v_reconfigure_1077_);
v_res_1083_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_1071_, v_inst_1072_, v_inst_1073_, v_inst_1074_, v_resolve_1075_, v_leanOpts_1076_, v_reconfigure_boxed_1082_, v_pkg_1078_, v_recurse_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_ws_1087_, lean_object* v_resolve_1088_, lean_object* v_root_1089_, lean_object* v_stack_1090_, lean_object* v_leanOpts_1091_, uint8_t v_reconfigure_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_box(v_reconfigure_1092_);
lean_inc(v_inst_1085_);
lean_inc_ref(v_inst_1084_);
v___x_1094_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed), 11, 7);
lean_closure_set(v___x_1094_, 0, lean_box(0));
lean_closure_set(v___x_1094_, 1, v_inst_1084_);
lean_closure_set(v___x_1094_, 2, v_inst_1085_);
lean_closure_set(v___x_1094_, 3, v_inst_1086_);
lean_closure_set(v___x_1094_, 4, v_resolve_1088_);
lean_closure_set(v___x_1094_, 5, v_leanOpts_1091_);
lean_closure_set(v___x_1094_, 6, v___x_1093_);
v___x_1095_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(v_inst_1084_, v_inst_1085_, v_ws_1087_, v___x_1094_, v_root_1089_, v_stack_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg___boxed(lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_ws_1099_, lean_object* v_resolve_1100_, lean_object* v_root_1101_, lean_object* v_stack_1102_, lean_object* v_leanOpts_1103_, lean_object* v_reconfigure_1104_){
_start:
{
uint8_t v_reconfigure_boxed_1105_; lean_object* v_res_1106_; 
v_reconfigure_boxed_1105_ = lean_unbox(v_reconfigure_1104_);
v_res_1106_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(v_inst_1096_, v_inst_1097_, v_inst_1098_, v_ws_1099_, v_resolve_1100_, v_root_1101_, v_stack_1102_, v_leanOpts_1103_, v_reconfigure_boxed_1105_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_ws_1111_, lean_object* v_resolve_1112_, lean_object* v_root_1113_, lean_object* v_stack_1114_, lean_object* v_leanOpts_1115_, uint8_t v_reconfigure_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_box(v_reconfigure_1116_);
lean_inc(v_inst_1109_);
lean_inc_ref(v_inst_1108_);
v___x_1118_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed), 11, 7);
lean_closure_set(v___x_1118_, 0, lean_box(0));
lean_closure_set(v___x_1118_, 1, v_inst_1108_);
lean_closure_set(v___x_1118_, 2, v_inst_1109_);
lean_closure_set(v___x_1118_, 3, v_inst_1110_);
lean_closure_set(v___x_1118_, 4, v_resolve_1112_);
lean_closure_set(v___x_1118_, 5, v_leanOpts_1115_);
lean_closure_set(v___x_1118_, 6, v___x_1117_);
v___x_1119_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(v_inst_1108_, v_inst_1109_, v_ws_1111_, v___x_1118_, v_root_1113_, v_stack_1114_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___boxed(lean_object* v_m_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_ws_1124_, lean_object* v_resolve_1125_, lean_object* v_root_1126_, lean_object* v_stack_1127_, lean_object* v_leanOpts_1128_, lean_object* v_reconfigure_1129_){
_start:
{
uint8_t v_reconfigure_boxed_1130_; lean_object* v_res_1131_; 
v_reconfigure_boxed_1130_ = lean_unbox(v_reconfigure_1129_);
v_res_1131_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(v_m_1120_, v_inst_1121_, v_inst_1122_, v_inst_1123_, v_ws_1124_, v_resolve_1125_, v_root_1126_, v_stack_1127_, v_leanOpts_1128_, v_reconfigure_boxed_1130_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_1132_, lean_object* v_init_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_apply_1(v_x_1132_, v_init_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_1135_, lean_object* v_00_u03b1_1136_, lean_object* v_x_1137_, lean_object* v_init_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_apply_1(v_x_1137_, v_init_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(lean_object* v_toUpdate_1140_, lean_object* v_as_1141_, size_t v_i_1142_, size_t v_stop_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_fst_1148_; lean_object* v_snd_1149_; uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_eq(v_i_1142_, v_stop_1143_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; uint8_t v_inherited_1157_; 
v___x_1156_ = lean_array_uget_borrowed(v_as_1141_, v_i_1142_);
v_inherited_1157_ = lean_ctor_get_uint8(v___x_1156_, sizeof(void*)*5);
if (v_inherited_1157_ == 0)
{
lean_object* v_name_1158_; uint8_t v___x_1159_; 
v_name_1158_ = lean_ctor_get(v___x_1156_, 0);
v___x_1159_ = l_Lean_NameSet_contains(v_toUpdate_1140_, v_name_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_box(0);
lean_inc(v___x_1156_);
lean_inc(v_name_1158_);
v___x_1161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1158_, v___x_1156_, v___y_1145_);
v_fst_1148_ = v___x_1160_;
v_snd_1149_ = v___x_1161_;
goto v___jp_1147_;
}
else
{
goto v___jp_1153_;
}
}
else
{
goto v___jp_1153_;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1144_);
lean_ctor_set(v___x_1162_, 1, v___y_1145_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
return v___x_1163_;
}
v___jp_1147_:
{
size_t v___x_1150_; size_t v___x_1151_; 
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1142_, v___x_1150_);
v_i_1142_ = v___x_1151_;
v_b_1144_ = v_fst_1148_;
v___y_1145_ = v_snd_1149_;
goto _start;
}
v___jp_1153_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_box(0);
v_fst_1148_ = v___x_1154_;
v_snd_1149_ = v___y_1145_;
goto v___jp_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg___boxed(lean_object* v_toUpdate_1164_, lean_object* v_as_1165_, lean_object* v_i_1166_, lean_object* v_stop_1167_, lean_object* v_b_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
size_t v_i_boxed_1171_; size_t v_stop_boxed_1172_; lean_object* v_res_1173_; 
v_i_boxed_1171_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_stop_boxed_1172_ = lean_unbox_usize(v_stop_1167_);
lean_dec(v_stop_1167_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1164_, v_as_1165_, v_i_boxed_1171_, v_stop_boxed_1172_, v_b_1168_, v___y_1169_);
lean_dec_ref(v_as_1165_);
lean_dec(v_toUpdate_1164_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_1174_, size_t v_i_1175_, size_t v_stop_1176_, lean_object* v_b_1177_, lean_object* v___y_1178_){
_start:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_usize_dec_eq(v_i_1175_, v_stop_1176_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; 
v___x_1181_ = lean_array_uget_borrowed(v_as_1174_, v_i_1175_);
lean_inc_ref(v___y_1178_);
lean_inc(v___x_1181_);
v___x_1182_ = lean_apply_2(v___y_1178_, v___x_1181_, lean_box(0));
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1175_, v___x_1183_);
v_i_1175_ = v___x_1184_;
v_b_1177_ = v___x_1182_;
goto _start;
}
else
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_b_1177_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_1187_, lean_object* v_i_1188_, lean_object* v_stop_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
size_t v_i_boxed_1193_; size_t v_stop_boxed_1194_; lean_object* v_res_1195_; 
v_i_boxed_1193_ = lean_unbox_usize(v_i_1188_);
lean_dec(v_i_1188_);
v_stop_boxed_1194_ = lean_unbox_usize(v_stop_1189_);
lean_dec(v_stop_1189_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_1187_, v_i_boxed_1193_, v_stop_boxed_1194_, v_b_1190_, v___y_1191_);
lean_dec_ref(v___y_1191_);
lean_dec_ref(v_as_1187_);
return v_res_1195_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1203_ = lean_array_get_size(v___x_1202_);
return v___x_1203_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1204_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_nat_dec_lt(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1208_ = lean_nat_dec_le(v___x_1207_, v___x_1207_);
return v___x_1208_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8(void){
_start:
{
lean_object* v___x_1209_; size_t v___x_1210_; 
v___x_1209_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_1210_ = lean_usize_of_nat(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_1213_, lean_object* v_toUpdate_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___y_1219_; lean_object* v___y_1224_; lean_object* v_fst_1225_; lean_object* v_snd_1226_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v_val_1250_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v_root_1299_; lean_object* v_baseName_1300_; lean_object* v_dir_1301_; lean_object* v_config_1302_; lean_object* v_relManifestFile_1303_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; uint8_t v_fst_1308_; lean_object* v_snd_1309_; lean_object* v_packagesDir_x3f_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1372_; lean_object* v___y_1373_; uint8_t v___x_1376_; lean_object* v_rootName_1377_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_val_1432_; lean_object* v___x_1458_; 
v_root_1299_ = lean_ctor_get(v_ws_1213_, 0);
lean_inc_ref(v_root_1299_);
lean_dec_ref(v_ws_1213_);
v_baseName_1300_ = lean_ctor_get(v_root_1299_, 1);
lean_inc(v_baseName_1300_);
v_dir_1301_ = lean_ctor_get(v_root_1299_, 4);
lean_inc_ref_n(v_dir_1301_, 2);
v_config_1302_ = lean_ctor_get(v_root_1299_, 6);
lean_inc_ref(v_config_1302_);
v_relManifestFile_1303_ = lean_ctor_get(v_root_1299_, 9);
lean_inc_ref(v_relManifestFile_1303_);
lean_dec_ref(v_root_1299_);
v___x_1376_ = 0;
v_rootName_1377_ = l_Lean_Name_toString(v_baseName_1300_, v___x_1376_);
v___x_1429_ = l_Lake_joinRelative(v_dir_1301_, v_relManifestFile_1303_);
v___x_1430_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1458_ = l_Lake_Manifest_load(v___x_1429_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 1);
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
v_val_1432_ = v___x_1464_;
goto v___jp_1431_;
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_a_1467_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1458_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1458_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set_tag(v___x_1469_, 0);
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
v_val_1432_ = v___x_1472_;
goto v___jp_1431_;
}
}
}
v___jp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___y_1219_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
v___jp_1223_:
{
if (lean_obj_tag(v_fst_1225_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_snd_1226_);
v_a_1227_ = lean_ctor_get(v_fst_1225_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_fst_1225_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1229_ = v_fst_1225_;
v_isShared_1230_ = v_isSharedCheck_1241_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v_fst_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1241_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1231_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_1232_ = lean_io_error_to_string(v_a_1227_);
v___x_1233_ = lean_string_append(v___x_1231_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = 3;
v___x_1235_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*1, v___x_1234_);
lean_inc_ref(v___y_1224_);
v___x_1236_ = lean_apply_2(v___y_1224_, v___x_1235_, lean_box(0));
v___x_1237_ = lean_box(0);
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 1);
lean_ctor_set(v___x_1229_, 0, v___x_1237_);
v___x_1239_ = v___x_1229_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_fst_1225_);
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_snd_1226_);
v___x_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
return v___x_1244_;
}
}
v___jp_1245_:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_array_get_size(v___y_1247_);
v___x_1252_ = lean_nat_dec_lt(v___y_1246_, v___x_1251_);
if (v___x_1252_ == 0)
{
v___y_1224_ = v___y_1248_;
v_fst_1225_ = v_val_1250_;
v_snd_1226_ = v___y_1249_;
goto v___jp_1223_;
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = lean_nat_dec_le(v___x_1251_, v___x_1251_);
if (v___x_1254_ == 0)
{
if (v___x_1252_ == 0)
{
v___y_1224_ = v___y_1248_;
v_fst_1225_ = v_val_1250_;
v_snd_1226_ = v___y_1249_;
goto v___jp_1223_;
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = lean_usize_of_nat(v___x_1251_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1247_, v___x_1255_, v___x_1256_, v___x_1253_, v___y_1248_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_dec_ref(v___x_1257_);
v___y_1224_ = v___y_1248_;
v_fst_1225_ = v_val_1250_;
v_snd_1226_ = v___y_1249_;
goto v___jp_1223_;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v_val_1250_);
lean_dec(v___y_1249_);
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
size_t v___x_1266_; size_t v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = ((size_t)0ULL);
v___x_1267_ = lean_usize_of_nat(v___x_1251_);
v___x_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1247_, v___x_1266_, v___x_1267_, v___x_1253_, v___y_1248_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_dec_ref(v___x_1268_);
v___y_1224_ = v___y_1248_;
v_fst_1225_ = v_val_1250_;
v_snd_1226_ = v___y_1249_;
goto v___jp_1223_;
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_val_1250_);
lean_dec(v___y_1249_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
v___jp_1277_:
{
if (lean_obj_tag(v___y_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___y_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___y_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___y_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___y_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 1);
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v___y_1246_ = v___y_1278_;
v___y_1247_ = v___y_1279_;
v___y_1248_ = v___y_1280_;
v___y_1249_ = v___y_1281_;
v_val_1250_ = v___x_1288_;
goto v___jp_1245_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___y_1282_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1282_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___y_1282_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___y_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 0);
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
v___y_1246_ = v___y_1278_;
v___y_1247_ = v___y_1279_;
v___y_1248_ = v___y_1280_;
v___y_1249_ = v___y_1281_;
v_val_1250_ = v___x_1296_;
goto v___jp_1245_;
}
}
}
}
v___jp_1304_:
{
lean_object* v_toWorkspaceConfig_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_toWorkspaceConfig_1310_ = lean_ctor_get(v_config_1302_, 0);
lean_inc_ref(v_toWorkspaceConfig_1310_);
lean_dec_ref(v_config_1302_);
v___x_1311_ = l_System_FilePath_normalize(v___y_1307_);
v___x_1312_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1310_);
lean_inc_ref(v___x_1312_);
v___x_1313_ = l_System_FilePath_normalize(v___x_1312_);
v___x_1314_ = lean_string_dec_eq(v___x_1311_, v___x_1313_);
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___x_1311_);
if (v___x_1314_ == 0)
{
if (v_fst_1308_ == 0)
{
lean_dec_ref(v___x_1312_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v_dir_1301_);
v___y_1219_ = v_snd_1309_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1315_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_1316_ = lean_string_append(v___x_1315_, v___y_1305_);
v___x_1317_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_1318_ = lean_string_append(v___x_1316_, v___x_1317_);
v___x_1319_ = l_Lake_joinRelative(v_dir_1301_, v___x_1312_);
v___x_1320_ = lean_string_append(v___x_1318_, v___x_1319_);
v___x_1321_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1322_ = lean_string_append(v___x_1320_, v___x_1321_);
v___x_1323_ = 1;
v___x_1324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*1, v___x_1323_);
lean_inc_ref(v___y_1306_);
v___x_1325_ = lean_apply_2(v___y_1306_, v___x_1324_, lean_box(0));
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_1319_);
v___x_1328_ = l_Lake_createParentDirs(v___x_1319_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___x_1329_; 
lean_dec_ref(v___x_1328_);
v___x_1329_ = lean_io_rename(v___y_1305_, v___x_1319_);
lean_dec_ref(v___x_1319_);
lean_dec_ref(v___y_1305_);
v___y_1278_ = v___x_1326_;
v___y_1279_ = v___x_1327_;
v___y_1280_ = v___y_1306_;
v___y_1281_ = v_snd_1309_;
v___y_1282_ = v___x_1329_;
goto v___jp_1277_;
}
else
{
lean_dec_ref(v___x_1319_);
lean_dec_ref(v___y_1305_);
v___y_1278_ = v___x_1326_;
v___y_1279_ = v___x_1327_;
v___y_1280_ = v___y_1306_;
v___y_1281_ = v_snd_1309_;
v___y_1282_ = v___x_1328_;
goto v___jp_1277_;
}
}
}
else
{
lean_dec_ref(v___x_1312_);
lean_dec_ref(v___y_1305_);
lean_dec_ref(v_dir_1301_);
v___y_1219_ = v_snd_1309_;
goto v___jp_1218_;
}
}
v___jp_1330_:
{
if (lean_obj_tag(v_packagesDir_x3f_1331_) == 1)
{
lean_object* v_val_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_val_1334_ = lean_ctor_get(v_packagesDir_x3f_1331_, 0);
lean_inc_n(v_val_1334_, 2);
lean_dec_ref(v_packagesDir_x3f_1331_);
lean_inc_ref(v_dir_1301_);
v___x_1335_ = l_Lake_joinRelative(v_dir_1301_, v_val_1334_);
v___x_1336_ = l_System_FilePath_pathExists(v___x_1335_);
v___x_1337_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_1338_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1338_ == 0)
{
v___y_1305_ = v___x_1335_;
v___y_1306_ = v___y_1333_;
v___y_1307_ = v_val_1334_;
v_fst_1308_ = v___x_1336_;
v_snd_1309_ = v___y_1332_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1340_ == 0)
{
if (v___x_1338_ == 0)
{
v___y_1305_ = v___x_1335_;
v___y_1306_ = v___y_1333_;
v___y_1307_ = v_val_1334_;
v_fst_1308_ = v___x_1336_;
v_snd_1309_ = v___y_1332_;
goto v___jp_1304_;
}
else
{
size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1337_, v___x_1341_, v___x_1342_, v___x_1339_, v___y_1333_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref(v___x_1343_);
v___y_1305_ = v___x_1335_;
v___y_1306_ = v___y_1333_;
v___y_1307_ = v_val_1334_;
v_fst_1308_ = v___x_1336_;
v_snd_1309_ = v___y_1332_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v___x_1335_);
lean_dec(v_val_1334_);
lean_dec(v___y_1332_);
lean_dec_ref(v_config_1302_);
lean_dec_ref(v_dir_1301_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
else
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1337_, v___x_1352_, v___x_1353_, v___x_1339_, v___y_1333_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_dec_ref(v___x_1354_);
v___y_1305_ = v___x_1335_;
v___y_1306_ = v___y_1333_;
v___y_1307_ = v_val_1334_;
v_fst_1308_ = v___x_1336_;
v_snd_1309_ = v___y_1332_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v___x_1335_);
lean_dec(v_val_1334_);
lean_dec(v___y_1332_);
lean_dec_ref(v_config_1302_);
lean_dec_ref(v_dir_1301_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
else
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_packagesDir_x3f_1331_);
lean_dec_ref(v_config_1302_);
lean_dec_ref(v_dir_1301_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___y_1332_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
v___jp_1366_:
{
lean_object* v_packagesDir_x3f_1370_; 
v_packagesDir_x3f_1370_ = lean_ctor_get(v___y_1367_, 2);
lean_inc(v_packagesDir_x3f_1370_);
lean_dec_ref(v___y_1367_);
v_packagesDir_x3f_1331_ = v_packagesDir_x3f_1370_;
v___y_1332_ = v___y_1368_;
v___y_1333_ = v___y_1369_;
goto v___jp_1330_;
}
v___jp_1371_:
{
if (lean_obj_tag(v___y_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v_snd_1375_; 
v_a_1374_ = lean_ctor_get(v___y_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___y_1373_);
v_snd_1375_ = lean_ctor_get(v_a_1374_, 1);
lean_inc(v_snd_1375_);
lean_dec(v_a_1374_);
v___y_1367_ = v___y_1372_;
v___y_1368_ = v_snd_1375_;
v___y_1369_ = v_a_1216_;
goto v___jp_1366_;
}
else
{
lean_dec_ref(v___y_1372_);
lean_dec_ref(v_config_1302_);
lean_dec_ref(v_dir_1301_);
return v___y_1373_;
}
}
v___jp_1378_:
{
if (lean_obj_tag(v_fst_1379_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v_config_1302_);
lean_dec_ref(v_dir_1301_);
v_a_1381_ = lean_ctor_get(v_fst_1379_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_fst_1379_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1383_ = v_fst_1379_;
v_isShared_1384_ = v_isSharedCheck_1413_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v_fst_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1413_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
if (lean_obj_tag(v_a_1381_) == 11)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec_ref(v_a_1381_);
v___x_1385_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_1386_ = lean_string_append(v_rootName_1377_, v___x_1385_);
v___x_1387_ = 1;
v___x_1388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*1, v___x_1387_);
lean_inc_ref(v_a_1216_);
v___x_1389_ = lean_apply_2(v_a_1216_, v___x_1388_, lean_box(0));
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v_snd_1380_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1390_);
v___x_1392_ = v___x_1383_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_1214_) == 0)
{
lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_dec(v_snd_1380_);
lean_dec_ref(v_rootName_1377_);
v___x_1394_ = lean_io_error_to_string(v_a_1381_);
v___x_1395_ = 3;
v___x_1396_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*1, v___x_1395_);
lean_inc_ref(v_a_1216_);
v___x_1397_ = lean_apply_2(v_a_1216_, v___x_1396_, lean_box(0));
v___x_1398_ = lean_box(0);
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 1);
lean_ctor_set(v___x_1383_, 0, v___x_1398_);
v___x_1400_ = v___x_1383_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1402_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_1403_ = lean_string_append(v_rootName_1377_, v___x_1402_);
v___x_1404_ = lean_io_error_to_string(v_a_1381_);
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = 2;
v___x_1407_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set_uint8(v___x_1407_, sizeof(void*)*1, v___x_1406_);
lean_inc_ref(v_a_1216_);
v___x_1408_ = lean_apply_2(v_a_1216_, v___x_1407_, lean_box(0));
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_snd_1380_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1409_);
v___x_1411_ = v___x_1383_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_1377_);
if (lean_obj_tag(v_toUpdate_1214_) == 0)
{
lean_object* v_a_1414_; lean_object* v_packagesDir_x3f_1415_; lean_object* v_packages_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_a_1414_ = lean_ctor_get(v_fst_1379_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v_fst_1379_);
v_packagesDir_x3f_1415_ = lean_ctor_get(v_a_1414_, 2);
v_packages_1416_ = lean_ctor_get(v_a_1414_, 3);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_array_get_size(v_packages_1416_);
v___x_1419_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_inc(v_packagesDir_x3f_1415_);
lean_dec(v_a_1414_);
v_packagesDir_x3f_1331_ = v_packagesDir_x3f_1415_;
v___y_1332_ = v_snd_1380_;
v___y_1333_ = v_a_1216_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = lean_box(0);
v___x_1421_ = lean_nat_dec_le(v___x_1418_, v___x_1418_);
if (v___x_1421_ == 0)
{
if (v___x_1419_ == 0)
{
lean_inc(v_packagesDir_x3f_1415_);
lean_dec(v_a_1414_);
v_packagesDir_x3f_1331_ = v_packagesDir_x3f_1415_;
v___y_1332_ = v_snd_1380_;
v___y_1333_ = v_a_1216_;
goto v___jp_1330_;
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1418_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1214_, v_packages_1416_, v___x_1422_, v___x_1423_, v___x_1420_, v_snd_1380_);
v___y_1372_ = v_a_1414_;
v___y_1373_ = v___x_1424_;
goto v___jp_1371_;
}
}
else
{
size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = lean_usize_of_nat(v___x_1418_);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1214_, v_packages_1416_, v___x_1425_, v___x_1426_, v___x_1420_, v_snd_1380_);
v___y_1372_ = v_a_1414_;
v___y_1373_ = v___x_1427_;
goto v___jp_1371_;
}
}
}
else
{
lean_object* v_a_1428_; 
v_a_1428_ = lean_ctor_get(v_fst_1379_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v_fst_1379_);
v___y_1367_ = v_a_1428_;
v___y_1368_ = v_snd_1380_;
v___y_1369_ = v_a_1216_;
goto v___jp_1366_;
}
}
}
v___jp_1431_:
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_1433_ == 0)
{
v_fst_1379_ = v_val_1432_;
v_snd_1380_ = v_a_1215_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_1435_ == 0)
{
if (v___x_1433_ == 0)
{
v_fst_1379_ = v_val_1432_;
v_snd_1380_ = v_a_1215_;
goto v___jp_1378_;
}
else
{
size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = ((size_t)0ULL);
v___x_1437_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1430_, v___x_1436_, v___x_1437_, v___x_1434_, v_a_1216_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref(v___x_1438_);
v_fst_1379_ = v_val_1432_;
v_snd_1380_ = v_a_1215_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_val_1432_);
lean_dec_ref(v_rootName_1377_);
lean_dec_ref(v_config_1302_);
lean_dec_ref(v_dir_1301_);
lean_dec(v_a_1215_);
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
else
{
size_t v___x_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = ((size_t)0ULL);
v___x_1448_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_1430_, v___x_1447_, v___x_1448_, v___x_1434_, v_a_1216_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_dec_ref(v___x_1449_);
v_fst_1379_ = v_val_1432_;
v_snd_1380_ = v_a_1215_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v_val_1432_);
lean_dec_ref(v_rootName_1377_);
lean_dec_ref(v_config_1302_);
lean_dec_ref(v_dir_1301_);
lean_dec(v_a_1215_);
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_1475_, lean_object* v_toUpdate_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_1475_, v_toUpdate_1476_, v_a_1477_, v_a_1478_);
lean_dec_ref(v_a_1478_);
lean_dec(v_toUpdate_1476_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_toUpdate_1481_, lean_object* v_as_1482_, size_t v_i_1483_, size_t v_stop_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_1481_, v_as_1482_, v_i_1483_, v_stop_1484_, v_b_1485_, v___y_1486_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_toUpdate_1490_, lean_object* v_as_1491_, lean_object* v_i_1492_, lean_object* v_stop_1493_, lean_object* v_b_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
size_t v_i_boxed_1498_; size_t v_stop_boxed_1499_; lean_object* v_res_1500_; 
v_i_boxed_1498_ = lean_unbox_usize(v_i_1492_);
lean_dec(v_i_1492_);
v_stop_boxed_1499_ = lean_unbox_usize(v_stop_1493_);
lean_dec(v_stop_1493_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_toUpdate_1490_, v_as_1491_, v_i_boxed_1498_, v_stop_boxed_1499_, v_b_1494_, v___y_1495_, v___y_1496_);
lean_dec_ref(v___y_1496_);
lean_dec_ref(v_as_1491_);
lean_dec(v_toUpdate_1490_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_dep_1501_, lean_object* v_as_1502_, size_t v_i_1503_, size_t v_stop_1504_, lean_object* v_b_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_fst_1509_; lean_object* v_snd_1510_; lean_object* v___y_1515_; lean_object* v_name_1516_; uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_eq(v_i_1503_, v_stop_1504_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; lean_object* v_name_1521_; lean_object* v_scope_1522_; lean_object* v_configFile_1523_; lean_object* v_manifestFile_x3f_1524_; lean_object* v_src_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1548_; 
v___x_1520_ = lean_array_uget(v_as_1502_, v_i_1503_);
v_name_1521_ = lean_ctor_get(v___x_1520_, 0);
v_scope_1522_ = lean_ctor_get(v___x_1520_, 1);
v_configFile_1523_ = lean_ctor_get(v___x_1520_, 2);
v_manifestFile_x3f_1524_ = lean_ctor_get(v___x_1520_, 3);
v_src_1525_ = lean_ctor_get(v___x_1520_, 4);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1527_ = v___x_1520_;
v_isShared_1528_ = v_isSharedCheck_1548_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_src_1525_);
lean_inc(v_manifestFile_x3f_1524_);
lean_inc(v_configFile_1523_);
lean_inc(v_scope_1522_);
lean_inc(v_name_1521_);
lean_dec(v___x_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1548_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1521_, v___y_1506_);
if (v___x_1529_ == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = 1;
if (lean_obj_tag(v_src_1525_) == 0)
{
lean_object* v_dir_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1543_; 
v_dir_1531_ = lean_ctor_get(v_src_1525_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_src_1525_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1533_ = v_src_1525_;
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_dir_1531_);
lean_dec(v_src_1525_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1543_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_relPkgDir_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v_relPkgDir_1535_ = lean_ctor_get(v_dep_1501_, 1);
lean_inc_ref(v_relPkgDir_1535_);
v___x_1536_ = l_Lake_joinRelative(v_relPkgDir_1535_, v_dir_1531_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1536_);
v___x_1538_ = v___x_1533_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
lean_inc(v_name_1521_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 4, v___x_1538_);
v___x_1540_ = v___x_1527_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_name_1521_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_scope_1522_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_configFile_1523_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_manifestFile_x3f_1524_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*5, v___x_1530_);
v___y_1515_ = v___x_1540_;
v_name_1516_ = v_name_1521_;
goto v___jp_1514_;
}
}
}
}
else
{
lean_object* v___x_1545_; 
lean_inc(v_name_1521_);
if (v_isShared_1528_ == 0)
{
v___x_1545_ = v___x_1527_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_name_1521_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_scope_1522_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_configFile_1523_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_manifestFile_x3f_1524_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_src_1525_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*5, v___x_1530_);
v___y_1515_ = v___x_1545_;
v_name_1516_ = v_name_1521_;
goto v___jp_1514_;
}
}
}
else
{
lean_object* v___x_1547_; 
lean_del_object(v___x_1527_);
lean_dec_ref(v_src_1525_);
lean_dec(v_manifestFile_x3f_1524_);
lean_dec_ref(v_configFile_1523_);
lean_dec_ref(v_scope_1522_);
lean_dec(v_name_1521_);
v___x_1547_ = lean_box(0);
v_fst_1509_ = v___x_1547_;
v_snd_1510_ = v___y_1506_;
goto v___jp_1508_;
}
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec_ref(v_dep_1501_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_b_1505_);
lean_ctor_set(v___x_1549_, 1, v___y_1506_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
v___jp_1508_:
{
size_t v___x_1511_; size_t v___x_1512_; 
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1503_, v___x_1511_);
v_i_1503_ = v___x_1512_;
v_b_1505_ = v_fst_1509_;
v___y_1506_ = v_snd_1510_;
goto _start;
}
v___jp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1516_, v___y_1515_, v___y_1506_);
v_fst_1509_ = v___x_1517_;
v_snd_1510_ = v___x_1518_;
goto v___jp_1508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_dep_1551_, lean_object* v_as_1552_, lean_object* v_i_1553_, lean_object* v_stop_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
size_t v_i_boxed_1558_; size_t v_stop_boxed_1559_; lean_object* v_res_1560_; 
v_i_boxed_1558_ = lean_unbox_usize(v_i_1553_);
lean_dec(v_i_1553_);
v_stop_boxed_1559_ = lean_unbox_usize(v_stop_1554_);
lean_dec(v_stop_1554_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1551_, v_as_1552_, v_i_boxed_1558_, v_stop_boxed_1559_, v_b_1555_, v___y_1556_);
lean_dec_ref(v_as_1552_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_dep_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_manifestEntry_1567_; lean_object* v_pkgDir_1568_; lean_object* v_name_1569_; lean_object* v_manifestFile_x3f_1570_; lean_object* v___y_1572_; lean_object* v_fst_1573_; lean_object* v_snd_1574_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v_val_1634_; lean_object* v___y_1662_; 
v_manifestEntry_1567_ = lean_ctor_get(v_dep_1563_, 4);
v_pkgDir_1568_ = lean_ctor_get(v_dep_1563_, 0);
v_name_1569_ = lean_ctor_get(v_manifestEntry_1567_, 0);
v_manifestFile_x3f_1570_ = lean_ctor_get(v_manifestEntry_1567_, 3);
if (lean_obj_tag(v_manifestFile_x3f_1570_) == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_1568_);
v___x_1683_ = l_Lake_joinRelative(v_pkgDir_1568_, v___x_1682_);
v___y_1662_ = v___x_1683_;
goto v___jp_1661_;
}
else
{
lean_object* v_val_1684_; lean_object* v___x_1685_; 
v_val_1684_ = lean_ctor_get(v_manifestFile_x3f_1570_, 0);
lean_inc(v_val_1684_);
lean_inc_ref(v_pkgDir_1568_);
v___x_1685_ = l_Lake_joinRelative(v_pkgDir_1568_, v_val_1684_);
v___y_1662_ = v___x_1685_;
goto v___jp_1661_;
}
v___jp_1571_:
{
if (lean_obj_tag(v_fst_1573_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1604_; 
lean_inc(v_name_1569_);
lean_dec_ref(v_dep_1563_);
v_a_1575_ = lean_ctor_get(v_fst_1573_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_fst_1573_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1577_ = v_fst_1573_;
v_isShared_1578_ = v_isSharedCheck_1604_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v_fst_1573_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1604_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
if (lean_obj_tag(v_a_1575_) == 11)
{
uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec_ref(v_a_1575_);
v___x_1579_ = 0;
v___x_1580_ = l_Lean_Name_toString(v_name_1569_, v___x_1579_);
v___x_1581_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1582_ = lean_string_append(v___x_1580_, v___x_1581_);
v___x_1583_ = lean_string_append(v___x_1582_, v___y_1572_);
lean_dec_ref(v___y_1572_);
v___x_1584_ = 2;
v___x_1585_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set_uint8(v___x_1585_, sizeof(void*)*1, v___x_1584_);
lean_inc_ref(v_a_1565_);
v___x_1586_ = lean_apply_2(v_a_1565_, v___x_1585_, lean_box(0));
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_snd_1574_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1587_);
v___x_1589_ = v___x_1577_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
else
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_dec_ref(v___y_1572_);
v___x_1591_ = 0;
v___x_1592_ = l_Lean_Name_toString(v_name_1569_, v___x_1591_);
v___x_1593_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1594_ = lean_string_append(v___x_1592_, v___x_1593_);
v___x_1595_ = lean_io_error_to_string(v_a_1575_);
v___x_1596_ = lean_string_append(v___x_1594_, v___x_1595_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = 2;
v___x_1598_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*1, v___x_1597_);
lean_inc_ref(v_a_1565_);
v___x_1599_ = lean_apply_2(v_a_1565_, v___x_1598_, lean_box(0));
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
lean_ctor_set(v___x_1600_, 1, v_snd_1574_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1600_);
v___x_1602_ = v___x_1577_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v___y_1572_);
v_a_1605_ = lean_ctor_get(v_fst_1573_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_fst_1573_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1607_ = v_fst_1573_;
v_isShared_1608_ = v_isSharedCheck_1629_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v_fst_1573_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1629_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_packages_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_packages_1609_ = lean_ctor_get(v_a_1605_, 3);
lean_inc_ref(v_packages_1609_);
lean_dec(v_a_1605_);
v___x_1610_ = lean_unsigned_to_nat(0u);
v___x_1611_ = lean_array_get_size(v_packages_1609_);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_nat_dec_lt(v___x_1610_, v___x_1611_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_dec_ref(v_packages_1609_);
lean_dec_ref(v_dep_1563_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v_snd_1574_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1614_);
v___x_1616_ = v___x_1607_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_nat_dec_le(v___x_1611_, v___x_1611_);
if (v___x_1618_ == 0)
{
if (v___x_1613_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_dec_ref(v_packages_1609_);
lean_dec_ref(v_dep_1563_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1612_);
lean_ctor_set(v___x_1619_, 1, v_snd_1574_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1619_);
v___x_1621_ = v___x_1607_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
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
size_t v___x_1623_; size_t v___x_1624_; lean_object* v___x_1625_; 
lean_del_object(v___x_1607_);
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = lean_usize_of_nat(v___x_1611_);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1563_, v_packages_1609_, v___x_1623_, v___x_1624_, v___x_1612_, v_snd_1574_);
lean_dec_ref(v_packages_1609_);
return v___x_1625_;
}
}
else
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
lean_del_object(v___x_1607_);
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1611_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1563_, v_packages_1609_, v___x_1626_, v___x_1627_, v___x_1612_, v_snd_1574_);
lean_dec_ref(v_packages_1609_);
return v___x_1628_;
}
}
}
}
}
v___jp_1630_:
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = lean_array_get_size(v___y_1633_);
v___x_1636_ = lean_nat_dec_lt(v___y_1632_, v___x_1635_);
if (v___x_1636_ == 0)
{
v___y_1572_ = v___y_1631_;
v_fst_1573_ = v_val_1634_;
v_snd_1574_ = v_a_1564_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_nat_dec_le(v___x_1635_, v___x_1635_);
if (v___x_1638_ == 0)
{
if (v___x_1636_ == 0)
{
v___y_1572_ = v___y_1631_;
v_fst_1573_ = v_val_1634_;
v_snd_1574_ = v_a_1564_;
goto v___jp_1571_;
}
else
{
size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = lean_usize_of_nat(v___x_1635_);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1633_, v___x_1639_, v___x_1640_, v___x_1637_, v_a_1565_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec_ref(v___x_1641_);
v___y_1572_ = v___y_1631_;
v_fst_1573_ = v_val_1634_;
v_snd_1574_ = v_a_1564_;
goto v___jp_1571_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v_val_1634_);
lean_dec_ref(v___y_1631_);
lean_dec(v_a_1564_);
lean_dec_ref(v_dep_1563_);
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
else
{
size_t v___x_1650_; size_t v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = lean_usize_of_nat(v___x_1635_);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_1633_, v___x_1650_, v___x_1651_, v___x_1637_, v_a_1565_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_dec_ref(v___x_1652_);
v___y_1572_ = v___y_1631_;
v_fst_1573_ = v_val_1634_;
v_snd_1574_ = v_a_1564_;
goto v___jp_1571_;
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v_val_1634_);
lean_dec_ref(v___y_1631_);
lean_dec(v_a_1564_);
lean_dec_ref(v_dep_1563_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
v___jp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_1662_);
v___x_1665_ = l_Lake_Manifest_load(v___y_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 1);
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
v___y_1631_ = v___y_1662_;
v___y_1632_ = v___x_1663_;
v___y_1633_ = v___x_1664_;
v_val_1634_ = v___x_1671_;
goto v___jp_1630_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1665_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1665_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 0);
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
v___y_1631_ = v___y_1662_;
v___y_1632_ = v___x_1663_;
v___y_1633_ = v___x_1664_;
v_val_1634_ = v___x_1679_;
goto v___jp_1630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_dep_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_dep_1686_, v_a_1687_, v_a_1688_);
lean_dec_ref(v_a_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_dep_1691_, lean_object* v_as_1692_, size_t v_i_1693_, size_t v_stop_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_1691_, v_as_1692_, v_i_1693_, v_stop_1694_, v_b_1695_, v___y_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_dep_1700_, lean_object* v_as_1701_, lean_object* v_i_1702_, lean_object* v_stop_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
size_t v_i_boxed_1708_; size_t v_stop_boxed_1709_; lean_object* v_res_1710_; 
v_i_boxed_1708_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_stop_boxed_1709_ = lean_unbox_usize(v_stop_1703_);
lean_dec(v_stop_1703_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_dep_1700_, v_as_1701_, v_i_boxed_1708_, v_stop_boxed_1709_, v_b_1704_, v___y_1705_, v___y_1706_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_as_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1712_, lean_object* v_pkg_1713_, lean_object* v_dep_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
uint8_t v___y_1719_; lean_object* v___y_1720_; lean_object* v_name_1748_; lean_object* v___x_1749_; 
v_name_1748_ = lean_ctor_get(v_dep_1714_, 0);
v___x_1749_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1715_, v_name_1748_);
if (lean_obj_tag(v___x_1749_) == 1)
{
lean_object* v_root_1750_; lean_object* v_config_1751_; lean_object* v_val_1752_; lean_object* v_lakeEnv_1753_; lean_object* v_dir_1754_; lean_object* v_toWorkspaceConfig_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v_dep_1714_);
lean_dec_ref(v_pkg_1713_);
v_root_1750_ = lean_ctor_get(v_ws_1712_, 0);
lean_inc_ref(v_root_1750_);
v_config_1751_ = lean_ctor_get(v_root_1750_, 6);
lean_inc_ref(v_config_1751_);
v_val_1752_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_val_1752_);
lean_dec_ref(v___x_1749_);
v_lakeEnv_1753_ = lean_ctor_get(v_ws_1712_, 1);
lean_inc_ref(v_lakeEnv_1753_);
lean_dec_ref(v_ws_1712_);
v_dir_1754_ = lean_ctor_get(v_root_1750_, 4);
lean_inc_ref(v_dir_1754_);
lean_dec_ref(v_root_1750_);
v_toWorkspaceConfig_1755_ = lean_ctor_get(v_config_1751_, 0);
lean_inc_ref(v_toWorkspaceConfig_1755_);
lean_dec_ref(v_config_1751_);
v___x_1756_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1755_);
v___x_1757_ = l_Lake_PackageEntry_materialize(v_val_1752_, v_lakeEnv_1753_, v_dir_1754_, v___x_1756_, v_a_1716_);
lean_dec_ref(v_lakeEnv_1753_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v_a_1758_);
lean_ctor_set(v___x_1762_, 1, v_a_1715_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1715_);
v_a_1767_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1757_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1757_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_wsIdx_1775_; lean_object* v_relDir_1776_; uint8_t v___y_1778_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
lean_dec(v___x_1749_);
v_wsIdx_1775_ = lean_ctor_get(v_pkg_1713_, 0);
lean_inc(v_wsIdx_1775_);
v_relDir_1776_ = lean_ctor_get(v_pkg_1713_, 5);
lean_inc_ref(v_relDir_1776_);
lean_dec_ref(v_pkg_1713_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_nat_dec_eq(v_wsIdx_1775_, v___x_1782_);
lean_dec(v_wsIdx_1775_);
if (v___x_1783_ == 0)
{
uint8_t v___x_1784_; 
v___x_1784_ = 1;
v___y_1778_ = v___x_1784_;
goto v___jp_1777_;
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = 0;
v___y_1778_ = v___x_1785_;
goto v___jp_1777_;
}
v___jp_1777_:
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1780_ = lean_string_dec_eq(v_relDir_1776_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lake_joinRelative(v_relDir_1776_, v___x_1779_);
v___y_1719_ = v___y_1778_;
v___y_1720_ = v___x_1781_;
goto v___jp_1718_;
}
else
{
v___y_1719_ = v___y_1778_;
v___y_1720_ = v_relDir_1776_;
goto v___jp_1718_;
}
}
}
v___jp_1718_:
{
lean_object* v_root_1721_; lean_object* v_config_1722_; lean_object* v_lakeEnv_1723_; lean_object* v_dir_1724_; lean_object* v_toWorkspaceConfig_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_root_1721_ = lean_ctor_get(v_ws_1712_, 0);
lean_inc_ref(v_root_1721_);
v_config_1722_ = lean_ctor_get(v_root_1721_, 6);
lean_inc_ref(v_config_1722_);
v_lakeEnv_1723_ = lean_ctor_get(v_ws_1712_, 1);
lean_inc_ref(v_lakeEnv_1723_);
lean_dec_ref(v_ws_1712_);
v_dir_1724_ = lean_ctor_get(v_root_1721_, 4);
lean_inc_ref(v_dir_1724_);
lean_dec_ref(v_root_1721_);
v_toWorkspaceConfig_1725_ = lean_ctor_get(v_config_1722_, 0);
lean_inc_ref(v_toWorkspaceConfig_1725_);
lean_dec_ref(v_config_1722_);
v___x_1726_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1725_);
v___x_1727_ = l_Lake_Dependency_materialize(v_dep_1714_, v___y_1719_, v_lakeEnv_1723_, v_dir_1724_, v___x_1726_, v___y_1720_, v_a_1716_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1739_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1739_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1739_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_manifestEntry_1732_; lean_object* v_name_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v_manifestEntry_1732_ = lean_ctor_get(v_a_1728_, 4);
v_name_1733_ = lean_ctor_get(v_manifestEntry_1732_, 0);
lean_inc_ref(v_manifestEntry_1732_);
lean_inc(v_name_1733_);
v___x_1734_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1733_, v_manifestEntry_1732_, v_a_1715_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v_a_1728_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1735_);
v___x_1737_ = v___x_1730_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1715_);
v_a_1740_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1727_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1727_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1786_, lean_object* v_pkg_1787_, lean_object* v_dep_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1786_, v_pkg_1787_, v_dep_1788_, v_a_1789_, v_a_1790_);
lean_dec_ref(v_a_1790_);
return v_res_1792_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1793_; 
v___x_1793_ = 4;
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1794_, lean_object* v_tc_x3f_1795_, uint8_t v_fixed_1796_, lean_object* v_self_1797_){
_start:
{
lean_object* v_clashes_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
v_clashes_1798_ = lean_ctor_get(v_self_1797_, 2);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_self_1797_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; lean_object* v_unused_1807_; 
v_unused_1806_ = lean_ctor_get(v_self_1797_, 1);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v_self_1797_, 0);
lean_dec(v_unused_1807_);
v___x_1800_ = v_self_1797_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_clashes_1798_);
lean_dec(v_self_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 1, v_tc_x3f_1795_);
lean_ctor_set(v___x_1800_, 0, v_src_1794_);
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_src_1794_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_tc_x3f_1795_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_clashes_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*3, v_fixed_1796_);
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1808_, lean_object* v_tc_x3f_1809_, lean_object* v_fixed_1810_, lean_object* v_self_1811_){
_start:
{
uint8_t v_fixed_boxed_1812_; lean_object* v_res_1813_; 
v_fixed_boxed_1812_ = lean_unbox(v_fixed_1810_);
v_res_1813_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1808_, v_tc_x3f_1809_, v_fixed_boxed_1812_, v_self_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1814_, lean_object* v_ver_1815_, uint8_t v_fixed_1816_, lean_object* v_self_1817_){
_start:
{
lean_object* v_src_1818_; lean_object* v_tc_x3f_1819_; lean_object* v_clashes_1820_; uint8_t v_fixed_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1830_; 
v_src_1818_ = lean_ctor_get(v_self_1817_, 0);
v_tc_x3f_1819_ = lean_ctor_get(v_self_1817_, 1);
v_clashes_1820_ = lean_ctor_get(v_self_1817_, 2);
v_fixed_1821_ = lean_ctor_get_uint8(v_self_1817_, sizeof(void*)*3);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_self_1817_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1823_ = v_self_1817_;
v_isShared_1824_ = v_isSharedCheck_1830_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_clashes_1820_);
lean_inc(v_tc_x3f_1819_);
lean_inc(v_src_1818_);
lean_dec(v_self_1817_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1830_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1825_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1825_, 0, v_src_1814_);
lean_ctor_set(v___x_1825_, 1, v_ver_1815_);
lean_ctor_set_uint8(v___x_1825_, sizeof(void*)*2, v_fixed_1816_);
v___x_1826_ = lean_array_push(v_clashes_1820_, v___x_1825_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 2, v___x_1826_);
v___x_1828_ = v___x_1823_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_src_1818_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_tc_x3f_1819_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v___x_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*3, v_fixed_1821_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1831_, lean_object* v_ver_1832_, lean_object* v_fixed_1833_, lean_object* v_self_1834_){
_start:
{
uint8_t v_fixed_boxed_1835_; lean_object* v_res_1836_; 
v_fixed_boxed_1835_ = lean_unbox(v_fixed_1833_);
v_res_1836_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1831_, v_ver_1832_, v_fixed_boxed_1835_, v_self_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v_as_1841_, size_t v_i_1842_, size_t v_stop_1843_, lean_object* v_b_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_usize_dec_eq(v_i_1842_, v_stop_1843_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v_src_1847_; lean_object* v_ver_1848_; uint8_t v_fixed_1849_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1865_; 
v___x_1846_ = lean_array_uget_borrowed(v_as_1841_, v_i_1842_);
v_src_1847_ = lean_ctor_get(v___x_1846_, 0);
v_ver_1848_ = lean_ctor_get(v___x_1846_, 1);
v_fixed_1849_ = lean_ctor_get_uint8(v___x_1846_, sizeof(void*)*2);
if (v_fixed_1849_ == 0)
{
lean_object* v___x_1869_; 
v___x_1869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1865_ = v___x_1869_;
goto v___jp_1864_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1865_ = v___x_1870_;
goto v___jp_1864_;
}
v___jp_1850_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; 
v___x_1854_ = lean_string_append(v___y_1852_, v___y_1853_);
lean_dec_ref(v___y_1853_);
v___x_1855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1856_ = lean_string_append(v___x_1854_, v___x_1855_);
v___x_1857_ = 1;
lean_inc(v_src_1847_);
v___x_1858_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1847_, v___x_1857_);
v___x_1859_ = lean_string_append(v___x_1856_, v___x_1858_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = lean_string_append(v___x_1859_, v___y_1851_);
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1842_, v___x_1861_);
v_i_1842_ = v___x_1862_;
v_b_1844_ = v___x_1860_;
goto _start;
}
v___jp_1864_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_toString_1868_; 
v___x_1866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1867_ = lean_string_append(v_b_1844_, v___x_1866_);
v_toString_1868_ = lean_ctor_get(v_ver_1848_, 0);
lean_inc_ref(v_toString_1868_);
v___y_1851_ = v___y_1865_;
v___y_1852_ = v___x_1867_;
v___y_1853_ = v_toString_1868_;
goto v___jp_1850_;
}
}
else
{
return v_b_1844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v_as_1871_, lean_object* v_i_1872_, lean_object* v_stop_1873_, lean_object* v_b_1874_){
_start:
{
size_t v_i_boxed_1875_; size_t v_stop_boxed_1876_; lean_object* v_res_1877_; 
v_i_boxed_1875_ = lean_unbox_usize(v_i_1872_);
lean_dec(v_i_1872_);
v_stop_boxed_1876_ = lean_unbox_usize(v_stop_1873_);
lean_dec(v_stop_1873_);
v_res_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1871_, v_i_boxed_1875_, v_stop_boxed_1876_, v_b_1874_);
lean_dec_ref(v_as_1871_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v_as_1878_, size_t v_i_1879_, size_t v_stop_1880_, lean_object* v_b_1881_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_usize_dec_eq(v_i_1879_, v_stop_1880_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v_src_1884_; lean_object* v_ver_1885_; uint8_t v_fixed_1886_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1902_; 
v___x_1883_ = lean_array_uget_borrowed(v_as_1878_, v_i_1879_);
v_src_1884_ = lean_ctor_get(v___x_1883_, 0);
v_ver_1885_ = lean_ctor_get(v___x_1883_, 1);
v_fixed_1886_ = lean_ctor_get_uint8(v___x_1883_, sizeof(void*)*2);
if (v_fixed_1886_ == 0)
{
lean_object* v___x_1906_; 
v___x_1906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1902_ = v___x_1906_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1907_; 
v___x_1907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1902_ = v___x_1907_;
goto v___jp_1901_;
}
v___jp_1887_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1891_ = lean_string_append(v___y_1888_, v___y_1890_);
lean_dec_ref(v___y_1890_);
v___x_1892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1893_ = lean_string_append(v___x_1891_, v___x_1892_);
v___x_1894_ = 1;
lean_inc(v_src_1884_);
v___x_1895_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1884_, v___x_1894_);
v___x_1896_ = lean_string_append(v___x_1893_, v___x_1895_);
lean_dec_ref(v___x_1895_);
v___x_1897_ = lean_string_append(v___x_1896_, v___y_1889_);
v___x_1898_ = ((size_t)1ULL);
v___x_1899_ = lean_usize_add(v_i_1879_, v___x_1898_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1878_, v___x_1899_, v_stop_1880_, v___x_1897_);
return v___x_1900_;
}
v___jp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_toString_1905_; 
v___x_1903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1904_ = lean_string_append(v_b_1881_, v___x_1903_);
v_toString_1905_ = lean_ctor_get(v_ver_1885_, 0);
lean_inc_ref(v_toString_1905_);
v___y_1888_ = v___x_1904_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v_toString_1905_;
goto v___jp_1887_;
}
}
else
{
return v_b_1881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v_as_1908_, lean_object* v_i_1909_, lean_object* v_stop_1910_, lean_object* v_b_1911_){
_start:
{
size_t v_i_boxed_1912_; size_t v_stop_boxed_1913_; lean_object* v_res_1914_; 
v_i_boxed_1912_ = lean_unbox_usize(v_i_1909_);
lean_dec(v_i_1909_);
v_stop_boxed_1913_ = lean_unbox_usize(v_stop_1910_);
lean_dec(v_stop_1910_);
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v_as_1908_, v_i_boxed_1912_, v_stop_boxed_1913_, v_b_1911_);
lean_dec_ref(v_as_1908_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_1915_, lean_object* v_as_1916_, size_t v_i_1917_, size_t v_stop_1918_, lean_object* v_b_1919_, lean_object* v___y_1920_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_eq(v_i_1917_, v_stop_1918_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v_relPkgDir_1924_; lean_object* v_manifestEntry_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1923_ = lean_array_uget_borrowed(v_as_1916_, v_i_1917_);
v_relPkgDir_1924_ = lean_ctor_get(v___x_1923_, 1);
v_manifestEntry_1925_ = lean_ctor_get(v___x_1923_, 4);
lean_inc_ref(v_relPkgDir_1924_);
lean_inc_ref(v___x_1915_);
v___x_1926_ = l_Lake_joinRelative(v___x_1915_, v_relPkgDir_1924_);
v___x_1927_ = l_Lake_toolchainFileName;
v___x_1928_ = l_System_FilePath_join(v___x_1926_, v___x_1927_);
v___x_1929_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1928_);
lean_dec_ref(v___x_1928_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v_a_1932_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1929_);
if (lean_obj_tag(v_a_1930_) == 1)
{
lean_object* v_tc_x3f_1936_; 
v_tc_x3f_1936_ = lean_ctor_get(v_b_1919_, 1);
if (lean_obj_tag(v_tc_x3f_1936_) == 1)
{
lean_object* v_val_1937_; lean_object* v_src_1938_; lean_object* v_clashes_1939_; uint8_t v_fixed_1940_; lean_object* v_val_1941_; uint8_t v___x_1942_; 
v_val_1937_ = lean_ctor_get(v_a_1930_, 0);
v_src_1938_ = lean_ctor_get(v_b_1919_, 0);
v_clashes_1939_ = lean_ctor_get(v_b_1919_, 2);
v_fixed_1940_ = lean_ctor_get_uint8(v_b_1919_, sizeof(void*)*3);
v_val_1941_ = lean_ctor_get(v_tc_x3f_1936_, 0);
v___x_1942_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1923_);
if (v___x_1942_ == 0)
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lake_ToolchainVer_ble(v_val_1937_, v_val_1941_);
if (v___x_1952_ == 0)
{
lean_inc_ref(v_clashes_1939_);
lean_inc(v_src_1938_);
lean_inc_ref(v_tc_x3f_1936_);
lean_dec_ref(v_b_1919_);
if (v_fixed_1940_ == 0)
{
goto v___jp_1948_;
}
else
{
if (v___x_1942_ == 0)
{
lean_inc(v_val_1937_);
lean_dec_ref(v_a_1930_);
goto v___jp_1943_;
}
else
{
goto v___jp_1948_;
}
}
}
else
{
lean_dec_ref(v_a_1930_);
v_a_1932_ = v_b_1919_;
goto v___jp_1931_;
}
}
else
{
if (v_fixed_1940_ == 0)
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1967_; 
lean_inc_ref(v_clashes_1939_);
lean_inc(v_src_1938_);
lean_inc_ref(v_tc_x3f_1936_);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_b_1919_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; lean_object* v_unused_1969_; lean_object* v_unused_1970_; 
v_unused_1968_ = lean_ctor_get(v_b_1919_, 2);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_b_1919_, 1);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_b_1919_, 0);
lean_dec(v_unused_1970_);
v___x_1954_ = v_b_1919_;
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v_b_1919_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1967_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
uint8_t v___x_1956_; 
v___x_1956_ = l_Lake_ToolchainVer_ble(v_val_1941_, v_val_1937_);
if (v___x_1956_ == 0)
{
lean_object* v_name_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
lean_inc(v_val_1937_);
lean_dec_ref(v_a_1930_);
v_name_1957_ = lean_ctor_get(v_manifestEntry_1925_, 0);
lean_inc(v_name_1957_);
v___x_1958_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1958_, 0, v_name_1957_);
lean_ctor_set(v___x_1958_, 1, v_val_1937_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*2, v___x_1942_);
v___x_1959_ = lean_array_push(v_clashes_1939_, v___x_1958_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 2, v___x_1959_);
v___x_1961_ = v___x_1954_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_src_1938_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_tc_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v___x_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1962_, sizeof(void*)*3, v_fixed_1940_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v_a_1932_ = v___x_1961_;
goto v___jp_1931_;
}
}
else
{
lean_object* v_name_1963_; lean_object* v___x_1965_; 
lean_dec(v_src_1938_);
lean_dec_ref(v_tc_x3f_1936_);
v_name_1963_ = lean_ctor_get(v_manifestEntry_1925_, 0);
lean_inc(v_name_1963_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_a_1930_);
lean_ctor_set(v___x_1954_, 0, v_name_1963_);
v___x_1965_ = v___x_1954_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_name_1963_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_a_1930_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_clashes_1939_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*3, v___x_1942_);
v_a_1932_ = v___x_1965_;
goto v___jp_1931_;
}
}
}
}
else
{
uint8_t v___x_1971_; 
lean_inc_n(v_val_1937_, 2);
lean_dec_ref(v_a_1930_);
lean_inc(v_val_1941_);
v___x_1971_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_1941_, v_val_1937_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1981_; 
lean_inc_ref(v_clashes_1939_);
lean_inc(v_src_1938_);
lean_inc_ref(v_tc_x3f_1936_);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_b_1919_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; lean_object* v_unused_1983_; lean_object* v_unused_1984_; 
v_unused_1982_ = lean_ctor_get(v_b_1919_, 2);
lean_dec(v_unused_1982_);
v_unused_1983_ = lean_ctor_get(v_b_1919_, 1);
lean_dec(v_unused_1983_);
v_unused_1984_ = lean_ctor_get(v_b_1919_, 0);
lean_dec(v_unused_1984_);
v___x_1973_ = v_b_1919_;
v_isShared_1974_ = v_isSharedCheck_1981_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v_b_1919_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1981_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_name_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v_name_1975_ = lean_ctor_get(v_manifestEntry_1925_, 0);
lean_inc(v_name_1975_);
v___x_1976_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1976_, 0, v_name_1975_);
lean_ctor_set(v___x_1976_, 1, v_val_1937_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*2, v___x_1942_);
v___x_1977_ = lean_array_push(v_clashes_1939_, v___x_1976_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 2, v___x_1977_);
v___x_1979_ = v___x_1973_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_src_1938_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_tc_x3f_1936_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v___x_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_1980_, sizeof(void*)*3, v_fixed_1940_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
v_a_1932_ = v___x_1979_;
goto v___jp_1931_;
}
}
}
else
{
lean_dec(v_val_1937_);
v_a_1932_ = v_b_1919_;
goto v___jp_1931_;
}
}
}
v___jp_1943_:
{
lean_object* v_name_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_name_1944_ = lean_ctor_get(v_manifestEntry_1925_, 0);
lean_inc(v_name_1944_);
v___x_1945_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1945_, 0, v_name_1944_);
lean_ctor_set(v___x_1945_, 1, v_val_1937_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*2, v___x_1942_);
v___x_1946_ = lean_array_push(v_clashes_1939_, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1947_, 0, v_src_1938_);
lean_ctor_set(v___x_1947_, 1, v_tc_x3f_1936_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
lean_ctor_set_uint8(v___x_1947_, sizeof(void*)*3, v_fixed_1940_);
v_a_1932_ = v___x_1947_;
goto v___jp_1931_;
}
v___jp_1948_:
{
uint8_t v___x_1949_; 
v___x_1949_ = l_Lake_ToolchainVer_blt(v_val_1941_, v_val_1937_);
if (v___x_1949_ == 0)
{
lean_inc(v_val_1937_);
lean_dec_ref(v_a_1930_);
goto v___jp_1943_;
}
else
{
lean_object* v_name_1950_; lean_object* v___x_1951_; 
lean_dec(v_src_1938_);
lean_dec_ref(v_tc_x3f_1936_);
v_name_1950_ = lean_ctor_get(v_manifestEntry_1925_, 0);
lean_inc(v_name_1950_);
v___x_1951_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1951_, 0, v_name_1950_);
lean_ctor_set(v___x_1951_, 1, v_a_1930_);
lean_ctor_set(v___x_1951_, 2, v_clashes_1939_);
lean_ctor_set_uint8(v___x_1951_, sizeof(void*)*3, v___x_1942_);
v_a_1932_ = v___x_1951_;
goto v___jp_1931_;
}
}
}
else
{
lean_object* v_clashes_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1994_; 
v_clashes_1985_ = lean_ctor_get(v_b_1919_, 2);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_b_1919_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; lean_object* v_unused_1996_; 
v_unused_1995_ = lean_ctor_get(v_b_1919_, 1);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_b_1919_, 0);
lean_dec(v_unused_1996_);
v___x_1987_ = v_b_1919_;
v_isShared_1988_ = v_isSharedCheck_1994_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_clashes_1985_);
lean_dec(v_b_1919_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1994_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_name_1989_; uint8_t v___x_1990_; lean_object* v___x_1992_; 
v_name_1989_ = lean_ctor_get(v_manifestEntry_1925_, 0);
v___x_1990_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1923_);
lean_inc(v_name_1989_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v_a_1930_);
lean_ctor_set(v___x_1987_, 0, v_name_1989_);
v___x_1992_ = v___x_1987_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_name_1989_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_a_1930_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_clashes_1985_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*3, v___x_1990_);
v_a_1932_ = v___x_1992_;
goto v___jp_1931_;
}
}
}
}
else
{
lean_dec(v_a_1930_);
v_a_1932_ = v_b_1919_;
goto v___jp_1931_;
}
v___jp_1931_:
{
size_t v___x_1933_; size_t v___x_1934_; 
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1917_, v___x_1933_);
v_i_1917_ = v___x_1934_;
v_b_1919_ = v_a_1932_;
goto _start;
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_b_1919_);
lean_dec_ref(v___x_1915_);
v_a_1997_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1999_ = v___x_1929_;
v_isShared_2000_ = v_isSharedCheck_2009_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1929_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2009_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2001_ = lean_io_error_to_string(v_a_1997_);
v___x_2002_ = 3;
v___x_2003_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set_uint8(v___x_2003_, sizeof(void*)*1, v___x_2002_);
lean_inc_ref(v___y_1920_);
v___x_2004_ = lean_apply_2(v___y_1920_, v___x_2003_, lean_box(0));
v___x_2005_ = lean_box(0);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2005_);
v___x_2007_ = v___x_1999_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_object* v___x_2010_; 
lean_dec_ref(v___x_1915_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_b_1919_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_2011_, lean_object* v_as_2012_, lean_object* v_i_2013_, lean_object* v_stop_2014_, lean_object* v_b_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
size_t v_i_boxed_2018_; size_t v_stop_boxed_2019_; lean_object* v_res_2020_; 
v_i_boxed_2018_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_stop_boxed_2019_ = lean_unbox_usize(v_stop_2014_);
lean_dec(v_stop_2014_);
v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_2011_, v_as_2012_, v_i_boxed_2018_, v_stop_boxed_2019_, v_b_2015_, v___y_2016_);
lean_dec_ref(v___y_2016_);
lean_dec_ref(v_as_2012_);
return v_res_2020_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2030_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v___x_2031_ = lean_unsigned_to_nat(4u);
v___x_2032_ = lean_mk_empty_array_with_capacity(v___x_2031_);
v___x_2033_ = lean_array_push(v___x_2032_, v___x_2030_);
return v___x_2033_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_2035_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6);
v___x_2036_ = lean_array_push(v___x_2035_, v___x_2034_);
return v___x_2036_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10(void){
_start:
{
uint32_t v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = 4;
v___x_2042_ = lean_uint32_to_uint8(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_2060_, lean_object* v_rootDeps_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___y_2065_; lean_object* v_root_2070_; lean_object* v_lakeEnv_2071_; lean_object* v_lakeArgs_x3f_2072_; uint8_t v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2219_; lean_object* v___y_2220_; uint8_t v___y_2221_; lean_object* v_baseName_2224_; lean_object* v_dir_2225_; lean_object* v_config_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_root_2070_ = lean_ctor_get(v_ws_2060_, 0);
lean_inc_ref(v_root_2070_);
v_lakeEnv_2071_ = lean_ctor_get(v_ws_2060_, 1);
lean_inc_ref(v_lakeEnv_2071_);
v_lakeArgs_x3f_2072_ = lean_ctor_get(v_ws_2060_, 4);
lean_inc(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_ws_2060_);
v_baseName_2224_ = lean_ctor_get(v_root_2070_, 1);
lean_inc(v_baseName_2224_);
v_dir_2225_ = lean_ctor_get(v_root_2070_, 4);
lean_inc_ref_n(v_dir_2225_, 2);
v_config_2226_ = lean_ctor_get(v_root_2070_, 6);
lean_inc_ref(v_config_2226_);
lean_dec_ref(v_root_2070_);
v___x_2227_ = l_Lake_toolchainFileName;
v___x_2228_ = l_System_FilePath_join(v_dir_2225_, v___x_2227_);
v___x_2229_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2228_);
lean_dec_ref(v___x_2228_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2324_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2324_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2324_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
uint8_t v_fixedToolchain_2234_; lean_object* v___x_2235_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2263_; lean_object* v___y_2264_; uint8_t v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v_src_2272_; lean_object* v_tc_x3f_2273_; lean_object* v_clashes_2274_; uint8_t v_fixed_2275_; lean_object* v___y_2299_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_fixedToolchain_2234_ = lean_ctor_get_uint8(v_config_2226_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_2226_);
v___x_2235_ = lean_unsigned_to_nat(0u);
v___x_2313_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2314_ = lean_array_get_size(v_rootDeps_2061_);
v___x_2315_ = lean_nat_dec_lt(v___x_2235_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_inc(v_a_2230_);
v_src_2272_ = v_baseName_2224_;
v_tc_x3f_2273_ = v_a_2230_;
v_clashes_2274_ = v___x_2313_;
v_fixed_2275_ = v_fixedToolchain_2234_;
goto v___jp_2271_;
}
else
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
lean_inc(v_a_2230_);
lean_inc(v_baseName_2224_);
v___x_2316_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2316_, 0, v_baseName_2224_);
lean_ctor_set(v___x_2316_, 1, v_a_2230_);
lean_ctor_set(v___x_2316_, 2, v___x_2313_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*3, v_fixedToolchain_2234_);
v___x_2317_ = lean_nat_dec_le(v___x_2314_, v___x_2314_);
if (v___x_2317_ == 0)
{
if (v___x_2315_ == 0)
{
lean_dec_ref(v___x_2316_);
lean_inc(v_a_2230_);
v_src_2272_ = v_baseName_2224_;
v_tc_x3f_2273_ = v_a_2230_;
v_clashes_2274_ = v___x_2313_;
v_fixed_2275_ = v_fixedToolchain_2234_;
goto v___jp_2271_;
}
else
{
size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
lean_dec(v_baseName_2224_);
v___x_2318_ = ((size_t)0ULL);
v___x_2319_ = lean_usize_of_nat(v___x_2314_);
lean_inc_ref(v_dir_2225_);
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2225_, v_rootDeps_2061_, v___x_2318_, v___x_2319_, v___x_2316_, v_a_2062_);
v___y_2299_ = v___x_2320_;
goto v___jp_2298_;
}
}
else
{
size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
lean_dec(v_baseName_2224_);
v___x_2321_ = ((size_t)0ULL);
v___x_2322_ = lean_usize_of_nat(v___x_2314_);
lean_inc_ref(v_dir_2225_);
v___x_2323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2225_, v_rootDeps_2061_, v___x_2321_, v___x_2322_, v___x_2316_, v_a_2062_);
v___y_2299_ = v___x_2323_;
goto v___jp_2298_;
}
}
v___jp_2236_:
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_nat_dec_lt(v___x_2235_, v___y_2238_);
if (v___x_2240_ == 0)
{
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
v___y_2065_ = v___y_2239_;
goto v___jp_2064_;
}
else
{
uint8_t v___x_2241_; 
v___x_2241_ = lean_nat_dec_le(v___y_2238_, v___y_2238_);
if (v___x_2241_ == 0)
{
if (v___x_2240_ == 0)
{
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
v___y_2065_ = v___y_2239_;
goto v___jp_2064_;
}
else
{
size_t v___x_2242_; size_t v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = lean_usize_of_nat(v___y_2238_);
lean_dec(v___y_2238_);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2237_, v___x_2242_, v___x_2243_, v___y_2239_);
lean_dec_ref(v___y_2237_);
v___y_2065_ = v___x_2244_;
goto v___jp_2064_;
}
}
else
{
size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = ((size_t)0ULL);
v___x_2246_ = lean_usize_of_nat(v___y_2238_);
lean_dec(v___y_2238_);
v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2237_, v___x_2245_, v___x_2246_, v___y_2239_);
lean_dec_ref(v___y_2237_);
v___y_2065_ = v___x_2247_;
goto v___jp_2064_;
}
}
}
v___jp_2248_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_inc_ref(v___y_2251_);
v___x_2256_ = lean_string_append(v___y_2251_, v___y_2255_);
lean_dec_ref(v___y_2255_);
v___x_2257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2258_ = lean_string_append(v___x_2256_, v___x_2257_);
v___x_2259_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2250_, v___y_2253_);
v___x_2260_ = lean_string_append(v___x_2258_, v___x_2259_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = lean_string_append(v___x_2260_, v___y_2249_);
v___y_2237_ = v___y_2252_;
v___y_2238_ = v___y_2254_;
v___y_2239_ = v___x_2261_;
goto v___jp_2236_;
}
v___jp_2262_:
{
lean_object* v___x_2269_; lean_object* v_toString_2270_; 
v___x_2269_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2270_ = lean_ctor_get(v___y_2266_, 0);
lean_inc_ref(v_toString_2270_);
lean_dec_ref(v___y_2266_);
v___y_2249_ = v___y_2268_;
v___y_2250_ = v___y_2263_;
v___y_2251_ = v___x_2269_;
v___y_2252_ = v___y_2264_;
v___y_2253_ = v___y_2265_;
v___y_2254_ = v___y_2267_;
v___y_2255_ = v_toString_2270_;
goto v___jp_2248_;
}
v___jp_2271_:
{
lean_object* v___x_2276_; uint8_t v___x_2277_; 
v___x_2276_ = lean_array_get_size(v_clashes_2274_);
v___x_2277_ = lean_nat_dec_lt(v___x_2235_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_dec_ref(v_clashes_2274_);
lean_dec(v_src_2272_);
if (lean_obj_tag(v_tc_x3f_2273_) == 1)
{
lean_object* v_val_2278_; lean_object* v_rootToolchainFile_2279_; 
v_val_2278_ = lean_ctor_get(v_tc_x3f_2273_, 0);
lean_inc(v_val_2278_);
lean_dec_ref(v_tc_x3f_2273_);
v_rootToolchainFile_2279_ = l_Lake_joinRelative(v_dir_2225_, v___x_2227_);
if (lean_obj_tag(v_a_2230_) == 0)
{
lean_del_object(v___x_2232_);
v___y_2219_ = v_val_2278_;
v___y_2220_ = v_rootToolchainFile_2279_;
v___y_2221_ = v___x_2277_;
goto v___jp_2218_;
}
else
{
lean_object* v_val_2280_; uint8_t v___x_2281_; 
v_val_2280_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_val_2280_);
lean_dec_ref(v_a_2230_);
lean_inc(v_val_2278_);
v___x_2281_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2280_, v_val_2278_);
if (v___x_2281_ == 0)
{
lean_del_object(v___x_2232_);
v___y_2219_ = v_val_2278_;
v___y_2220_ = v_rootToolchainFile_2279_;
v___y_2221_ = v___x_2281_;
goto v___jp_2218_;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_dec_ref(v_rootToolchainFile_2279_);
lean_dec(v_val_2278_);
lean_dec(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_lakeEnv_2071_);
v___x_2282_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2062_);
v___x_2283_ = lean_apply_2(v_a_2062_, v___x_2282_, lean_box(0));
v___x_2284_ = lean_box(0);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2284_);
v___x_2286_ = v___x_2232_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
lean_dec(v_tc_x3f_2273_);
lean_dec(v_a_2230_);
lean_dec_ref(v_dir_2225_);
lean_dec(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_lakeEnv_2071_);
v___x_2288_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2062_);
v___x_2289_ = lean_apply_2(v_a_2062_, v___x_2288_, lean_box(0));
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2289_);
v___x_2291_ = v___x_2232_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
else
{
lean_del_object(v___x_2232_);
lean_dec(v_a_2230_);
lean_dec_ref(v_dir_2225_);
lean_dec(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_lakeEnv_2071_);
if (lean_obj_tag(v_tc_x3f_2273_) == 1)
{
if (v_fixed_2275_ == 0)
{
lean_object* v_val_2293_; lean_object* v___x_2294_; 
v_val_2293_ = lean_ctor_get(v_tc_x3f_2273_, 0);
lean_inc(v_val_2293_);
lean_dec_ref(v_tc_x3f_2273_);
v___x_2294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2263_ = v_src_2272_;
v___y_2264_ = v_clashes_2274_;
v___y_2265_ = v___x_2277_;
v___y_2266_ = v_val_2293_;
v___y_2267_ = v___x_2276_;
v___y_2268_ = v___x_2294_;
goto v___jp_2262_;
}
else
{
lean_object* v_val_2295_; lean_object* v___x_2296_; 
v_val_2295_ = lean_ctor_get(v_tc_x3f_2273_, 0);
lean_inc(v_val_2295_);
lean_dec_ref(v_tc_x3f_2273_);
v___x_2296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2263_ = v_src_2272_;
v___y_2264_ = v_clashes_2274_;
v___y_2265_ = v___x_2277_;
v___y_2266_ = v_val_2295_;
v___y_2267_ = v___x_2276_;
v___y_2268_ = v___x_2296_;
goto v___jp_2262_;
}
}
else
{
lean_object* v___x_2297_; 
lean_dec(v_tc_x3f_2273_);
lean_dec(v_src_2272_);
v___x_2297_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2237_ = v_clashes_2274_;
v___y_2238_ = v___x_2276_;
v___y_2239_ = v___x_2297_;
goto v___jp_2236_;
}
}
}
v___jp_2298_:
{
if (lean_obj_tag(v___y_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v_src_2301_; lean_object* v_tc_x3f_2302_; lean_object* v_clashes_2303_; uint8_t v_fixed_2304_; 
v_a_2300_ = lean_ctor_get(v___y_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___y_2299_);
v_src_2301_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_src_2301_);
v_tc_x3f_2302_ = lean_ctor_get(v_a_2300_, 1);
lean_inc(v_tc_x3f_2302_);
v_clashes_2303_ = lean_ctor_get(v_a_2300_, 2);
lean_inc_ref(v_clashes_2303_);
v_fixed_2304_ = lean_ctor_get_uint8(v_a_2300_, sizeof(void*)*3);
lean_dec(v_a_2300_);
v_src_2272_ = v_src_2301_;
v_tc_x3f_2273_ = v_tc_x3f_2302_;
v_clashes_2274_ = v_clashes_2303_;
v_fixed_2275_ = v_fixed_2304_;
goto v___jp_2271_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_del_object(v___x_2232_);
lean_dec(v_a_2230_);
lean_dec_ref(v_dir_2225_);
lean_dec(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_lakeEnv_2071_);
v_a_2305_ = lean_ctor_get(v___y_2299_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___y_2299_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___y_2299_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___y_2299_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2337_; 
lean_dec_ref(v_config_2226_);
lean_dec_ref(v_dir_2225_);
lean_dec(v_baseName_2224_);
lean_dec(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_lakeEnv_2071_);
v_a_2325_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2327_ = v___x_2229_;
v_isShared_2328_ = v_isSharedCheck_2337_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2229_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2337_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2329_ = lean_io_error_to_string(v_a_2325_);
v___x_2330_ = 3;
v___x_2331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*1, v___x_2330_);
lean_inc_ref(v_a_2062_);
v___x_2332_ = lean_apply_2(v_a_2062_, v___x_2331_, lean_box(0));
v___x_2333_ = lean_box(0);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2333_);
v___x_2335_ = v___x_2327_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
v___jp_2064_:
{
uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = 2;
v___x_2067_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2067_, 0, v___y_2065_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*1, v___x_2066_);
lean_inc_ref(v_a_2062_);
v___x_2068_ = lean_apply_2(v_a_2062_, v___x_2067_, lean_box(0));
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
v___jp_2073_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_inc_ref(v___y_2076_);
v___x_2078_ = lean_string_append(v___y_2076_, v___y_2077_);
v___x_2079_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
v___x_2081_ = 1;
v___x_2082_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*1, v___x_2081_);
lean_inc_ref(v_a_2062_);
v___x_2083_ = lean_apply_2(v_a_2062_, v___x_2082_, lean_box(0));
v___x_2084_ = l_IO_FS_writeFile(v___y_2075_, v___y_2077_);
lean_dec_ref(v___y_2075_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_dec_ref(v___x_2084_);
if (lean_obj_tag(v_lakeArgs_x3f_2072_) == 1)
{
lean_object* v_elan_x3f_2085_; 
v_elan_x3f_2085_ = lean_ctor_get(v_lakeEnv_2071_, 2);
if (lean_obj_tag(v_elan_x3f_2085_) == 1)
{
lean_object* v_val_2086_; lean_object* v_val_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_elan_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_val_2086_ = lean_ctor_get(v_lakeArgs_x3f_2072_, 0);
lean_inc(v_val_2086_);
lean_dec_ref(v_lakeArgs_x3f_2072_);
v_val_2087_ = lean_ctor_get(v_elan_x3f_2085_, 0);
v___x_2088_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2062_);
v___x_2089_ = lean_apply_2(v_a_2062_, v___x_2088_, lean_box(0));
v___x_2090_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2091_ = lean_ctor_get(v_val_2087_, 1);
lean_inc_ref(v_elan_2091_);
v___x_2092_ = 1;
v___x_2093_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2094_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2095_ = lean_array_push(v___x_2094_, v___y_2077_);
v___x_2096_ = lean_array_push(v___x_2095_, v___x_2093_);
v___x_2097_ = l_Array_append___redArg(v___x_2096_, v_val_2086_);
lean_dec(v_val_2086_);
v___x_2098_ = lean_box(0);
v___x_2099_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2071_);
v___x_2100_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2100_, 0, v___x_2090_);
lean_ctor_set(v___x_2100_, 1, v_elan_2091_);
lean_ctor_set(v___x_2100_, 2, v___x_2097_);
lean_ctor_set(v___x_2100_, 3, v___x_2098_);
lean_ctor_set(v___x_2100_, 4, v___x_2099_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*5, v___x_2092_);
lean_ctor_set_uint8(v___x_2100_, sizeof(void*)*5 + 1, v___y_2074_);
v___x_2101_ = lean_io_process_spawn(v___x_2100_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
v___x_2103_ = lean_io_process_child_wait(v___x_2090_, v_a_2102_);
lean_dec(v_a_2102_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; uint32_t v___x_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v___x_2105_ = lean_unbox_uint32(v_a_2104_);
lean_dec(v_a_2104_);
v___x_2106_ = lean_uint32_to_uint8(v___x_2105_);
v___x_2107_ = lean_io_exit(v___x_2106_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2128_; 
v_a_2116_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2118_ = v___x_2107_;
v_isShared_2119_ = v_isSharedCheck_2128_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2107_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2128_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2120_ = lean_io_error_to_string(v_a_2116_);
v___x_2121_ = 3;
v___x_2122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*1, v___x_2121_);
lean_inc_ref(v_a_2062_);
v___x_2123_ = lean_apply_2(v_a_2062_, v___x_2122_, lean_box(0));
v___x_2124_ = lean_box(0);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2124_);
v___x_2126_ = v___x_2118_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2141_; 
v_a_2129_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2131_ = v___x_2103_;
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2103_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2133_ = lean_io_error_to_string(v_a_2129_);
v___x_2134_ = 3;
v___x_2135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*1, v___x_2134_);
lean_inc_ref(v_a_2062_);
v___x_2136_ = lean_apply_2(v_a_2062_, v___x_2135_, lean_box(0));
v___x_2137_ = lean_box(0);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2137_);
v___x_2139_ = v___x_2131_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2154_; 
v_a_2142_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2144_ = v___x_2101_;
v_isShared_2145_ = v_isSharedCheck_2154_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2101_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2154_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2146_ = lean_io_error_to_string(v_a_2142_);
v___x_2147_ = 3;
v___x_2148_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*1, v___x_2147_);
lean_inc_ref(v_a_2062_);
v___x_2149_ = lean_apply_2(v_a_2062_, v___x_2148_, lean_box(0));
v___x_2150_ = lean_box(0);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2150_);
v___x_2152_ = v___x_2144_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v_lakeArgs_x3f_2072_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v_lakeEnv_2071_);
v___x_2155_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2062_);
v___x_2156_ = lean_apply_2(v_a_2062_, v___x_2155_, lean_box(0));
v___x_2157_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2158_ = lean_io_exit(v___x_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2179_; 
v_a_2167_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2169_ = v___x_2158_;
v_isShared_2170_ = v_isSharedCheck_2179_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2158_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2179_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2171_ = lean_io_error_to_string(v_a_2167_);
v___x_2172_ = 3;
v___x_2173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*1, v___x_2172_);
lean_inc_ref(v_a_2062_);
v___x_2174_ = lean_apply_2(v_a_2062_, v___x_2173_, lean_box(0));
v___x_2175_ = lean_box(0);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2175_);
v___x_2177_ = v___x_2169_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v___y_2077_);
lean_dec(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_lakeEnv_2071_);
v___x_2180_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2062_);
v___x_2181_ = lean_apply_2(v_a_2062_, v___x_2180_, lean_box(0));
v___x_2182_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2183_ = lean_io_exit(v___x_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2204_; 
v_a_2192_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2194_ = v___x_2183_;
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2183_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2204_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2196_ = lean_io_error_to_string(v_a_2192_);
v___x_2197_ = 3;
v___x_2198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*1, v___x_2197_);
lean_inc_ref(v_a_2062_);
v___x_2199_ = lean_apply_2(v_a_2062_, v___x_2198_, lean_box(0));
v___x_2200_ = lean_box(0);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2200_);
v___x_2202_ = v___x_2194_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v___y_2077_);
lean_dec(v_lakeArgs_x3f_2072_);
lean_dec_ref(v_lakeEnv_2071_);
v_a_2205_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2207_ = v___x_2084_;
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2084_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2217_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2209_ = lean_io_error_to_string(v_a_2205_);
v___x_2210_ = 3;
v___x_2211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*1, v___x_2210_);
lean_inc_ref(v_a_2062_);
v___x_2212_ = lean_apply_2(v_a_2062_, v___x_2211_, lean_box(0));
v___x_2213_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2213_);
v___x_2215_ = v___x_2207_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
v___jp_2218_:
{
lean_object* v___x_2222_; lean_object* v_toString_2223_; 
v___x_2222_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2223_ = lean_ctor_get(v___y_2219_, 0);
lean_inc_ref(v_toString_2223_);
lean_dec_ref(v___y_2219_);
v___y_2074_ = v___y_2221_;
v___y_2075_ = v___y_2220_;
v___y_2076_ = v___x_2222_;
v___y_2077_ = v_toString_2223_;
goto v___jp_2073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_2338_, lean_object* v_rootDeps_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_2338_, v_rootDeps_2339_, v_a_2340_);
lean_dec_ref(v_a_2340_);
lean_dec_ref(v_rootDeps_2339_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(lean_object* v_pkg_2343_, lean_object* v_dep_2344_, lean_object* v_ws_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_2345_, v_pkg_2343_, v_dep_2344_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v_fst_2351_; lean_object* v_snd_2352_; lean_object* v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v_fst_2351_ = lean_ctor_get(v_a_2350_, 0);
lean_inc_n(v_fst_2351_, 2);
v_snd_2352_ = lean_ctor_get(v_a_2350_, 1);
lean_inc(v_snd_2352_);
lean_dec(v_a_2350_);
v___x_2353_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_2351_, v_snd_2352_, v_a_2347_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2370_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2370_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2370_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_snd_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2368_; 
v_snd_2358_ = lean_ctor_get(v_a_2354_, 1);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_a_2354_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; 
v_unused_2369_ = lean_ctor_get(v_a_2354_, 0);
lean_dec(v_unused_2369_);
v___x_2360_ = v_a_2354_;
v_isShared_2361_ = v_isSharedCheck_2368_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_snd_2358_);
lean_dec(v_a_2354_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2368_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v_fst_2351_);
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_fst_2351_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_snd_2358_);
v___x_2363_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2363_);
v___x_2365_ = v___x_2356_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec(v_fst_2351_);
v_a_2371_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2353_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2353_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
else
{
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep___boxed(lean_object* v_pkg_2379_, lean_object* v_dep_2380_, lean_object* v_ws_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndAddDep(v_pkg_2379_, v_dep_2380_, v_ws_2381_, v_a_2382_, v_a_2383_);
lean_dec_ref(v_a_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2386_, lean_object* v_ws_2387_, lean_object* v_pkg_2388_, lean_object* v_dep_2389_, lean_object* v_a_2390_){
_start:
{
uint8_t v___y_2393_; lean_object* v___y_2394_; lean_object* v_name_2422_; lean_object* v___x_2423_; 
v_name_2422_ = lean_ctor_get(v_dep_2389_, 0);
v___x_2423_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2390_, v_name_2422_);
if (lean_obj_tag(v___x_2423_) == 1)
{
lean_object* v_root_2424_; lean_object* v_config_2425_; lean_object* v_val_2426_; lean_object* v_lakeEnv_2427_; lean_object* v_dir_2428_; lean_object* v_toWorkspaceConfig_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref(v_dep_2389_);
lean_dec_ref(v_pkg_2388_);
v_root_2424_ = lean_ctor_get(v_ws_2387_, 0);
lean_inc_ref(v_root_2424_);
v_config_2425_ = lean_ctor_get(v_root_2424_, 6);
lean_inc_ref(v_config_2425_);
v_val_2426_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_val_2426_);
lean_dec_ref(v___x_2423_);
v_lakeEnv_2427_ = lean_ctor_get(v_ws_2387_, 1);
lean_inc_ref(v_lakeEnv_2427_);
lean_dec_ref(v_ws_2387_);
v_dir_2428_ = lean_ctor_get(v_root_2424_, 4);
lean_inc_ref(v_dir_2428_);
lean_dec_ref(v_root_2424_);
v_toWorkspaceConfig_2429_ = lean_ctor_get(v_config_2425_, 0);
lean_inc_ref(v_toWorkspaceConfig_2429_);
lean_dec_ref(v_config_2425_);
v___x_2430_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2429_);
v___x_2431_ = l_Lake_PackageEntry_materialize(v_val_2426_, v_lakeEnv_2427_, v_dir_2428_, v___x_2430_, v___y_2386_);
lean_dec_ref(v_lakeEnv_2427_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2440_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2440_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_a_2432_);
lean_ctor_set(v___x_2436_, 1, v_a_2390_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2436_);
v___x_2438_ = v___x_2434_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v_a_2390_);
v_a_2441_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2431_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2431_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
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
else
{
lean_object* v_wsIdx_2449_; lean_object* v_relDir_2450_; uint8_t v___y_2452_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
lean_dec(v___x_2423_);
v_wsIdx_2449_ = lean_ctor_get(v_pkg_2388_, 0);
lean_inc(v_wsIdx_2449_);
v_relDir_2450_ = lean_ctor_get(v_pkg_2388_, 5);
lean_inc_ref(v_relDir_2450_);
lean_dec_ref(v_pkg_2388_);
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_nat_dec_eq(v_wsIdx_2449_, v___x_2456_);
lean_dec(v_wsIdx_2449_);
if (v___x_2457_ == 0)
{
uint8_t v___x_2458_; 
v___x_2458_ = 1;
v___y_2452_ = v___x_2458_;
goto v___jp_2451_;
}
else
{
uint8_t v___x_2459_; 
v___x_2459_ = 0;
v___y_2452_ = v___x_2459_;
goto v___jp_2451_;
}
v___jp_2451_:
{
lean_object* v___x_2453_; uint8_t v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2454_ = lean_string_dec_eq(v_relDir_2450_, v___x_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lake_joinRelative(v_relDir_2450_, v___x_2453_);
v___y_2393_ = v___y_2452_;
v___y_2394_ = v___x_2455_;
goto v___jp_2392_;
}
else
{
v___y_2393_ = v___y_2452_;
v___y_2394_ = v_relDir_2450_;
goto v___jp_2392_;
}
}
}
v___jp_2392_:
{
lean_object* v_root_2395_; lean_object* v_config_2396_; lean_object* v_lakeEnv_2397_; lean_object* v_dir_2398_; lean_object* v_toWorkspaceConfig_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_root_2395_ = lean_ctor_get(v_ws_2387_, 0);
lean_inc_ref(v_root_2395_);
v_config_2396_ = lean_ctor_get(v_root_2395_, 6);
lean_inc_ref(v_config_2396_);
v_lakeEnv_2397_ = lean_ctor_get(v_ws_2387_, 1);
lean_inc_ref(v_lakeEnv_2397_);
lean_dec_ref(v_ws_2387_);
v_dir_2398_ = lean_ctor_get(v_root_2395_, 4);
lean_inc_ref(v_dir_2398_);
lean_dec_ref(v_root_2395_);
v_toWorkspaceConfig_2399_ = lean_ctor_get(v_config_2396_, 0);
lean_inc_ref(v_toWorkspaceConfig_2399_);
lean_dec_ref(v_config_2396_);
v___x_2400_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2399_);
v___x_2401_ = l_Lake_Dependency_materialize(v_dep_2389_, v___y_2393_, v_lakeEnv_2397_, v_dir_2398_, v___x_2400_, v___y_2394_, v___y_2386_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2413_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v_manifestEntry_2406_; lean_object* v_name_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v_manifestEntry_2406_ = lean_ctor_get(v_a_2402_, 4);
v_name_2407_ = lean_ctor_get(v_manifestEntry_2406_, 0);
lean_inc_ref(v_manifestEntry_2406_);
lean_inc(v_name_2407_);
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2407_, v_manifestEntry_2406_, v_a_2390_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_a_2402_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2409_);
v___x_2411_ = v___x_2404_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_a_2390_);
v_a_2414_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2401_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2401_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2460_, lean_object* v_ws_2461_, lean_object* v_pkg_2462_, lean_object* v_dep_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2460_, v_ws_2461_, v_pkg_2462_, v_dep_2463_, v_a_2464_);
lean_dec_ref(v___y_2460_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2467_, lean_object* v_dep_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v_manifestEntry_2471_; lean_object* v_pkgDir_2472_; lean_object* v_name_2473_; lean_object* v_manifestFile_x3f_2474_; lean_object* v___y_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v_val_2538_; lean_object* v___y_2566_; 
v_manifestEntry_2471_ = lean_ctor_get(v_dep_2468_, 4);
v_pkgDir_2472_ = lean_ctor_get(v_dep_2468_, 0);
v_name_2473_ = lean_ctor_get(v_manifestEntry_2471_, 0);
v_manifestFile_x3f_2474_ = lean_ctor_get(v_manifestEntry_2471_, 3);
if (lean_obj_tag(v_manifestFile_x3f_2474_) == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = l_Lake_defaultManifestFile;
lean_inc_ref(v_pkgDir_2472_);
v___x_2587_ = l_Lake_joinRelative(v_pkgDir_2472_, v___x_2586_);
v___y_2566_ = v___x_2587_;
goto v___jp_2565_;
}
else
{
lean_object* v_val_2588_; lean_object* v___x_2589_; 
v_val_2588_ = lean_ctor_get(v_manifestFile_x3f_2474_, 0);
lean_inc(v_val_2588_);
lean_inc_ref(v_pkgDir_2472_);
v___x_2589_ = l_Lake_joinRelative(v_pkgDir_2472_, v_val_2588_);
v___y_2566_ = v___x_2589_;
goto v___jp_2565_;
}
v___jp_2475_:
{
if (lean_obj_tag(v_fst_2477_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2508_; 
lean_inc(v_name_2473_);
lean_dec_ref(v_dep_2468_);
v_a_2479_ = lean_ctor_get(v_fst_2477_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_fst_2477_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2481_ = v_fst_2477_;
v_isShared_2482_ = v_isSharedCheck_2508_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v_fst_2477_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2508_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
if (lean_obj_tag(v_a_2479_) == 11)
{
uint8_t v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec_ref(v_a_2479_);
v___x_2483_ = 0;
v___x_2484_ = l_Lean_Name_toString(v_name_2473_, v___x_2483_);
v___x_2485_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2486_ = lean_string_append(v___x_2484_, v___x_2485_);
v___x_2487_ = lean_string_append(v___x_2486_, v___y_2476_);
lean_dec_ref(v___y_2476_);
v___x_2488_ = 2;
v___x_2489_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*1, v___x_2488_);
v___x_2490_ = lean_apply_2(v___y_2467_, v___x_2489_, lean_box(0));
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
lean_ctor_set(v___x_2491_, 1, v_snd_2478_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2491_);
v___x_2493_ = v___x_2481_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
else
{
uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
lean_dec_ref(v___y_2476_);
v___x_2495_ = 0;
v___x_2496_ = l_Lean_Name_toString(v_name_2473_, v___x_2495_);
v___x_2497_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2498_ = lean_string_append(v___x_2496_, v___x_2497_);
v___x_2499_ = lean_io_error_to_string(v_a_2479_);
v___x_2500_ = lean_string_append(v___x_2498_, v___x_2499_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = 2;
v___x_2502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set_uint8(v___x_2502_, sizeof(void*)*1, v___x_2501_);
v___x_2503_ = lean_apply_2(v___y_2467_, v___x_2502_, lean_box(0));
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v_snd_2478_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2504_);
v___x_2506_ = v___x_2481_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___y_2467_);
v_a_2509_ = lean_ctor_get(v_fst_2477_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_fst_2477_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2511_ = v_fst_2477_;
v_isShared_2512_ = v_isSharedCheck_2533_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v_fst_2477_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2533_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_packages_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_packages_2513_ = lean_ctor_get(v_a_2509_, 3);
lean_inc_ref(v_packages_2513_);
lean_dec(v_a_2509_);
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = lean_array_get_size(v_packages_2513_);
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_nat_dec_lt(v___x_2514_, v___x_2515_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_dec_ref(v_packages_2513_);
lean_dec_ref(v_dep_2468_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v_snd_2478_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2518_);
v___x_2520_ = v___x_2511_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
else
{
uint8_t v___x_2522_; 
v___x_2522_ = lean_nat_dec_le(v___x_2515_, v___x_2515_);
if (v___x_2522_ == 0)
{
if (v___x_2517_ == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_dec_ref(v_packages_2513_);
lean_dec_ref(v_dep_2468_);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2516_);
lean_ctor_set(v___x_2523_, 1, v_snd_2478_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2523_);
v___x_2525_ = v___x_2511_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
else
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
lean_del_object(v___x_2511_);
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2515_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2468_, v_packages_2513_, v___x_2527_, v___x_2528_, v___x_2516_, v_snd_2478_);
lean_dec_ref(v_packages_2513_);
return v___x_2529_;
}
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
lean_del_object(v___x_2511_);
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = lean_usize_of_nat(v___x_2515_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_dep_2468_, v_packages_2513_, v___x_2530_, v___x_2531_, v___x_2516_, v_snd_2478_);
lean_dec_ref(v_packages_2513_);
return v___x_2532_;
}
}
}
}
}
v___jp_2534_:
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = lean_array_get_size(v___y_2537_);
v___x_2540_ = lean_nat_dec_lt(v___y_2536_, v___x_2539_);
if (v___x_2540_ == 0)
{
v___y_2476_ = v___y_2535_;
v_fst_2477_ = v_val_2538_;
v_snd_2478_ = v_a_2469_;
goto v___jp_2475_;
}
else
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_nat_dec_le(v___x_2539_, v___x_2539_);
if (v___x_2542_ == 0)
{
if (v___x_2540_ == 0)
{
v___y_2476_ = v___y_2535_;
v_fst_2477_ = v_val_2538_;
v_snd_2478_ = v_a_2469_;
goto v___jp_2475_;
}
else
{
size_t v___x_2543_; size_t v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = lean_usize_of_nat(v___x_2539_);
v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2537_, v___x_2543_, v___x_2544_, v___x_2541_, v___y_2467_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_dec_ref(v___x_2545_);
v___y_2476_ = v___y_2535_;
v_fst_2477_ = v_val_2538_;
v_snd_2478_ = v_a_2469_;
goto v___jp_2475_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_val_2538_);
lean_dec_ref(v___y_2535_);
lean_dec(v_a_2469_);
lean_dec_ref(v_dep_2468_);
lean_dec_ref(v___y_2467_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
else
{
size_t v___x_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = lean_usize_of_nat(v___x_2539_);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2537_, v___x_2554_, v___x_2555_, v___x_2541_, v___y_2467_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_dec_ref(v___x_2556_);
v___y_2476_ = v___y_2535_;
v_fst_2477_ = v_val_2538_;
v_snd_2478_ = v_a_2469_;
goto v___jp_2475_;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_val_2538_);
lean_dec_ref(v___y_2535_);
lean_dec(v_a_2469_);
lean_dec_ref(v_dep_2468_);
lean_dec_ref(v___y_2467_);
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
v___jp_2565_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___y_2566_);
v___x_2569_ = l_Lake_Manifest_load(v___y_2566_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 1);
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
v___y_2535_ = v___y_2566_;
v___y_2536_ = v___x_2567_;
v___y_2537_ = v___x_2568_;
v_val_2538_ = v___x_2575_;
goto v___jp_2534_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
v_a_2578_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2569_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2569_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 0);
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
v___y_2535_ = v___y_2566_;
v___y_2536_ = v___x_2567_;
v___y_2537_ = v___x_2568_;
v_val_2538_ = v___x_2583_;
goto v___jp_2534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2590_, lean_object* v_dep_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2590_, v_dep_2591_, v_a_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2599_, v___y_2597_, v___y_2595_, v___y_2596_, v___y_2598_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v_fst_2603_; lean_object* v_snd_2604_; lean_object* v___x_2605_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2601_);
v_fst_2603_ = lean_ctor_get(v_a_2602_, 0);
lean_inc_n(v_fst_2603_, 2);
v_snd_2604_ = lean_ctor_get(v_a_2602_, 1);
lean_inc(v_snd_2604_);
lean_dec(v_a_2602_);
v___x_2605_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2599_, v_fst_2603_, v_snd_2604_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2622_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2622_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2622_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_snd_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2620_; 
v_snd_2610_ = lean_ctor_get(v_a_2606_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_a_2606_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v_a_2606_, 0);
lean_dec(v_unused_2621_);
v___x_2612_ = v_a_2606_;
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snd_2610_);
lean_dec(v_a_2606_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2620_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_fst_2603_);
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_fst_2603_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_snd_2610_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2615_);
v___x_2617_ = v___x_2608_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_fst_2603_);
v_a_2623_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2605_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2605_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_dec_ref(v___y_2599_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(lean_object* v_a_2638_, lean_object* v_ws_2639_, lean_object* v_toUpdate_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___y_2644_; lean_object* v___y_2649_; lean_object* v_fst_2650_; lean_object* v_snd_2651_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v_val_2675_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2707_; lean_object* v_root_2724_; lean_object* v_baseName_2725_; lean_object* v_dir_2726_; lean_object* v_config_2727_; lean_object* v_relManifestFile_2728_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; uint8_t v_fst_2733_; lean_object* v_snd_2734_; lean_object* v_packagesDir_x3f_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v___x_2801_; lean_object* v_rootName_2802_; lean_object* v_fst_2804_; lean_object* v_snd_2805_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v_val_2857_; lean_object* v___x_2883_; 
v_root_2724_ = lean_ctor_get(v_ws_2639_, 0);
lean_inc_ref(v_root_2724_);
lean_dec_ref(v_ws_2639_);
v_baseName_2725_ = lean_ctor_get(v_root_2724_, 1);
lean_inc(v_baseName_2725_);
v_dir_2726_ = lean_ctor_get(v_root_2724_, 4);
lean_inc_ref_n(v_dir_2726_, 2);
v_config_2727_ = lean_ctor_get(v_root_2724_, 6);
lean_inc_ref(v_config_2727_);
v_relManifestFile_2728_ = lean_ctor_get(v_root_2724_, 9);
lean_inc_ref(v_relManifestFile_2728_);
lean_dec_ref(v_root_2724_);
v___x_2801_ = 0;
v_rootName_2802_ = l_Lean_Name_toString(v_baseName_2725_, v___x_2801_);
v___x_2854_ = l_Lake_joinRelative(v_dir_2726_, v_relManifestFile_2728_);
v___x_2855_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2883_ = l_Lake_Manifest_load(v___x_2854_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2883_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
lean_ctor_set_tag(v___x_2886_, 1);
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
v_val_2857_ = v___x_2889_;
goto v___jp_2856_;
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_a_2892_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2883_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2883_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 0);
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
v_val_2857_ = v___x_2897_;
goto v___jp_2856_;
}
}
}
v___jp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2645_ = lean_box(0);
v___x_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
lean_ctor_set(v___x_2646_, 1, v___y_2644_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
v___jp_2648_:
{
if (lean_obj_tag(v_fst_2650_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_snd_2651_);
v_a_2652_ = lean_ctor_get(v_fst_2650_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_fst_2650_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2654_ = v_fst_2650_;
v_isShared_2655_ = v_isSharedCheck_2666_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v_fst_2650_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2666_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2656_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2657_ = lean_io_error_to_string(v_a_2652_);
v___x_2658_ = lean_string_append(v___x_2656_, v___x_2657_);
lean_dec_ref(v___x_2657_);
v___x_2659_ = 3;
v___x_2660_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set_uint8(v___x_2660_, sizeof(void*)*1, v___x_2659_);
lean_inc_ref(v___y_2649_);
v___x_2661_ = lean_apply_2(v___y_2649_, v___x_2660_, lean_box(0));
v___x_2662_ = lean_box(0);
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 1);
lean_ctor_set(v___x_2654_, 0, v___x_2662_);
v___x_2664_ = v___x_2654_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec_ref(v_fst_2650_);
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v_snd_2651_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
return v___x_2669_;
}
}
v___jp_2670_:
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = lean_array_get_size(v___y_2674_);
v___x_2677_ = lean_nat_dec_lt(v___y_2673_, v___x_2676_);
if (v___x_2677_ == 0)
{
v___y_2649_ = v___y_2671_;
v_fst_2650_ = v_val_2675_;
v_snd_2651_ = v___y_2672_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2678_ = lean_box(0);
v___x_2679_ = lean_nat_dec_le(v___x_2676_, v___x_2676_);
if (v___x_2679_ == 0)
{
if (v___x_2677_ == 0)
{
v___y_2649_ = v___y_2671_;
v_fst_2650_ = v_val_2675_;
v_snd_2651_ = v___y_2672_;
goto v___jp_2648_;
}
else
{
size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = lean_usize_of_nat(v___x_2676_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2674_, v___x_2680_, v___x_2681_, v___x_2678_, v___y_2671_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_dec_ref(v___x_2682_);
v___y_2649_ = v___y_2671_;
v_fst_2650_ = v_val_2675_;
v_snd_2651_ = v___y_2672_;
goto v___jp_2648_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_val_2675_);
lean_dec(v___y_2672_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
else
{
size_t v___x_2691_; size_t v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = lean_usize_of_nat(v___x_2676_);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2674_, v___x_2691_, v___x_2692_, v___x_2678_, v___y_2671_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_dec_ref(v___x_2693_);
v___y_2649_ = v___y_2671_;
v_fst_2650_ = v_val_2675_;
v_snd_2651_ = v___y_2672_;
goto v___jp_2648_;
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_val_2675_);
lean_dec(v___y_2672_);
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
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
}
}
v___jp_2702_:
{
if (lean_obj_tag(v___y_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_a_2708_ = lean_ctor_get(v___y_2707_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___y_2707_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___y_2707_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___y_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 1);
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
v___y_2671_ = v___y_2704_;
v___y_2672_ = v___y_2703_;
v___y_2673_ = v___y_2706_;
v___y_2674_ = v___y_2705_;
v_val_2675_ = v___x_2713_;
goto v___jp_2670_;
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_a_2716_ = lean_ctor_get(v___y_2707_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___y_2707_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___y_2707_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___y_2707_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 0);
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
v___y_2671_ = v___y_2704_;
v___y_2672_ = v___y_2703_;
v___y_2673_ = v___y_2706_;
v___y_2674_ = v___y_2705_;
v_val_2675_ = v___x_2721_;
goto v___jp_2670_;
}
}
}
}
v___jp_2729_:
{
lean_object* v_toWorkspaceConfig_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_toWorkspaceConfig_2735_ = lean_ctor_get(v_config_2727_, 0);
lean_inc_ref(v_toWorkspaceConfig_2735_);
lean_dec_ref(v_config_2727_);
v___x_2736_ = l_System_FilePath_normalize(v___y_2731_);
v___x_2737_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2735_);
lean_inc_ref(v___x_2737_);
v___x_2738_ = l_System_FilePath_normalize(v___x_2737_);
v___x_2739_ = lean_string_dec_eq(v___x_2736_, v___x_2738_);
lean_dec_ref(v___x_2738_);
lean_dec_ref(v___x_2736_);
if (v___x_2739_ == 0)
{
if (v_fst_2733_ == 0)
{
lean_dec_ref(v___x_2737_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v_dir_2726_);
v___y_2644_ = v_snd_2734_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2740_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2741_ = lean_string_append(v___x_2740_, v___y_2732_);
v___x_2742_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2743_ = lean_string_append(v___x_2741_, v___x_2742_);
v___x_2744_ = l_Lake_joinRelative(v_dir_2726_, v___x_2737_);
v___x_2745_ = lean_string_append(v___x_2743_, v___x_2744_);
v___x_2746_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2747_ = lean_string_append(v___x_2745_, v___x_2746_);
v___x_2748_ = 1;
v___x_2749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*1, v___x_2748_);
lean_inc_ref(v___y_2730_);
v___x_2750_ = lean_apply_2(v___y_2730_, v___x_2749_, lean_box(0));
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2744_);
v___x_2753_ = l_Lake_createParentDirs(v___x_2744_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v___x_2754_; 
lean_dec_ref(v___x_2753_);
v___x_2754_ = lean_io_rename(v___y_2732_, v___x_2744_);
lean_dec_ref(v___x_2744_);
lean_dec_ref(v___y_2732_);
v___y_2703_ = v_snd_2734_;
v___y_2704_ = v___y_2730_;
v___y_2705_ = v___x_2752_;
v___y_2706_ = v___x_2751_;
v___y_2707_ = v___x_2754_;
goto v___jp_2702_;
}
else
{
lean_dec_ref(v___x_2744_);
lean_dec_ref(v___y_2732_);
v___y_2703_ = v_snd_2734_;
v___y_2704_ = v___y_2730_;
v___y_2705_ = v___x_2752_;
v___y_2706_ = v___x_2751_;
v___y_2707_ = v___x_2753_;
goto v___jp_2702_;
}
}
}
else
{
lean_dec_ref(v___x_2737_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v_dir_2726_);
v___y_2644_ = v_snd_2734_;
goto v___jp_2643_;
}
}
v___jp_2755_:
{
if (lean_obj_tag(v_packagesDir_x3f_2756_) == 1)
{
lean_object* v_val_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_val_2759_ = lean_ctor_get(v_packagesDir_x3f_2756_, 0);
lean_inc_n(v_val_2759_, 2);
lean_dec_ref(v_packagesDir_x3f_2756_);
lean_inc_ref(v_dir_2726_);
v___x_2760_ = l_Lake_joinRelative(v_dir_2726_, v_val_2759_);
v___x_2761_ = l_System_FilePath_pathExists(v___x_2760_);
v___x_2762_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2763_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2763_ == 0)
{
v___y_2730_ = v___y_2758_;
v___y_2731_ = v_val_2759_;
v___y_2732_ = v___x_2760_;
v_fst_2733_ = v___x_2761_;
v_snd_2734_ = v___y_2757_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = lean_box(0);
v___x_2765_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2765_ == 0)
{
if (v___x_2763_ == 0)
{
v___y_2730_ = v___y_2758_;
v___y_2731_ = v_val_2759_;
v___y_2732_ = v___x_2760_;
v_fst_2733_ = v___x_2761_;
v_snd_2734_ = v___y_2757_;
goto v___jp_2729_;
}
else
{
size_t v___x_2766_; size_t v___x_2767_; lean_object* v___x_2768_; 
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2762_, v___x_2766_, v___x_2767_, v___x_2764_, v___y_2758_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_dec_ref(v___x_2768_);
v___y_2730_ = v___y_2758_;
v___y_2731_ = v_val_2759_;
v___y_2732_ = v___x_2760_;
v_fst_2733_ = v___x_2761_;
v_snd_2734_ = v___y_2757_;
goto v___jp_2729_;
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v___x_2760_);
lean_dec(v_val_2759_);
lean_dec(v___y_2757_);
lean_dec_ref(v_config_2727_);
lean_dec_ref(v_dir_2726_);
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
else
{
size_t v___x_2777_; size_t v___x_2778_; lean_object* v___x_2779_; 
v___x_2777_ = ((size_t)0ULL);
v___x_2778_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2762_, v___x_2777_, v___x_2778_, v___x_2764_, v___y_2758_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_dec_ref(v___x_2779_);
v___y_2730_ = v___y_2758_;
v___y_2731_ = v_val_2759_;
v___y_2732_ = v___x_2760_;
v_fst_2733_ = v___x_2761_;
v_snd_2734_ = v___y_2757_;
goto v___jp_2729_;
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v___x_2760_);
lean_dec(v_val_2759_);
lean_dec(v___y_2757_);
lean_dec_ref(v_config_2727_);
lean_dec_ref(v_dir_2726_);
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec(v_packagesDir_x3f_2756_);
lean_dec_ref(v_config_2727_);
lean_dec_ref(v_dir_2726_);
v___x_2788_ = lean_box(0);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___y_2757_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
v___jp_2791_:
{
lean_object* v_packagesDir_x3f_2795_; 
v_packagesDir_x3f_2795_ = lean_ctor_get(v___y_2792_, 2);
lean_inc(v_packagesDir_x3f_2795_);
lean_dec_ref(v___y_2792_);
v_packagesDir_x3f_2756_ = v_packagesDir_x3f_2795_;
v___y_2757_ = v___y_2793_;
v___y_2758_ = v___y_2794_;
goto v___jp_2755_;
}
v___jp_2796_:
{
if (lean_obj_tag(v___y_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v_snd_2800_; 
v_a_2799_ = lean_ctor_get(v___y_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___y_2798_);
v_snd_2800_ = lean_ctor_get(v_a_2799_, 1);
lean_inc(v_snd_2800_);
lean_dec(v_a_2799_);
v___y_2792_ = v___y_2797_;
v___y_2793_ = v_snd_2800_;
v___y_2794_ = v_a_2638_;
goto v___jp_2791_;
}
else
{
lean_dec_ref(v___y_2797_);
lean_dec_ref(v_config_2727_);
lean_dec_ref(v_dir_2726_);
return v___y_2798_;
}
}
v___jp_2803_:
{
if (lean_obj_tag(v_fst_2804_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref(v_config_2727_);
lean_dec_ref(v_dir_2726_);
v_a_2806_ = lean_ctor_get(v_fst_2804_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_fst_2804_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2808_ = v_fst_2804_;
v_isShared_2809_ = v_isSharedCheck_2838_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v_fst_2804_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2838_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
if (lean_obj_tag(v_a_2806_) == 11)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_dec_ref(v_a_2806_);
v___x_2810_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2811_ = lean_string_append(v_rootName_2802_, v___x_2810_);
v___x_2812_ = 1;
v___x_2813_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*1, v___x_2812_);
lean_inc_ref(v_a_2638_);
v___x_2814_ = lean_apply_2(v_a_2638_, v___x_2813_, lean_box(0));
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_snd_2805_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2815_);
v___x_2817_ = v___x_2808_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2640_) == 0)
{
lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_dec(v_snd_2805_);
lean_dec_ref(v_rootName_2802_);
v___x_2819_ = lean_io_error_to_string(v_a_2806_);
v___x_2820_ = 3;
v___x_2821_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set_uint8(v___x_2821_, sizeof(void*)*1, v___x_2820_);
lean_inc_ref(v_a_2638_);
v___x_2822_ = lean_apply_2(v_a_2638_, v___x_2821_, lean_box(0));
v___x_2823_ = lean_box(0);
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 1);
lean_ctor_set(v___x_2808_, 0, v___x_2823_);
v___x_2825_ = v___x_2808_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2827_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_2828_ = lean_string_append(v_rootName_2802_, v___x_2827_);
v___x_2829_ = lean_io_error_to_string(v_a_2806_);
v___x_2830_ = lean_string_append(v___x_2828_, v___x_2829_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = 2;
v___x_2832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set_uint8(v___x_2832_, sizeof(void*)*1, v___x_2831_);
lean_inc_ref(v_a_2638_);
v___x_2833_ = lean_apply_2(v_a_2638_, v___x_2832_, lean_box(0));
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
lean_ctor_set(v___x_2834_, 1, v_snd_2805_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2834_);
v___x_2836_ = v___x_2808_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_2802_);
if (lean_obj_tag(v_toUpdate_2640_) == 0)
{
lean_object* v_a_2839_; lean_object* v_packagesDir_x3f_2840_; lean_object* v_packages_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v_a_2839_ = lean_ctor_get(v_fst_2804_, 0);
lean_inc(v_a_2839_);
lean_dec_ref(v_fst_2804_);
v_packagesDir_x3f_2840_ = lean_ctor_get(v_a_2839_, 2);
v_packages_2841_ = lean_ctor_get(v_a_2839_, 3);
v___x_2842_ = lean_unsigned_to_nat(0u);
v___x_2843_ = lean_array_get_size(v_packages_2841_);
v___x_2844_ = lean_nat_dec_lt(v___x_2842_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_inc(v_packagesDir_x3f_2840_);
lean_dec(v_a_2839_);
v_packagesDir_x3f_2756_ = v_packagesDir_x3f_2840_;
v___y_2757_ = v_snd_2805_;
v___y_2758_ = v_a_2638_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = lean_box(0);
v___x_2846_ = lean_nat_dec_le(v___x_2843_, v___x_2843_);
if (v___x_2846_ == 0)
{
if (v___x_2844_ == 0)
{
lean_inc(v_packagesDir_x3f_2840_);
lean_dec(v_a_2839_);
v_packagesDir_x3f_2756_ = v_packagesDir_x3f_2840_;
v___y_2757_ = v_snd_2805_;
v___y_2758_ = v_a_2638_;
goto v___jp_2755_;
}
else
{
size_t v___x_2847_; size_t v___x_2848_; lean_object* v___x_2849_; 
v___x_2847_ = ((size_t)0ULL);
v___x_2848_ = lean_usize_of_nat(v___x_2843_);
v___x_2849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2640_, v_packages_2841_, v___x_2847_, v___x_2848_, v___x_2845_, v_snd_2805_);
v___y_2797_ = v_a_2839_;
v___y_2798_ = v___x_2849_;
goto v___jp_2796_;
}
}
else
{
size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = ((size_t)0ULL);
v___x_2851_ = lean_usize_of_nat(v___x_2843_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2640_, v_packages_2841_, v___x_2850_, v___x_2851_, v___x_2845_, v_snd_2805_);
v___y_2797_ = v_a_2839_;
v___y_2798_ = v___x_2852_;
goto v___jp_2796_;
}
}
}
else
{
lean_object* v_a_2853_; 
v_a_2853_ = lean_ctor_get(v_fst_2804_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v_fst_2804_);
v___y_2792_ = v_a_2853_;
v___y_2793_ = v_snd_2805_;
v___y_2794_ = v_a_2638_;
goto v___jp_2791_;
}
}
}
v___jp_2856_:
{
uint8_t v___x_2858_; 
v___x_2858_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2858_ == 0)
{
v_fst_2804_ = v_val_2857_;
v_snd_2805_ = v_a_2641_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = lean_box(0);
v___x_2860_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2860_ == 0)
{
if (v___x_2858_ == 0)
{
v_fst_2804_ = v_val_2857_;
v_snd_2805_ = v_a_2641_;
goto v___jp_2803_;
}
else
{
size_t v___x_2861_; size_t v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = ((size_t)0ULL);
v___x_2862_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2855_, v___x_2861_, v___x_2862_, v___x_2859_, v_a_2638_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_dec_ref(v___x_2863_);
v_fst_2804_ = v_val_2857_;
v_snd_2805_ = v_a_2641_;
goto v___jp_2803_;
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_val_2857_);
lean_dec_ref(v_rootName_2802_);
lean_dec_ref(v_config_2727_);
lean_dec_ref(v_dir_2726_);
lean_dec(v_a_2641_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
else
{
size_t v___x_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = ((size_t)0ULL);
v___x_2873_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2855_, v___x_2872_, v___x_2873_, v___x_2859_, v_a_2638_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_dec_ref(v___x_2874_);
v_fst_2804_ = v_val_2857_;
v_snd_2805_ = v_a_2641_;
goto v___jp_2803_;
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v_val_2857_);
lean_dec_ref(v_rootName_2802_);
lean_dec_ref(v_config_2727_);
lean_dec_ref(v_dir_2726_);
lean_dec(v_a_2641_);
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3___boxed(lean_object* v_a_2900_, lean_object* v_ws_2901_, lean_object* v_toUpdate_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_2900_, v_ws_2901_, v_toUpdate_2902_, v_a_2903_);
lean_dec(v_toUpdate_2902_);
lean_dec_ref(v_a_2900_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v_a_2906_, lean_object* v_ws_2907_, lean_object* v_rootDeps_2908_){
_start:
{
lean_object* v___y_2911_; lean_object* v_root_2916_; lean_object* v_lakeEnv_2917_; lean_object* v_lakeArgs_x3f_2918_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_3067_; lean_object* v___y_3068_; uint8_t v___y_3069_; lean_object* v_baseName_3072_; lean_object* v_dir_3073_; lean_object* v_config_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_root_2916_ = lean_ctor_get(v_ws_2907_, 0);
lean_inc_ref(v_root_2916_);
v_lakeEnv_2917_ = lean_ctor_get(v_ws_2907_, 1);
lean_inc_ref(v_lakeEnv_2917_);
v_lakeArgs_x3f_2918_ = lean_ctor_get(v_ws_2907_, 4);
lean_inc(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_ws_2907_);
v_baseName_3072_ = lean_ctor_get(v_root_2916_, 1);
lean_inc(v_baseName_3072_);
v_dir_3073_ = lean_ctor_get(v_root_2916_, 4);
lean_inc_ref_n(v_dir_3073_, 2);
v_config_3074_ = lean_ctor_get(v_root_2916_, 6);
lean_inc_ref(v_config_3074_);
lean_dec_ref(v_root_2916_);
v___x_3075_ = l_Lake_toolchainFileName;
v___x_3076_ = l_System_FilePath_join(v_dir_3073_, v___x_3075_);
v___x_3077_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_3076_);
lean_dec_ref(v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3172_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3172_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3172_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v_fixedToolchain_3082_; lean_object* v___x_3083_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; uint8_t v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; uint8_t v___y_3115_; lean_object* v___y_3116_; lean_object* v_src_3120_; lean_object* v_tc_x3f_3121_; lean_object* v_clashes_3122_; uint8_t v_fixed_3123_; lean_object* v___y_3147_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_fixedToolchain_3082_ = lean_ctor_get_uint8(v_config_3074_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_3074_);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3161_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_3162_ = lean_array_get_size(v_rootDeps_2908_);
v___x_3163_ = lean_nat_dec_lt(v___x_3083_, v___x_3162_);
if (v___x_3163_ == 0)
{
lean_inc(v_a_3078_);
v_src_3120_ = v_baseName_3072_;
v_tc_x3f_3121_ = v_a_3078_;
v_clashes_3122_ = v___x_3161_;
v_fixed_3123_ = v_fixedToolchain_3082_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
lean_inc(v_a_3078_);
lean_inc(v_baseName_3072_);
v___x_3164_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3164_, 0, v_baseName_3072_);
lean_ctor_set(v___x_3164_, 1, v_a_3078_);
lean_ctor_set(v___x_3164_, 2, v___x_3161_);
lean_ctor_set_uint8(v___x_3164_, sizeof(void*)*3, v_fixedToolchain_3082_);
v___x_3165_ = lean_nat_dec_le(v___x_3162_, v___x_3162_);
if (v___x_3165_ == 0)
{
if (v___x_3163_ == 0)
{
lean_dec_ref(v___x_3164_);
lean_inc(v_a_3078_);
v_src_3120_ = v_baseName_3072_;
v_tc_x3f_3121_ = v_a_3078_;
v_clashes_3122_ = v___x_3161_;
v_fixed_3123_ = v_fixedToolchain_3082_;
goto v___jp_3119_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
lean_dec(v_baseName_3072_);
v___x_3166_ = ((size_t)0ULL);
v___x_3167_ = lean_usize_of_nat(v___x_3162_);
lean_inc_ref(v_dir_3073_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3073_, v_rootDeps_2908_, v___x_3166_, v___x_3167_, v___x_3164_, v_a_2906_);
v___y_3147_ = v___x_3168_;
goto v___jp_3146_;
}
}
else
{
size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
lean_dec(v_baseName_3072_);
v___x_3169_ = ((size_t)0ULL);
v___x_3170_ = lean_usize_of_nat(v___x_3162_);
lean_inc_ref(v_dir_3073_);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_3073_, v_rootDeps_2908_, v___x_3169_, v___x_3170_, v___x_3164_, v_a_2906_);
v___y_3147_ = v___x_3171_;
goto v___jp_3146_;
}
}
v___jp_3084_:
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_nat_dec_lt(v___x_3083_, v___y_3086_);
if (v___x_3088_ == 0)
{
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
v___y_2911_ = v___y_3087_;
goto v___jp_2910_;
}
else
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_nat_dec_le(v___y_3086_, v___y_3086_);
if (v___x_3089_ == 0)
{
if (v___x_3088_ == 0)
{
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
v___y_2911_ = v___y_3087_;
goto v___jp_2910_;
}
else
{
size_t v___x_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = lean_usize_of_nat(v___y_3086_);
lean_dec(v___y_3086_);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3085_, v___x_3090_, v___x_3091_, v___y_3087_);
lean_dec_ref(v___y_3085_);
v___y_2911_ = v___x_3092_;
goto v___jp_2910_;
}
}
else
{
size_t v___x_3093_; size_t v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = lean_usize_of_nat(v___y_3086_);
lean_dec(v___y_3086_);
v___x_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_3085_, v___x_3093_, v___x_3094_, v___y_3087_);
lean_dec_ref(v___y_3085_);
v___y_2911_ = v___x_3095_;
goto v___jp_2910_;
}
}
}
v___jp_3096_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_inc_ref(v___y_3101_);
v___x_3104_ = lean_string_append(v___y_3101_, v___y_3103_);
lean_dec_ref(v___y_3103_);
v___x_3105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_3106_ = lean_string_append(v___x_3104_, v___x_3105_);
v___x_3107_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_3100_, v___y_3102_);
v___x_3108_ = lean_string_append(v___x_3106_, v___x_3107_);
lean_dec_ref(v___x_3107_);
v___x_3109_ = lean_string_append(v___x_3108_, v___y_3097_);
v___y_3085_ = v___y_3099_;
v___y_3086_ = v___y_3098_;
v___y_3087_ = v___x_3109_;
goto v___jp_3084_;
}
v___jp_3110_:
{
lean_object* v___x_3117_; lean_object* v_toString_3118_; 
v___x_3117_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_3118_ = lean_ctor_get(v___y_3114_, 0);
lean_inc_ref(v_toString_3118_);
lean_dec_ref(v___y_3114_);
v___y_3097_ = v___y_3116_;
v___y_3098_ = v___y_3112_;
v___y_3099_ = v___y_3111_;
v___y_3100_ = v___y_3113_;
v___y_3101_ = v___x_3117_;
v___y_3102_ = v___y_3115_;
v___y_3103_ = v_toString_3118_;
goto v___jp_3096_;
}
v___jp_3119_:
{
lean_object* v___x_3124_; uint8_t v___x_3125_; 
v___x_3124_ = lean_array_get_size(v_clashes_3122_);
v___x_3125_ = lean_nat_dec_lt(v___x_3083_, v___x_3124_);
if (v___x_3125_ == 0)
{
lean_dec_ref(v_clashes_3122_);
lean_dec(v_src_3120_);
if (lean_obj_tag(v_tc_x3f_3121_) == 1)
{
lean_object* v_val_3126_; lean_object* v_rootToolchainFile_3127_; 
v_val_3126_ = lean_ctor_get(v_tc_x3f_3121_, 0);
lean_inc(v_val_3126_);
lean_dec_ref(v_tc_x3f_3121_);
v_rootToolchainFile_3127_ = l_Lake_joinRelative(v_dir_3073_, v___x_3075_);
if (lean_obj_tag(v_a_3078_) == 0)
{
lean_del_object(v___x_3080_);
v___y_3067_ = v_rootToolchainFile_3127_;
v___y_3068_ = v_val_3126_;
v___y_3069_ = v___x_3125_;
goto v___jp_3066_;
}
else
{
lean_object* v_val_3128_; uint8_t v___x_3129_; 
v_val_3128_ = lean_ctor_get(v_a_3078_, 0);
lean_inc(v_val_3128_);
lean_dec_ref(v_a_3078_);
lean_inc(v_val_3126_);
v___x_3129_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_3128_, v_val_3126_);
if (v___x_3129_ == 0)
{
lean_del_object(v___x_3080_);
v___y_3067_ = v_rootToolchainFile_3127_;
v___y_3068_ = v_val_3126_;
v___y_3069_ = v___x_3129_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
lean_dec_ref(v_rootToolchainFile_3127_);
lean_dec(v_val_3126_);
lean_dec(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_lakeEnv_2917_);
v___x_3130_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2906_);
v___x_3131_ = lean_apply_2(v_a_2906_, v___x_3130_, lean_box(0));
v___x_3132_ = lean_box(0);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3132_);
v___x_3134_ = v___x_3080_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_dec(v_tc_x3f_3121_);
lean_dec(v_a_3078_);
lean_dec_ref(v_dir_3073_);
lean_dec(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_lakeEnv_2917_);
v___x_3136_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2906_);
v___x_3137_ = lean_apply_2(v_a_2906_, v___x_3136_, lean_box(0));
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3137_);
v___x_3139_ = v___x_3080_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
lean_del_object(v___x_3080_);
lean_dec(v_a_3078_);
lean_dec_ref(v_dir_3073_);
lean_dec(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_lakeEnv_2917_);
if (lean_obj_tag(v_tc_x3f_3121_) == 1)
{
if (v_fixed_3123_ == 0)
{
lean_object* v_val_3141_; lean_object* v___x_3142_; 
v_val_3141_ = lean_ctor_get(v_tc_x3f_3121_, 0);
lean_inc(v_val_3141_);
lean_dec_ref(v_tc_x3f_3121_);
v___x_3142_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_3111_ = v_clashes_3122_;
v___y_3112_ = v___x_3124_;
v___y_3113_ = v_src_3120_;
v___y_3114_ = v_val_3141_;
v___y_3115_ = v___x_3125_;
v___y_3116_ = v___x_3142_;
goto v___jp_3110_;
}
else
{
lean_object* v_val_3143_; lean_object* v___x_3144_; 
v_val_3143_ = lean_ctor_get(v_tc_x3f_3121_, 0);
lean_inc(v_val_3143_);
lean_dec_ref(v_tc_x3f_3121_);
v___x_3144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_3111_ = v_clashes_3122_;
v___y_3112_ = v___x_3124_;
v___y_3113_ = v_src_3120_;
v___y_3114_ = v_val_3143_;
v___y_3115_ = v___x_3125_;
v___y_3116_ = v___x_3144_;
goto v___jp_3110_;
}
}
else
{
lean_object* v___x_3145_; 
lean_dec(v_tc_x3f_3121_);
lean_dec(v_src_3120_);
v___x_3145_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_3085_ = v_clashes_3122_;
v___y_3086_ = v___x_3124_;
v___y_3087_ = v___x_3145_;
goto v___jp_3084_;
}
}
}
v___jp_3146_:
{
if (lean_obj_tag(v___y_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v_src_3149_; lean_object* v_tc_x3f_3150_; lean_object* v_clashes_3151_; uint8_t v_fixed_3152_; 
v_a_3148_ = lean_ctor_get(v___y_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___y_3147_);
v_src_3149_ = lean_ctor_get(v_a_3148_, 0);
lean_inc(v_src_3149_);
v_tc_x3f_3150_ = lean_ctor_get(v_a_3148_, 1);
lean_inc(v_tc_x3f_3150_);
v_clashes_3151_ = lean_ctor_get(v_a_3148_, 2);
lean_inc_ref(v_clashes_3151_);
v_fixed_3152_ = lean_ctor_get_uint8(v_a_3148_, sizeof(void*)*3);
lean_dec(v_a_3148_);
v_src_3120_ = v_src_3149_;
v_tc_x3f_3121_ = v_tc_x3f_3150_;
v_clashes_3122_ = v_clashes_3151_;
v_fixed_3123_ = v_fixed_3152_;
goto v___jp_3119_;
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_del_object(v___x_3080_);
lean_dec(v_a_3078_);
lean_dec_ref(v_dir_3073_);
lean_dec(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_lakeEnv_2917_);
v_a_3153_ = lean_ctor_get(v___y_3147_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___y_3147_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___y_3147_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___y_3147_);
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
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref(v_config_3074_);
lean_dec_ref(v_dir_3073_);
lean_dec(v_baseName_3072_);
lean_dec(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_lakeEnv_2917_);
v_a_3173_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3175_ = v___x_3077_;
v_isShared_3176_ = v_isSharedCheck_3185_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3077_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3185_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3177_ = lean_io_error_to_string(v_a_3173_);
v___x_3178_ = 3;
v___x_3179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set_uint8(v___x_3179_, sizeof(void*)*1, v___x_3178_);
lean_inc_ref(v_a_2906_);
v___x_3180_ = lean_apply_2(v_a_2906_, v___x_3179_, lean_box(0));
v___x_3181_ = lean_box(0);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3181_);
v___x_3183_ = v___x_3175_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
v___jp_2910_:
{
uint8_t v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2912_ = 2;
v___x_2913_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2913_, 0, v___y_2911_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*1, v___x_2912_);
lean_inc_ref(v_a_2906_);
v___x_2914_ = lean_apply_2(v_a_2906_, v___x_2913_, lean_box(0));
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
v___jp_2919_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_inc_ref(v___y_2920_);
v___x_2924_ = lean_string_append(v___y_2920_, v___y_2923_);
v___x_2925_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2926_ = lean_string_append(v___x_2924_, v___x_2925_);
v___x_2927_ = 1;
v___x_2928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set_uint8(v___x_2928_, sizeof(void*)*1, v___x_2927_);
lean_inc_ref(v_a_2906_);
v___x_2929_ = lean_apply_2(v_a_2906_, v___x_2928_, lean_box(0));
v___x_2930_ = l_IO_FS_writeFile(v___y_2922_, v___y_2923_);
lean_dec_ref(v___y_2922_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_dec_ref(v___x_2930_);
if (lean_obj_tag(v_lakeArgs_x3f_2918_) == 1)
{
lean_object* v_elan_x3f_2931_; 
v_elan_x3f_2931_ = lean_ctor_get(v_lakeEnv_2917_, 2);
if (lean_obj_tag(v_elan_x3f_2931_) == 1)
{
lean_object* v_val_2932_; lean_object* v_val_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v_elan_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_val_2932_ = lean_ctor_get(v_lakeArgs_x3f_2918_, 0);
lean_inc(v_val_2932_);
lean_dec_ref(v_lakeArgs_x3f_2918_);
v_val_2933_ = lean_ctor_get(v_elan_x3f_2931_, 0);
v___x_2934_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2906_);
v___x_2935_ = lean_apply_2(v_a_2906_, v___x_2934_, lean_box(0));
v___x_2936_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2937_ = lean_ctor_get(v_val_2933_, 1);
lean_inc_ref(v_elan_2937_);
v___x_2938_ = 1;
v___x_2939_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2940_ = lean_unsigned_to_nat(4u);
v___x_2941_ = lean_mk_empty_array_with_capacity(v___x_2940_);
lean_dec_ref(v___x_2941_);
v___x_2942_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2943_ = lean_array_push(v___x_2942_, v___y_2923_);
v___x_2944_ = lean_array_push(v___x_2943_, v___x_2939_);
v___x_2945_ = l_Array_append___redArg(v___x_2944_, v_val_2932_);
lean_dec(v_val_2932_);
v___x_2946_ = lean_box(0);
v___x_2947_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2917_);
v___x_2948_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2948_, 0, v___x_2936_);
lean_ctor_set(v___x_2948_, 1, v_elan_2937_);
lean_ctor_set(v___x_2948_, 2, v___x_2945_);
lean_ctor_set(v___x_2948_, 3, v___x_2946_);
lean_ctor_set(v___x_2948_, 4, v___x_2947_);
lean_ctor_set_uint8(v___x_2948_, sizeof(void*)*5, v___x_2938_);
lean_ctor_set_uint8(v___x_2948_, sizeof(void*)*5 + 1, v___y_2921_);
v___x_2949_ = lean_io_process_spawn(v___x_2948_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
v___x_2951_ = lean_io_process_child_wait(v___x_2936_, v_a_2950_);
lean_dec(v_a_2950_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; uint32_t v___x_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = lean_unbox_uint32(v_a_2952_);
lean_dec(v_a_2952_);
v___x_2954_ = lean_uint32_to_uint8(v___x_2953_);
v___x_2955_ = lean_io_exit(v___x_2954_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2976_; 
v_a_2964_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2966_ = v___x_2955_;
v_isShared_2967_ = v_isSharedCheck_2976_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2955_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2976_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2968_ = lean_io_error_to_string(v_a_2964_);
v___x_2969_ = 3;
v___x_2970_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*1, v___x_2969_);
lean_inc_ref(v_a_2906_);
v___x_2971_ = lean_apply_2(v_a_2906_, v___x_2970_, lean_box(0));
v___x_2972_ = lean_box(0);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2972_);
v___x_2974_ = v___x_2966_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2989_; 
v_a_2977_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2979_ = v___x_2951_;
v_isShared_2980_ = v_isSharedCheck_2989_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2951_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2989_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2981_ = lean_io_error_to_string(v_a_2977_);
v___x_2982_ = 3;
v___x_2983_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set_uint8(v___x_2983_, sizeof(void*)*1, v___x_2982_);
lean_inc_ref(v_a_2906_);
v___x_2984_ = lean_apply_2(v_a_2906_, v___x_2983_, lean_box(0));
v___x_2985_ = lean_box(0);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2985_);
v___x_2987_ = v___x_2979_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3002_; 
v_a_2990_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2992_ = v___x_2949_;
v_isShared_2993_ = v_isSharedCheck_3002_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2949_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3002_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2994_ = lean_io_error_to_string(v_a_2990_);
v___x_2995_ = 3;
v___x_2996_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*1, v___x_2995_);
lean_inc_ref(v_a_2906_);
v___x_2997_ = lean_apply_2(v_a_2906_, v___x_2996_, lean_box(0));
v___x_2998_ = lean_box(0);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2998_);
v___x_3000_ = v___x_2992_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; lean_object* v___x_3006_; 
lean_dec_ref(v_lakeArgs_x3f_2918_);
lean_dec_ref(v___y_2923_);
lean_dec_ref(v_lakeEnv_2917_);
v___x_3003_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2906_);
v___x_3004_ = lean_apply_2(v_a_2906_, v___x_3003_, lean_box(0));
v___x_3005_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3006_ = lean_io_exit(v___x_3005_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3027_; 
v_a_3015_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3017_ = v___x_3006_;
v_isShared_3018_ = v_isSharedCheck_3027_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3006_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3027_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3019_ = lean_io_error_to_string(v_a_3015_);
v___x_3020_ = 3;
v___x_3021_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*1, v___x_3020_);
lean_inc_ref(v_a_2906_);
v___x_3022_ = lean_apply_2(v_a_2906_, v___x_3021_, lean_box(0));
v___x_3023_ = lean_box(0);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3023_);
v___x_3025_ = v___x_3017_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; 
lean_dec_ref(v___y_2923_);
lean_dec(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_lakeEnv_2917_);
v___x_3028_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2906_);
v___x_3029_ = lean_apply_2(v_a_2906_, v___x_3028_, lean_box(0));
v___x_3030_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_3031_ = lean_io_exit(v___x_3030_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3052_; 
v_a_3040_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3042_ = v___x_3031_;
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3031_);
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
lean_inc_ref(v_a_2906_);
v___x_3047_ = lean_apply_2(v_a_2906_, v___x_3046_, lean_box(0));
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
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v___y_2923_);
lean_dec(v_lakeArgs_x3f_2918_);
lean_dec_ref(v_lakeEnv_2917_);
v_a_3053_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3055_ = v___x_2930_;
v_isShared_3056_ = v_isSharedCheck_3065_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2930_);
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
lean_inc_ref(v_a_2906_);
v___x_3060_ = lean_apply_2(v_a_2906_, v___x_3059_, lean_box(0));
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
v___jp_3066_:
{
lean_object* v___x_3070_; lean_object* v_toString_3071_; 
v___x_3070_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_3071_ = lean_ctor_get(v___y_3068_, 0);
lean_inc_ref(v_toString_3071_);
lean_dec_ref(v___y_3068_);
v___y_2920_ = v___x_3070_;
v___y_2921_ = v___y_3069_;
v___y_2922_ = v___y_3067_;
v___y_2923_ = v_toString_3071_;
goto v___jp_2919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object* v_a_3186_, lean_object* v_ws_3187_, lean_object* v_rootDeps_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_a_3186_, v_ws_3187_, v_rootDeps_3188_);
lean_dec_ref(v_rootDeps_3188_);
lean_dec_ref(v_a_3186_);
return v_res_3190_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(lean_object* v_a_3191_, lean_object* v_as_3192_, size_t v_i_3193_, size_t v_stop_3194_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = lean_usize_dec_eq(v_i_3193_, v_stop_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v_baseName_3197_; lean_object* v_name_3198_; uint8_t v___x_3199_; 
v___x_3196_ = lean_array_uget_borrowed(v_as_3192_, v_i_3193_);
v_baseName_3197_ = lean_ctor_get(v___x_3196_, 1);
v_name_3198_ = lean_ctor_get(v_a_3191_, 0);
v___x_3199_ = lean_name_eq(v_baseName_3197_, v_name_3198_);
if (v___x_3199_ == 0)
{
size_t v___x_3200_; size_t v___x_3201_; 
v___x_3200_ = ((size_t)1ULL);
v___x_3201_ = lean_usize_add(v_i_3193_, v___x_3200_);
v_i_3193_ = v___x_3201_;
goto _start;
}
else
{
return v___x_3199_;
}
}
else
{
uint8_t v___x_3203_; 
v___x_3203_ = 0;
return v___x_3203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4___boxed(lean_object* v_a_3204_, lean_object* v_as_3205_, lean_object* v_i_3206_, lean_object* v_stop_3207_){
_start:
{
size_t v_i_boxed_3208_; size_t v_stop_boxed_3209_; uint8_t v_res_3210_; lean_object* v_r_3211_; 
v_i_boxed_3208_ = lean_unbox_usize(v_i_3206_);
lean_dec(v_i_3206_);
v_stop_boxed_3209_ = lean_unbox_usize(v_stop_3207_);
lean_dec(v_stop_3207_);
v_res_3210_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v_a_3204_, v_as_3205_, v_i_boxed_3208_, v_stop_boxed_3209_);
lean_dec_ref(v_as_3205_);
lean_dec_ref(v_a_3204_);
v_r_3211_ = lean_box(v_res_3210_);
return v_r_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(lean_object* v_pkg_3212_, lean_object* v_leanOpts_3213_, uint8_t v_reconfigure_3214_, lean_object* v_as_3215_, size_t v_i_3216_, size_t v_stop_3217_, lean_object* v_b_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_usize_dec_eq(v_i_3216_, v_stop_3217_);
if (v___x_3223_ == 0)
{
lean_object* v_packages_3224_; size_t v___x_3225_; size_t v___x_3226_; lean_object* v___y_3228_; lean_object* v_fst_3229_; lean_object* v_snd_3230_; lean_object* v___x_3233_; uint8_t v___y_3235_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_packages_3224_ = lean_ctor_get(v___y_3219_, 5);
v___x_3225_ = ((size_t)1ULL);
v___x_3226_ = lean_usize_sub(v_i_3216_, v___x_3225_);
v___x_3233_ = lean_array_uget_borrowed(v_as_3215_, v___x_3226_);
v___x_3343_ = lean_unsigned_to_nat(0u);
v___x_3344_ = lean_array_get_size(v_packages_3224_);
v___x_3345_ = lean_nat_dec_lt(v___x_3343_, v___x_3344_);
if (v___x_3345_ == 0)
{
v___y_3235_ = v___x_3223_;
goto v___jp_3234_;
}
else
{
if (v___x_3345_ == 0)
{
v___y_3235_ = v___x_3223_;
goto v___jp_3234_;
}
else
{
size_t v___x_3346_; size_t v___x_3347_; uint8_t v___x_3348_; 
v___x_3346_ = ((size_t)0ULL);
v___x_3347_ = lean_usize_of_nat(v___x_3344_);
v___x_3348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v___x_3233_, v_packages_3224_, v___x_3346_, v___x_3347_);
if (v___x_3348_ == 0)
{
v___y_3235_ = v___x_3348_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_box(0);
v_i_3216_ = v___x_3226_;
v_b_3218_ = v___x_3349_;
goto _start;
}
}
}
v___jp_3227_:
{
lean_object* v_snd_3231_; 
v_snd_3231_ = lean_ctor_get(v_fst_3229_, 1);
lean_inc(v_snd_3231_);
lean_dec_ref(v_fst_3229_);
v_i_3216_ = v___x_3226_;
v_b_3218_ = v___y_3228_;
v___y_3219_ = v_snd_3231_;
v___y_3220_ = v_snd_3230_;
goto _start;
}
v___jp_3234_:
{
lean_object* v_baseName_3236_; lean_object* v_name_3237_; lean_object* v_opts_3238_; uint8_t v___x_3239_; 
v_baseName_3236_ = lean_ctor_get(v_pkg_3212_, 1);
v_name_3237_ = lean_ctor_get(v___x_3233_, 0);
v_opts_3238_ = lean_ctor_get(v___x_3233_, 4);
v___x_3239_ = lean_name_eq(v_baseName_3236_, v_name_3237_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; 
lean_inc_ref(v___y_3221_);
lean_inc_ref(v___y_3219_);
lean_inc(v___x_3233_);
lean_inc_ref(v_pkg_3212_);
v___x_3240_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_pkg_3212_, v___x_3233_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3326_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3326_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3326_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v_fst_3245_; lean_object* v_snd_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_fst_3245_ = lean_ctor_get(v_a_3241_, 0);
lean_inc(v_fst_3245_);
v_snd_3246_ = lean_ctor_get(v_a_3241_, 1);
lean_inc(v_snd_3246_);
lean_dec(v_a_3241_);
v___x_3247_ = lean_unsigned_to_nat(0u);
v___x_3248_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3213_);
lean_inc(v_opts_3238_);
v___x_3249_ = l___private_Lake_Load_Resolve_0__Lake_addDepPackage(v_fst_3245_, v_opts_3238_, v_leanOpts_3213_, v_reconfigure_3214_, v___y_3219_, v___x_3248_);
v___x_3250_ = lean_box(0);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3251_; lean_object* v_a_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
lean_del_object(v___x_3243_);
v_a_3251_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3251_);
v_a_3252_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3249_);
v___x_3253_ = lean_array_get_size(v_a_3252_);
v___x_3254_ = lean_nat_dec_lt(v___x_3247_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_dec(v_a_3252_);
v___y_3228_ = v___x_3250_;
v_fst_3229_ = v_a_3251_;
v_snd_3230_ = v_snd_3246_;
goto v___jp_3227_;
}
else
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_nat_dec_le(v___x_3253_, v___x_3253_);
if (v___x_3255_ == 0)
{
if (v___x_3254_ == 0)
{
lean_dec(v_a_3252_);
v___y_3228_ = v___x_3250_;
v_fst_3229_ = v_a_3251_;
v_snd_3230_ = v_snd_3246_;
goto v___jp_3227_;
}
else
{
size_t v___x_3256_; size_t v___x_3257_; lean_object* v___x_3258_; 
v___x_3256_ = ((size_t)0ULL);
v___x_3257_ = lean_usize_of_nat(v___x_3253_);
v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3252_, v___x_3256_, v___x_3257_, v___x_3250_, v___y_3221_);
lean_dec(v_a_3252_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec_ref(v___x_3258_);
v___y_3228_ = v___x_3250_;
v_fst_3229_ = v_a_3251_;
v_snd_3230_ = v_snd_3246_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_a_3251_);
lean_dec(v_snd_3246_);
lean_dec_ref(v_leanOpts_3213_);
lean_dec_ref(v_pkg_3212_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
else
{
size_t v___x_3267_; size_t v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = ((size_t)0ULL);
v___x_3268_ = lean_usize_of_nat(v___x_3253_);
v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3252_, v___x_3267_, v___x_3268_, v___x_3250_, v___y_3221_);
lean_dec(v_a_3252_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_dec_ref(v___x_3269_);
v___y_3228_ = v___x_3250_;
v_fst_3229_ = v_a_3251_;
v_snd_3230_ = v_snd_3246_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v_a_3251_);
lean_dec(v_snd_3246_);
lean_dec_ref(v_leanOpts_3213_);
lean_dec_ref(v_pkg_3212_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
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
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; 
lean_dec(v_snd_3246_);
lean_dec_ref(v_leanOpts_3213_);
lean_dec_ref(v_pkg_3212_);
v_a_3278_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3249_);
v___x_3279_ = lean_array_get_size(v_a_3278_);
v___x_3280_ = lean_nat_dec_lt(v___x_3247_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3282_; 
lean_dec(v_a_3278_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set_tag(v___x_3243_, 1);
lean_ctor_set(v___x_3243_, 0, v___x_3250_);
v___x_3282_ = v___x_3243_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3250_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
else
{
uint8_t v___x_3284_; 
v___x_3284_ = lean_nat_dec_le(v___x_3279_, v___x_3279_);
if (v___x_3284_ == 0)
{
if (v___x_3280_ == 0)
{
lean_object* v___x_3286_; 
lean_dec(v_a_3278_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set_tag(v___x_3243_, 1);
lean_ctor_set(v___x_3243_, 0, v___x_3250_);
v___x_3286_ = v___x_3243_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3250_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
else
{
size_t v___x_3288_; size_t v___x_3289_; lean_object* v___x_3290_; 
lean_del_object(v___x_3243_);
v___x_3288_ = ((size_t)0ULL);
v___x_3289_ = lean_usize_of_nat(v___x_3279_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3278_, v___x_3288_, v___x_3289_, v___x_3250_, v___y_3221_);
lean_dec(v_a_3278_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3290_, 0);
lean_dec(v_unused_3298_);
v___x_3292_ = v___x_3290_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v___x_3290_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 1);
lean_ctor_set(v___x_3292_, 0, v___x_3250_);
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3250_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3299_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3290_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3290_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
else
{
size_t v___x_3307_; size_t v___x_3308_; lean_object* v___x_3309_; 
lean_del_object(v___x_3243_);
v___x_3307_ = ((size_t)0ULL);
v___x_3308_ = lean_usize_of_nat(v___x_3279_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3278_, v___x_3307_, v___x_3308_, v___x_3250_, v___y_3221_);
lean_dec(v_a_3278_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; 
v_unused_3317_ = lean_ctor_get(v___x_3309_, 0);
lean_dec(v_unused_3317_);
v___x_3311_ = v___x_3309_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_dec(v___x_3309_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set_tag(v___x_3311_, 1);
lean_ctor_set(v___x_3311_, 0, v___x_3250_);
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3250_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
v_a_3318_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3309_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3309_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
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
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec_ref(v___y_3219_);
lean_dec_ref(v_leanOpts_3213_);
lean_dec_ref(v_pkg_3212_);
v_a_3327_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3240_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3240_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_inc(v_baseName_3236_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec_ref(v_leanOpts_3213_);
lean_dec_ref(v_pkg_3212_);
v___x_3335_ = l_Lean_Name_toString(v_baseName_3236_, v___y_3235_);
v___x_3336_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__0));
v___x_3337_ = lean_string_append(v___x_3335_, v___x_3336_);
v___x_3338_ = 3;
v___x_3339_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set_uint8(v___x_3339_, sizeof(void*)*1, v___x_3338_);
lean_inc_ref(v___y_3221_);
v___x_3340_ = lean_apply_2(v___y_3221_, v___x_3339_, lean_box(0));
v___x_3341_ = lean_box(0);
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
return v___x_3342_;
}
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v_leanOpts_3213_);
lean_dec_ref(v_pkg_3212_);
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v_b_3218_);
lean_ctor_set(v___x_3351_, 1, v___y_3219_);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v___y_3220_);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg___boxed(lean_object* v_pkg_3354_, lean_object* v_leanOpts_3355_, lean_object* v_reconfigure_3356_, lean_object* v_as_3357_, lean_object* v_i_3358_, lean_object* v_stop_3359_, lean_object* v_b_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
uint8_t v_reconfigure_boxed_3365_; size_t v_i_boxed_3366_; size_t v_stop_boxed_3367_; lean_object* v_res_3368_; 
v_reconfigure_boxed_3365_ = lean_unbox(v_reconfigure_3356_);
v_i_boxed_3366_ = lean_unbox_usize(v_i_3358_);
lean_dec(v_i_3358_);
v_stop_boxed_3367_ = lean_unbox_usize(v_stop_3359_);
lean_dec(v_stop_3359_);
v_res_3368_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3354_, v_leanOpts_3355_, v_reconfigure_boxed_3365_, v_as_3357_, v_i_boxed_3366_, v_stop_boxed_3367_, v_b_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec_ref(v___y_3363_);
lean_dec_ref(v_as_3357_);
return v_res_3368_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(lean_object* v_a_3369_, lean_object* v_x_3370_){
_start:
{
if (lean_obj_tag(v_x_3370_) == 0)
{
uint8_t v___x_3371_; 
v___x_3371_ = 0;
return v___x_3371_;
}
else
{
lean_object* v_head_3372_; lean_object* v_tail_3373_; uint8_t v___x_3374_; 
v_head_3372_ = lean_ctor_get(v_x_3370_, 0);
v_tail_3373_ = lean_ctor_get(v_x_3370_, 1);
v___x_3374_ = lean_name_eq(v_a_3369_, v_head_3372_);
if (v___x_3374_ == 0)
{
v_x_3370_ = v_tail_3373_;
goto _start;
}
else
{
return v___x_3374_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10___boxed(lean_object* v_a_3376_, lean_object* v_x_3377_){
_start:
{
uint8_t v_res_3378_; lean_object* v_r_3379_; 
v_res_3378_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(v_a_3376_, v_x_3377_);
lean_dec(v_x_3377_);
lean_dec(v_a_3376_);
v_r_3379_ = lean_box(v_res_3378_);
return v_r_3379_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__12(lean_object* v___x_3380_, uint8_t v___x_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
if (lean_obj_tag(v_a_3382_) == 0)
{
lean_object* v_fst_3384_; lean_object* v_snd_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3394_; 
v_fst_3384_ = lean_ctor_get(v_a_3383_, 0);
v_snd_3385_ = lean_ctor_get(v_a_3383_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3387_ = v_a_3383_;
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_snd_3385_);
lean_inc(v_fst_3384_);
lean_dec(v_a_3383_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3389_ = l_List_reverse___redArg(v_fst_3384_);
v___x_3390_ = l_List_reverse___redArg(v_snd_3385_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 1, v___x_3390_);
lean_ctor_set(v___x_3387_, 0, v___x_3389_);
v___x_3392_ = v___x_3387_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
lean_object* v_head_3395_; lean_object* v_tail_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3418_; 
v_head_3395_ = lean_ctor_get(v_a_3382_, 0);
v_tail_3396_ = lean_ctor_get(v_a_3382_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3382_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3398_ = v_a_3382_;
v_isShared_3399_ = v_isSharedCheck_3418_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_tail_3396_);
lean_inc(v_head_3395_);
lean_dec(v_a_3382_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3418_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v_fst_3400_; lean_object* v_snd_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3417_; 
v_fst_3400_ = lean_ctor_get(v_a_3383_, 0);
v_snd_3401_ = lean_ctor_get(v_a_3383_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_a_3383_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3403_ = v_a_3383_;
v_isShared_3404_ = v_isSharedCheck_3417_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_snd_3401_);
lean_inc(v_fst_3400_);
lean_dec(v_a_3383_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3417_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_name_eq(v_head_3395_, v___x_3380_);
if (v___x_3413_ == 0)
{
if (v___x_3381_ == 0)
{
goto v___jp_3405_;
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_del_object(v___x_3403_);
lean_del_object(v___x_3398_);
v___x_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_head_3395_);
lean_ctor_set(v___x_3414_, 1, v_fst_3400_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v_snd_3401_);
v_a_3382_ = v_tail_3396_;
v_a_3383_ = v___x_3415_;
goto _start;
}
}
else
{
goto v___jp_3405_;
}
v___jp_3405_:
{
lean_object* v___x_3407_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 1, v_snd_3401_);
v___x_3407_ = v___x_3398_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_head_3395_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_snd_3401_);
v___x_3407_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3409_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 1, v___x_3407_);
v___x_3409_ = v___x_3403_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_fst_3400_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
v_a_3382_ = v_tail_3396_;
v_a_3383_ = v___x_3409_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__12___boxed(lean_object* v___x_3419_, lean_object* v___x_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
uint8_t v___x_73041__boxed_3423_; lean_object* v_res_3424_; 
v___x_73041__boxed_3423_ = lean_unbox(v___x_3420_);
v_res_3424_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__12(v___x_3419_, v___x_73041__boxed_3423_, v_a_3421_, v_a_3422_);
lean_dec(v___x_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19_spec__23(lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
if (lean_obj_tag(v_a_3426_) == 0)
{
lean_object* v___x_3428_; 
v___x_3428_ = l_List_reverse___redArg(v_a_3427_);
return v___x_3428_;
}
else
{
lean_object* v_head_3429_; lean_object* v_tail_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3442_; 
v_head_3429_ = lean_ctor_get(v_a_3426_, 0);
v_tail_3430_ = lean_ctor_get(v_a_3426_, 1);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_a_3426_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3432_ = v_a_3426_;
v_isShared_3433_ = v_isSharedCheck_3442_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_tail_3430_);
lean_inc(v_head_3429_);
lean_dec(v_a_3426_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3442_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; uint8_t v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3434_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19_spec__23___closed__0));
v___x_3435_ = 1;
v___x_3436_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_3429_, v___x_3435_);
v___x_3437_ = lean_string_append(v___x_3434_, v___x_3436_);
lean_dec_ref(v___x_3436_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_a_3427_);
lean_ctor_set(v___x_3432_, 0, v___x_3437_);
v___x_3439_ = v___x_3432_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3427_);
v___x_3439_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
v_a_3426_ = v_tail_3430_;
v_a_3427_ = v___x_3439_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19(lean_object* v_cycle_3444_){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3445_ = ((lean_object*)(l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19___closed__0));
v___x_3446_ = lean_box(0);
v___x_3447_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19_spec__23(v_cycle_3444_, v___x_3446_);
v___x_3448_ = l_String_intercalate(v___x_3445_, v___x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___redArg(lean_object* v_cycle_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3452_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1));
v___x_3453_ = l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19(v_cycle_3449_);
v___x_3454_ = lean_string_append(v___x_3452_, v___x_3453_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = 3;
v___x_3456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set_uint8(v___x_3456_, sizeof(void*)*1, v___x_3455_);
lean_inc_ref(v___y_3450_);
v___x_3457_ = lean_apply_2(v___y_3450_, v___x_3456_, lean_box(0));
v___x_3458_ = lean_box(0);
v___x_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_cycle_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___redArg(v_cycle_3460_, v___y_3461_);
lean_dec_ref(v___y_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(lean_object* v_leanOpts_3466_, lean_object* v___x_3467_, lean_object* v_as_3468_, size_t v_i_3469_, size_t v_stop_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_usize_dec_eq(v_i_3469_, v_stop_3470_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_array_uget_borrowed(v_as_3468_, v_i_3469_);
lean_inc(v___x_3477_);
lean_inc_ref(v_leanOpts_3466_);
v___x_3478_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg(v_leanOpts_3466_, v___x_3477_, v___x_3467_, v___y_3472_, v___y_3473_, v___y_3474_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v_fst_3480_; lean_object* v_snd_3481_; lean_object* v_fst_3482_; lean_object* v_snd_3483_; size_t v___x_3484_; size_t v___x_3485_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref(v___x_3478_);
v_fst_3480_ = lean_ctor_get(v_a_3479_, 0);
lean_inc(v_fst_3480_);
v_snd_3481_ = lean_ctor_get(v_a_3479_, 1);
lean_inc(v_snd_3481_);
lean_dec(v_a_3479_);
v_fst_3482_ = lean_ctor_get(v_fst_3480_, 0);
lean_inc(v_fst_3482_);
v_snd_3483_ = lean_ctor_get(v_fst_3480_, 1);
lean_inc(v_snd_3483_);
lean_dec(v_fst_3480_);
v___x_3484_ = ((size_t)1ULL);
v___x_3485_ = lean_usize_add(v_i_3469_, v___x_3484_);
v_i_3469_ = v___x_3485_;
v_b_3471_ = v_fst_3482_;
v___y_3472_ = v_snd_3483_;
v___y_3473_ = v_snd_3481_;
goto _start;
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v_leanOpts_3466_);
v_a_3487_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3478_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3478_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec_ref(v_leanOpts_3466_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v_b_3471_);
lean_ctor_set(v___x_3495_, 1, v___y_3472_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v___y_3473_);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26(lean_object* v_leanOpts_3498_, lean_object* v___x_3499_, lean_object* v_leanOpts_3500_, uint8_t v_reconfigure_3501_, lean_object* v_pkg_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_packages_3508_; lean_object* v_depConfigs_3509_; lean_object* v___x_3510_; lean_object* v_snd_3512_; lean_object* v_packages_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v_____x_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v_packages_3508_ = lean_ctor_get(v_a_3504_, 5);
v_depConfigs_3509_ = lean_ctor_get(v_pkg_3502_, 12);
lean_inc_ref(v_depConfigs_3509_);
v___x_3510_ = lean_array_get_size(v_packages_3508_);
v___x_3538_ = lean_array_get_size(v_depConfigs_3509_);
v___x_3539_ = lean_unsigned_to_nat(0u);
v___x_3540_ = lean_box(0);
v___x_3541_ = lean_nat_dec_le(v___x_3538_, v___x_3538_);
if (v___x_3541_ == 0)
{
uint8_t v___x_3542_; 
v___x_3542_ = lean_nat_dec_lt(v___x_3539_, v___x_3538_);
if (v___x_3542_ == 0)
{
uint8_t v___x_3543_; 
lean_dec_ref(v_depConfigs_3509_);
lean_dec_ref(v_pkg_3502_);
lean_dec_ref(v_leanOpts_3500_);
v___x_3543_ = lean_nat_dec_lt(v___x_3510_, v___x_3510_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec_ref(v_leanOpts_3498_);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3540_);
lean_ctor_set(v___x_3544_, 1, v_a_3504_);
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v___y_3505_);
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
return v___x_3546_;
}
else
{
uint8_t v___x_3547_; 
v___x_3547_ = lean_nat_dec_le(v___x_3510_, v___x_3510_);
if (v___x_3547_ == 0)
{
if (v___x_3543_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref(v_leanOpts_3498_);
v___x_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3540_);
lean_ctor_set(v___x_3548_, 1, v_a_3504_);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___y_3505_);
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
else
{
size_t v___x_3551_; lean_object* v___x_3552_; 
lean_inc_ref(v_packages_3508_);
v___x_3551_ = lean_usize_of_nat(v___x_3510_);
v___x_3552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(v_leanOpts_3498_, v___x_3499_, v_packages_3508_, v___x_3551_, v___x_3551_, v___x_3540_, v_a_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v_packages_3508_);
return v___x_3552_;
}
}
else
{
size_t v___x_3553_; lean_object* v___x_3554_; 
lean_inc_ref(v_packages_3508_);
v___x_3553_ = lean_usize_of_nat(v___x_3510_);
v___x_3554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(v_leanOpts_3498_, v___x_3499_, v_packages_3508_, v___x_3553_, v___x_3553_, v___x_3540_, v_a_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v_packages_3508_);
return v___x_3554_;
}
}
}
else
{
size_t v___x_3555_; size_t v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = lean_usize_of_nat(v___x_3538_);
v___x_3556_ = ((size_t)0ULL);
v___x_3557_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3502_, v_leanOpts_3500_, v_reconfigure_3501_, v_depConfigs_3509_, v___x_3555_, v___x_3556_, v___x_3540_, v_a_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v_depConfigs_3509_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v_fst_3559_; lean_object* v_snd_3560_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v___x_3557_);
v_fst_3559_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_fst_3559_);
v_snd_3560_ = lean_ctor_get(v_a_3558_, 1);
lean_inc(v_snd_3560_);
lean_dec(v_a_3558_);
v_____x_3533_ = v_fst_3559_;
v___y_3534_ = v_snd_3560_;
v___y_3535_ = v___y_3506_;
goto v___jp_3532_;
}
else
{
lean_dec_ref(v_leanOpts_3498_);
return v___x_3557_;
}
}
}
else
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_nat_dec_lt(v___x_3539_, v___x_3538_);
if (v___x_3561_ == 0)
{
lean_inc_ref(v_packages_3508_);
lean_dec_ref(v_depConfigs_3509_);
lean_dec_ref(v_pkg_3502_);
lean_dec_ref(v_leanOpts_3500_);
v_snd_3512_ = v_a_3504_;
v_packages_3513_ = v_packages_3508_;
v___y_3514_ = v___y_3505_;
v___y_3515_ = v___y_3506_;
goto v___jp_3511_;
}
else
{
size_t v___x_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_usize_of_nat(v___x_3538_);
v___x_3563_ = ((size_t)0ULL);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_3502_, v_leanOpts_3500_, v_reconfigure_3501_, v_depConfigs_3509_, v___x_3562_, v___x_3563_, v___x_3540_, v_a_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v_depConfigs_3509_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v_fst_3566_; lean_object* v_snd_3567_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref(v___x_3564_);
v_fst_3566_ = lean_ctor_get(v_a_3565_, 0);
lean_inc(v_fst_3566_);
v_snd_3567_ = lean_ctor_get(v_a_3565_, 1);
lean_inc(v_snd_3567_);
lean_dec(v_a_3565_);
v_____x_3533_ = v_fst_3566_;
v___y_3534_ = v_snd_3567_;
v___y_3535_ = v___y_3506_;
goto v___jp_3532_;
}
else
{
lean_dec_ref(v_leanOpts_3498_);
return v___x_3564_;
}
}
}
v___jp_3511_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3516_ = lean_array_get_size(v_packages_3513_);
v___x_3517_ = lean_box(0);
v___x_3518_ = lean_nat_dec_lt(v___x_3510_, v___x_3516_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
lean_dec_ref(v_packages_3513_);
lean_dec_ref(v_leanOpts_3498_);
v___x_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v_snd_3512_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___y_3514_);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
else
{
uint8_t v___x_3522_; 
v___x_3522_ = lean_nat_dec_le(v___x_3516_, v___x_3516_);
if (v___x_3522_ == 0)
{
if (v___x_3518_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref(v_packages_3513_);
lean_dec_ref(v_leanOpts_3498_);
v___x_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3517_);
lean_ctor_set(v___x_3523_, 1, v_snd_3512_);
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v___y_3514_);
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
return v___x_3525_;
}
else
{
size_t v___x_3526_; size_t v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_usize_of_nat(v___x_3510_);
v___x_3527_ = lean_usize_of_nat(v___x_3516_);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(v_leanOpts_3498_, v___x_3499_, v_packages_3513_, v___x_3526_, v___x_3527_, v___x_3517_, v_snd_3512_, v___y_3514_, v___y_3515_);
lean_dec_ref(v_packages_3513_);
return v___x_3528_;
}
}
else
{
size_t v___x_3529_; size_t v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_usize_of_nat(v___x_3510_);
v___x_3530_ = lean_usize_of_nat(v___x_3516_);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(v_leanOpts_3498_, v___x_3499_, v_packages_3513_, v___x_3529_, v___x_3530_, v___x_3517_, v_snd_3512_, v___y_3514_, v___y_3515_);
lean_dec_ref(v_packages_3513_);
return v___x_3531_;
}
}
}
v___jp_3532_:
{
lean_object* v_snd_3536_; lean_object* v_packages_3537_; 
v_snd_3536_ = lean_ctor_get(v_____x_3533_, 1);
lean_inc(v_snd_3536_);
lean_dec_ref(v_____x_3533_);
v_packages_3537_ = lean_ctor_get(v_snd_3536_, 5);
lean_inc_ref(v_packages_3537_);
v_snd_3512_ = v_snd_3536_;
v_packages_3513_ = v_packages_3537_;
v___y_3514_ = v___y_3534_;
v___y_3515_ = v___y_3535_;
goto v___jp_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg(lean_object* v_leanOpts_3568_, lean_object* v_a_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_baseName_3575_; uint8_t v___x_3576_; 
v_baseName_3575_ = lean_ctor_get(v_a_3569_, 1);
v___x_3576_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(v_baseName_3575_, v___y_3570_);
if (v___x_3576_ == 0)
{
uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = 1;
lean_inc(v___y_3570_);
lean_inc(v_baseName_3575_);
v___x_3578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_baseName_3575_);
lean_ctor_set(v___x_3578_, 1, v___y_3570_);
lean_inc_ref(v_leanOpts_3568_);
v___x_3579_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26(v_leanOpts_3568_, v___x_3578_, v_leanOpts_3568_, v___x_3577_, v_a_3569_, v___x_3578_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec_ref(v___x_3578_);
return v___x_3579_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v_fst_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3593_; 
lean_inc(v_baseName_3575_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v_a_3569_);
lean_dec_ref(v_leanOpts_3568_);
v___x_3580_ = lean_box(0);
v___x_3581_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg___closed__0));
lean_inc(v___y_3570_);
v___x_3582_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__12(v_baseName_3575_, v___x_3576_, v___y_3570_, v___x_3581_);
v_fst_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v___x_3582_, 1);
lean_dec(v_unused_3594_);
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_fst_3583_);
lean_dec(v___x_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
lean_inc(v_baseName_3575_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 1);
lean_ctor_set(v___x_3585_, 1, v_fst_3583_);
lean_ctor_set(v___x_3585_, 0, v_baseName_3575_);
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_baseName_3575_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_fst_3583_);
v___x_3588_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3589_, 0, v_baseName_3575_);
lean_ctor_set(v___x_3589_, 1, v___x_3580_);
v___x_3590_ = l_List_appendTR___redArg(v___x_3588_, v___x_3589_);
v___x_3591_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___redArg(v___x_3590_, v___y_3573_);
return v___x_3591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_leanOpts_3595_, lean_object* v_a_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg(v_leanOpts_3595_, v_a_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3597_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg___boxed(lean_object* v_leanOpts_3603_, lean_object* v___x_3604_, lean_object* v_as_3605_, lean_object* v_i_3606_, lean_object* v_stop_3607_, lean_object* v_b_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
size_t v_i_boxed_3613_; size_t v_stop_boxed_3614_; lean_object* v_res_3615_; 
v_i_boxed_3613_ = lean_unbox_usize(v_i_3606_);
lean_dec(v_i_3606_);
v_stop_boxed_3614_ = lean_unbox_usize(v_stop_3607_);
lean_dec(v_stop_3607_);
v_res_3615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(v_leanOpts_3603_, v___x_3604_, v_as_3605_, v_i_boxed_3613_, v_stop_boxed_3614_, v_b_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_as_3605_);
lean_dec(v___x_3604_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26___boxed(lean_object* v_leanOpts_3616_, lean_object* v___x_3617_, lean_object* v_leanOpts_3618_, lean_object* v_reconfigure_3619_, lean_object* v_pkg_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
uint8_t v_reconfigure_boxed_3626_; lean_object* v_res_3627_; 
v_reconfigure_boxed_3626_ = lean_unbox(v_reconfigure_3619_);
v_res_3627_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26(v_leanOpts_3616_, v___x_3617_, v_leanOpts_3618_, v_reconfigure_boxed_3626_, v_pkg_3620_, v_a_3621_, v_a_3622_, v___y_3623_, v___y_3624_);
lean_dec_ref(v___y_3624_);
lean_dec(v_a_3621_);
lean_dec(v___x_3617_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_leanOpts_3628_, lean_object* v_ws_3629_, lean_object* v_root_3630_, lean_object* v_stack_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg(v_leanOpts_3628_, v_root_3630_, v_stack_3631_, v_ws_3629_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3654_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3654_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3654_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_fst_3640_; lean_object* v_snd_3641_; lean_object* v_snd_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3652_; 
v_fst_3640_ = lean_ctor_get(v_a_3636_, 0);
lean_inc(v_fst_3640_);
v_snd_3641_ = lean_ctor_get(v_a_3636_, 1);
lean_inc(v_snd_3641_);
lean_dec(v_a_3636_);
v_snd_3642_ = lean_ctor_get(v_fst_3640_, 1);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_fst_3640_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; 
v_unused_3653_ = lean_ctor_get(v_fst_3640_, 0);
lean_dec(v_unused_3653_);
v___x_3644_ = v_fst_3640_;
v_isShared_3645_ = v_isSharedCheck_3652_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_snd_3642_);
lean_dec(v_fst_3640_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3652_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 1, v_snd_3641_);
lean_ctor_set(v___x_3644_, 0, v_snd_3642_);
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_snd_3642_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_snd_3641_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v___x_3647_);
v___x_3649_ = v___x_3638_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
v_a_3655_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3635_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3635_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___boxed(lean_object* v_leanOpts_3663_, lean_object* v_ws_3664_, lean_object* v_root_3665_, lean_object* v_stack_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_leanOpts_3663_, v_ws_3664_, v_root_3665_, v_stack_3666_, v___y_3667_, v___y_3668_);
lean_dec_ref(v___y_3668_);
lean_dec(v_stack_3666_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_leanOpts_3671_, lean_object* v_as_3672_, size_t v_i_3673_, size_t v_stop_3674_, lean_object* v_b_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v___x_3679_; 
v___x_3679_ = lean_usize_dec_eq(v_i_3673_, v_stop_3674_);
if (v___x_3679_ == 0)
{
lean_object* v_root_3680_; lean_object* v_baseName_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v_root_3680_ = lean_ctor_get(v_b_3675_, 0);
v_baseName_3681_ = lean_ctor_get(v_root_3680_, 1);
v___x_3682_ = lean_array_uget_borrowed(v_as_3672_, v_i_3673_);
v___x_3683_ = lean_box(0);
lean_inc(v_baseName_3681_);
v___x_3684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3684_, 0, v_baseName_3681_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
lean_inc(v___x_3682_);
lean_inc_ref(v_leanOpts_3671_);
v___x_3685_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_leanOpts_3671_, v_b_3675_, v___x_3682_, v___x_3684_, v___y_3676_, v___y_3677_);
lean_dec_ref(v___x_3684_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v_fst_3687_; lean_object* v_snd_3688_; size_t v___x_3689_; size_t v___x_3690_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref(v___x_3685_);
v_fst_3687_ = lean_ctor_get(v_a_3686_, 0);
lean_inc(v_fst_3687_);
v_snd_3688_ = lean_ctor_get(v_a_3686_, 1);
lean_inc(v_snd_3688_);
lean_dec(v_a_3686_);
v___x_3689_ = ((size_t)1ULL);
v___x_3690_ = lean_usize_add(v_i_3673_, v___x_3689_);
v_i_3673_ = v___x_3690_;
v_b_3675_ = v_fst_3687_;
v___y_3676_ = v_snd_3688_;
goto _start;
}
else
{
lean_dec_ref(v_leanOpts_3671_);
return v___x_3685_;
}
}
else
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_dec_ref(v_leanOpts_3671_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_b_3675_);
lean_ctor_set(v___x_3692_, 1, v___y_3676_);
v___x_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
return v___x_3693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_leanOpts_3694_, lean_object* v_as_3695_, lean_object* v_i_3696_, lean_object* v_stop_3697_, lean_object* v_b_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
size_t v_i_boxed_3702_; size_t v_stop_boxed_3703_; lean_object* v_res_3704_; 
v_i_boxed_3702_ = lean_unbox_usize(v_i_3696_);
lean_dec(v_i_3696_);
v_stop_boxed_3703_ = lean_unbox_usize(v_stop_3697_);
lean_dec(v_stop_3697_);
v_res_3704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_leanOpts_3694_, v_as_3695_, v_i_boxed_3702_, v_stop_boxed_3703_, v_b_3698_, v___y_3699_, v___y_3700_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v_as_3695_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(lean_object* v_leanOpts_3705_, lean_object* v_as_3706_, size_t v_i_3707_, size_t v_stop_3708_, lean_object* v_b_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
uint8_t v___x_3716_; 
v___x_3716_ = lean_usize_dec_eq(v_i_3707_, v_stop_3708_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v_fst_3718_; lean_object* v_snd_3719_; lean_object* v___x_3720_; 
v___x_3717_ = lean_array_uget_borrowed(v_as_3706_, v_i_3707_);
v_fst_3718_ = lean_ctor_get(v___x_3717_, 0);
v_snd_3719_ = lean_ctor_get(v___x_3717_, 1);
lean_inc(v_snd_3719_);
v___x_3720_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_snd_3719_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3796_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3796_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3796_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_snd_3725_; lean_object* v_opts_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_snd_3725_ = lean_ctor_get(v_a_3721_, 1);
lean_inc(v_snd_3725_);
lean_dec(v_a_3721_);
v_opts_3726_ = lean_ctor_get(v_fst_3718_, 4);
v___x_3727_ = 1;
v___x_3728_ = lean_unsigned_to_nat(0u);
v___x_3729_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_3705_);
lean_inc(v_opts_3726_);
lean_inc(v_snd_3719_);
v___x_3730_ = l___private_Lake_Load_Resolve_0__Lake_addDepPackage(v_snd_3719_, v_opts_3726_, v_leanOpts_3705_, v___x_3727_, v_b_3709_, v___x_3729_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v_a_3732_; lean_object* v_snd_3734_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
lean_del_object(v___x_3723_);
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
v_a_3732_ = lean_ctor_get(v___x_3730_, 1);
lean_inc(v_a_3732_);
lean_dec_ref(v___x_3730_);
v___x_3739_ = lean_array_get_size(v_a_3732_);
v___x_3740_ = lean_nat_dec_lt(v___x_3728_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_dec(v_a_3732_);
v_snd_3734_ = v_snd_3725_;
goto v___jp_3733_;
}
else
{
lean_object* v___x_3741_; uint8_t v___x_3742_; 
v___x_3741_ = lean_box(0);
v___x_3742_ = lean_nat_dec_le(v___x_3739_, v___x_3739_);
if (v___x_3742_ == 0)
{
if (v___x_3740_ == 0)
{
lean_dec(v_a_3732_);
v_snd_3734_ = v_snd_3725_;
goto v___jp_3733_;
}
else
{
size_t v___x_3743_; size_t v___x_3744_; lean_object* v___x_3745_; 
v___x_3743_ = ((size_t)0ULL);
v___x_3744_ = lean_usize_of_nat(v___x_3739_);
v___x_3745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3732_, v___x_3743_, v___x_3744_, v___x_3741_, v___y_3711_);
lean_dec(v_a_3732_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_dec_ref(v___x_3745_);
v_snd_3734_ = v_snd_3725_;
goto v___jp_3733_;
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3731_);
lean_dec(v_snd_3725_);
lean_dec_ref(v_leanOpts_3705_);
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
else
{
size_t v___x_3754_; size_t v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = ((size_t)0ULL);
v___x_3755_ = lean_usize_of_nat(v___x_3739_);
v___x_3756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3732_, v___x_3754_, v___x_3755_, v___x_3741_, v___y_3711_);
lean_dec(v_a_3732_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_dec_ref(v___x_3756_);
v_snd_3734_ = v_snd_3725_;
goto v___jp_3733_;
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3731_);
lean_dec(v_snd_3725_);
lean_dec_ref(v_leanOpts_3705_);
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
v___jp_3733_:
{
lean_object* v_snd_3735_; size_t v___x_3736_; size_t v___x_3737_; 
v_snd_3735_ = lean_ctor_get(v_a_3731_, 1);
lean_inc(v_snd_3735_);
lean_dec(v_a_3731_);
v___x_3736_ = ((size_t)1ULL);
v___x_3737_ = lean_usize_add(v_i_3707_, v___x_3736_);
v_i_3707_ = v___x_3737_;
v_b_3709_ = v_snd_3735_;
v___y_3710_ = v_snd_3734_;
goto _start;
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3766_; uint8_t v___x_3767_; 
lean_dec(v_snd_3725_);
lean_dec_ref(v_leanOpts_3705_);
v_a_3765_ = lean_ctor_get(v___x_3730_, 1);
lean_inc(v_a_3765_);
lean_dec_ref(v___x_3730_);
v___x_3766_ = lean_array_get_size(v_a_3765_);
v___x_3767_ = lean_nat_dec_lt(v___x_3728_, v___x_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; lean_object* v___x_3770_; 
lean_dec(v_a_3765_);
v___x_3768_ = lean_box(0);
if (v_isShared_3724_ == 0)
{
lean_ctor_set_tag(v___x_3723_, 1);
lean_ctor_set(v___x_3723_, 0, v___x_3768_);
v___x_3770_ = v___x_3723_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
else
{
lean_object* v___x_3772_; uint8_t v___x_3773_; 
lean_del_object(v___x_3723_);
v___x_3772_ = lean_box(0);
v___x_3773_ = lean_nat_dec_le(v___x_3766_, v___x_3766_);
if (v___x_3773_ == 0)
{
if (v___x_3767_ == 0)
{
lean_dec(v_a_3765_);
goto v___jp_3713_;
}
else
{
size_t v___x_3774_; size_t v___x_3775_; lean_object* v___x_3776_; 
v___x_3774_ = ((size_t)0ULL);
v___x_3775_ = lean_usize_of_nat(v___x_3766_);
v___x_3776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3765_, v___x_3774_, v___x_3775_, v___x_3772_, v___y_3711_);
lean_dec(v_a_3765_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_dec_ref(v___x_3776_);
goto v___jp_3713_;
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3776_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
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
}
else
{
size_t v___x_3785_; size_t v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = ((size_t)0ULL);
v___x_3786_ = lean_usize_of_nat(v___x_3766_);
v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_3765_, v___x_3785_, v___x_3786_, v___x_3772_, v___y_3711_);
lean_dec(v_a_3765_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_dec_ref(v___x_3787_);
goto v___jp_3713_;
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
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
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_b_3709_);
lean_dec_ref(v_leanOpts_3705_);
v_a_3797_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3720_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3720_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
lean_dec_ref(v_leanOpts_3705_);
v___x_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3805_, 0, v_b_3709_);
lean_ctor_set(v___x_3805_, 1, v___y_3710_);
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
v___jp_3713_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = lean_box(0);
v___x_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10___boxed(lean_object* v_leanOpts_3807_, lean_object* v_as_3808_, lean_object* v_i_3809_, lean_object* v_stop_3810_, lean_object* v_b_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
size_t v_i_boxed_3815_; size_t v_stop_boxed_3816_; lean_object* v_res_3817_; 
v_i_boxed_3815_ = lean_unbox_usize(v_i_3809_);
lean_dec(v_i_3809_);
v_stop_boxed_3816_ = lean_unbox_usize(v_stop_3810_);
lean_dec(v_stop_3810_);
v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(v_leanOpts_3807_, v_as_3808_, v_i_boxed_3815_, v_stop_boxed_3816_, v_b_3811_, v___y_3812_, v___y_3813_);
lean_dec_ref(v___y_3813_);
lean_dec_ref(v_as_3808_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17___redArg(lean_object* v_msg_3818_){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3819_ = lean_box(1);
v___x_3820_ = lean_panic_fn_borrowed(v___x_3819_, v_msg_3818_);
return v___x_3820_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3824_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__2));
v___x_3825_ = lean_unsigned_to_nat(35u);
v___x_3826_ = lean_unsigned_to_nat(276u);
v___x_3827_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__1));
v___x_3828_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__0));
v___x_3829_ = l_mkPanicMessageWithDecl(v___x_3828_, v___x_3827_, v___x_3826_, v___x_3825_, v___x_3824_);
return v___x_3829_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3830_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__2));
v___x_3831_ = lean_unsigned_to_nat(21u);
v___x_3832_ = lean_unsigned_to_nat(277u);
v___x_3833_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__1));
v___x_3834_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__0));
v___x_3835_ = l_mkPanicMessageWithDecl(v___x_3834_, v___x_3833_, v___x_3832_, v___x_3831_, v___x_3830_);
return v___x_3835_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3838_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__6));
v___x_3839_ = lean_unsigned_to_nat(35u);
v___x_3840_ = lean_unsigned_to_nat(182u);
v___x_3841_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__5));
v___x_3842_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__0));
v___x_3843_ = l_mkPanicMessageWithDecl(v___x_3842_, v___x_3841_, v___x_3840_, v___x_3839_, v___x_3838_);
return v___x_3843_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3844_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__6));
v___x_3845_ = lean_unsigned_to_nat(21u);
v___x_3846_ = lean_unsigned_to_nat(183u);
v___x_3847_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__5));
v___x_3848_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__0));
v___x_3849_ = l_mkPanicMessageWithDecl(v___x_3848_, v___x_3847_, v___x_3846_, v___x_3845_, v___x_3844_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg(lean_object* v_k_3850_, lean_object* v_v_3851_, lean_object* v_t_3852_){
_start:
{
if (lean_obj_tag(v_t_3852_) == 0)
{
lean_object* v_size_3853_; lean_object* v_k_3854_; lean_object* v_v_3855_; lean_object* v_l_3856_; lean_object* v_r_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_4214_; 
v_size_3853_ = lean_ctor_get(v_t_3852_, 0);
v_k_3854_ = lean_ctor_get(v_t_3852_, 1);
v_v_3855_ = lean_ctor_get(v_t_3852_, 2);
v_l_3856_ = lean_ctor_get(v_t_3852_, 3);
v_r_3857_ = lean_ctor_get(v_t_3852_, 4);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_t_3852_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_3859_ = v_t_3852_;
v_isShared_3860_ = v_isSharedCheck_4214_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_r_3857_);
lean_inc(v_l_3856_);
lean_inc(v_v_3855_);
lean_inc(v_k_3854_);
lean_inc(v_size_3853_);
lean_dec(v_t_3852_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_4214_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
uint8_t v___x_3861_; 
v___x_3861_ = lean_string_dec_lt(v_k_3850_, v_k_3854_);
if (v___x_3861_ == 0)
{
uint8_t v___x_3862_; 
v___x_3862_ = lean_string_dec_eq(v_k_3850_, v_k_3854_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_dec(v_size_3853_);
v___x_3863_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg(v_k_3850_, v_v_3851_, v_r_3857_);
if (lean_obj_tag(v_l_3856_) == 0)
{
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_size_3864_; lean_object* v_size_3865_; lean_object* v_k_3866_; lean_object* v_v_3867_; lean_object* v_l_3868_; lean_object* v_r_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v_size_3864_ = lean_ctor_get(v_l_3856_, 0);
v_size_3865_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_size_3865_);
v_k_3866_ = lean_ctor_get(v___x_3863_, 1);
lean_inc(v_k_3866_);
v_v_3867_ = lean_ctor_get(v___x_3863_, 2);
lean_inc(v_v_3867_);
v_l_3868_ = lean_ctor_get(v___x_3863_, 3);
lean_inc(v_l_3868_);
v_r_3869_ = lean_ctor_get(v___x_3863_, 4);
lean_inc(v_r_3869_);
v___x_3870_ = lean_unsigned_to_nat(3u);
v___x_3871_ = lean_nat_mul(v___x_3870_, v_size_3864_);
v___x_3872_ = lean_nat_dec_lt(v___x_3871_, v_size_3865_);
lean_dec(v___x_3871_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_dec(v_r_3869_);
lean_dec(v_l_3868_);
lean_dec(v_v_3867_);
lean_dec(v_k_3866_);
v___x_3873_ = lean_unsigned_to_nat(1u);
v___x_3874_ = lean_nat_add(v___x_3873_, v_size_3864_);
v___x_3875_ = lean_nat_add(v___x_3874_, v_size_3865_);
lean_dec(v_size_3865_);
lean_dec(v___x_3874_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_3863_);
lean_ctor_set(v___x_3859_, 0, v___x_3875_);
v___x_3877_ = v___x_3859_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3878_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_3878_, 4, v___x_3863_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
else
{
lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3948_; 
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; 
v_unused_3949_ = lean_ctor_get(v___x_3863_, 4);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v___x_3863_, 3);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v___x_3863_, 2);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v___x_3863_, 1);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v___x_3863_, 0);
lean_dec(v_unused_3953_);
v___x_3880_ = v___x_3863_;
v_isShared_3881_ = v_isSharedCheck_3948_;
goto v_resetjp_3879_;
}
else
{
lean_dec(v___x_3863_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3948_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
if (lean_obj_tag(v_l_3868_) == 0)
{
if (lean_obj_tag(v_r_3869_) == 0)
{
lean_object* v_size_3882_; lean_object* v_k_3883_; lean_object* v_v_3884_; lean_object* v_l_3885_; lean_object* v_r_3886_; lean_object* v_size_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; uint8_t v___x_3890_; 
v_size_3882_ = lean_ctor_get(v_l_3868_, 0);
v_k_3883_ = lean_ctor_get(v_l_3868_, 1);
v_v_3884_ = lean_ctor_get(v_l_3868_, 2);
v_l_3885_ = lean_ctor_get(v_l_3868_, 3);
v_r_3886_ = lean_ctor_get(v_l_3868_, 4);
v_size_3887_ = lean_ctor_get(v_r_3869_, 0);
v___x_3888_ = lean_unsigned_to_nat(2u);
v___x_3889_ = lean_nat_mul(v___x_3888_, v_size_3887_);
v___x_3890_ = lean_nat_dec_lt(v_size_3882_, v___x_3889_);
lean_dec(v___x_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3919_; 
lean_inc(v_r_3886_);
lean_inc(v_l_3885_);
lean_inc(v_v_3884_);
lean_inc(v_k_3883_);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_l_3868_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; lean_object* v_unused_3924_; 
v_unused_3920_ = lean_ctor_get(v_l_3868_, 4);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_l_3868_, 3);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_l_3868_, 2);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_l_3868_, 1);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_l_3868_, 0);
lean_dec(v_unused_3924_);
v___x_3892_ = v_l_3868_;
v_isShared_3893_ = v_isSharedCheck_3919_;
goto v_resetjp_3891_;
}
else
{
lean_dec(v_l_3868_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3919_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3909_; 
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = lean_nat_add(v___x_3894_, v_size_3864_);
v___x_3896_ = lean_nat_add(v___x_3895_, v_size_3865_);
lean_dec(v_size_3865_);
if (lean_obj_tag(v_l_3885_) == 0)
{
lean_object* v_size_3917_; 
v_size_3917_ = lean_ctor_get(v_l_3885_, 0);
lean_inc(v_size_3917_);
v___y_3909_ = v_size_3917_;
goto v___jp_3908_;
}
else
{
lean_object* v___x_3918_; 
v___x_3918_ = lean_unsigned_to_nat(0u);
v___y_3909_ = v___x_3918_;
goto v___jp_3908_;
}
v___jp_3897_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = lean_nat_add(v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec(v___y_3899_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 4, v_r_3869_);
lean_ctor_set(v___x_3892_, 3, v_r_3886_);
lean_ctor_set(v___x_3892_, 2, v_v_3867_);
lean_ctor_set(v___x_3892_, 1, v_k_3866_);
lean_ctor_set(v___x_3892_, 0, v___x_3901_);
v___x_3903_ = v___x_3892_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_k_3866_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v_v_3867_);
lean_ctor_set(v_reuseFailAlloc_3907_, 3, v_r_3886_);
lean_ctor_set(v_reuseFailAlloc_3907_, 4, v_r_3869_);
v___x_3903_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3905_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 4, v___x_3903_);
lean_ctor_set(v___x_3880_, 3, v___y_3898_);
lean_ctor_set(v___x_3880_, 2, v_v_3884_);
lean_ctor_set(v___x_3880_, 1, v_k_3883_);
lean_ctor_set(v___x_3880_, 0, v___x_3896_);
v___x_3905_ = v___x_3880_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_k_3883_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_v_3884_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v___y_3898_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
v___jp_3908_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_nat_add(v___x_3895_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec(v___x_3895_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_l_3885_);
lean_ctor_set(v___x_3859_, 0, v___x_3910_);
v___x_3912_ = v___x_3859_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3916_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_3916_, 4, v_l_3885_);
v___x_3912_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_nat_add(v___x_3894_, v_size_3887_);
if (lean_obj_tag(v_r_3886_) == 0)
{
lean_object* v_size_3914_; 
v_size_3914_ = lean_ctor_get(v_r_3886_, 0);
lean_inc(v_size_3914_);
v___y_3898_ = v___x_3912_;
v___y_3899_ = v___x_3913_;
v___y_3900_ = v_size_3914_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3915_; 
v___x_3915_ = lean_unsigned_to_nat(0u);
v___y_3898_ = v___x_3912_;
v___y_3899_ = v___x_3913_;
v___y_3900_ = v___x_3915_;
goto v___jp_3897_;
}
}
}
}
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
lean_del_object(v___x_3859_);
v___x_3925_ = lean_unsigned_to_nat(1u);
v___x_3926_ = lean_nat_add(v___x_3925_, v_size_3864_);
v___x_3927_ = lean_nat_add(v___x_3926_, v_size_3865_);
lean_dec(v_size_3865_);
v___x_3928_ = lean_nat_add(v___x_3926_, v_size_3882_);
lean_dec(v___x_3926_);
lean_inc_ref(v_l_3856_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 4, v_l_3868_);
lean_ctor_set(v___x_3880_, 3, v_l_3856_);
lean_ctor_set(v___x_3880_, 2, v_v_3855_);
lean_ctor_set(v___x_3880_, 1, v_k_3854_);
lean_ctor_set(v___x_3880_, 0, v___x_3928_);
v___x_3930_ = v___x_3880_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v_l_3868_);
v___x_3930_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
v_isSharedCheck_3937_ = !lean_is_exclusive(v_l_3856_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; 
v_unused_3938_ = lean_ctor_get(v_l_3856_, 4);
lean_dec(v_unused_3938_);
v_unused_3939_ = lean_ctor_get(v_l_3856_, 3);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_l_3856_, 2);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_l_3856_, 1);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_l_3856_, 0);
lean_dec(v_unused_3942_);
v___x_3932_ = v_l_3856_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_dec(v_l_3856_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 4, v_r_3869_);
lean_ctor_set(v___x_3932_, 3, v___x_3930_);
lean_ctor_set(v___x_3932_, 2, v_v_3867_);
lean_ctor_set(v___x_3932_, 1, v_k_3866_);
lean_ctor_set(v___x_3932_, 0, v___x_3927_);
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_k_3866_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_v_3867_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_r_3869_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
lean_dec_ref(v_l_3868_);
lean_del_object(v___x_3880_);
lean_dec(v_v_3867_);
lean_dec(v_k_3866_);
lean_dec(v_size_3865_);
lean_dec_ref(v_l_3856_);
lean_del_object(v___x_3859_);
lean_dec(v_v_3855_);
lean_dec(v_k_3854_);
v___x_3944_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__3);
v___x_3945_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17___redArg(v___x_3944_);
return v___x_3945_;
}
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_del_object(v___x_3880_);
lean_dec(v_r_3869_);
lean_dec(v_v_3867_);
lean_dec(v_k_3866_);
lean_dec(v_size_3865_);
lean_dec_ref(v_l_3856_);
lean_del_object(v___x_3859_);
lean_dec(v_v_3855_);
lean_dec(v_k_3854_);
v___x_3946_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__4);
v___x_3947_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17___redArg(v___x_3946_);
return v___x_3947_;
}
}
}
}
else
{
lean_object* v_size_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3958_; 
v_size_3954_ = lean_ctor_get(v_l_3856_, 0);
v___x_3955_ = lean_unsigned_to_nat(1u);
v___x_3956_ = lean_nat_add(v___x_3955_, v_size_3954_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_3863_);
lean_ctor_set(v___x_3859_, 0, v___x_3956_);
v___x_3958_ = v___x_3859_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3959_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3959_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_3959_, 4, v___x_3863_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
else
{
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_l_3960_; 
v_l_3960_ = lean_ctor_get(v___x_3863_, 3);
lean_inc(v_l_3960_);
if (lean_obj_tag(v_l_3960_) == 0)
{
lean_object* v_r_3961_; 
v_r_3961_ = lean_ctor_get(v___x_3863_, 4);
lean_inc(v_r_3961_);
if (lean_obj_tag(v_r_3961_) == 0)
{
lean_object* v_size_3962_; lean_object* v_k_3963_; lean_object* v_v_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3978_; 
v_size_3962_ = lean_ctor_get(v___x_3863_, 0);
v_k_3963_ = lean_ctor_get(v___x_3863_, 1);
v_v_3964_ = lean_ctor_get(v___x_3863_, 2);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3978_ == 0)
{
lean_object* v_unused_3979_; lean_object* v_unused_3980_; 
v_unused_3979_ = lean_ctor_get(v___x_3863_, 4);
lean_dec(v_unused_3979_);
v_unused_3980_ = lean_ctor_get(v___x_3863_, 3);
lean_dec(v_unused_3980_);
v___x_3966_ = v___x_3863_;
v_isShared_3967_ = v_isSharedCheck_3978_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_v_3964_);
lean_inc(v_k_3963_);
lean_inc(v_size_3962_);
lean_dec(v___x_3863_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3978_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v_size_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
v_size_3968_ = lean_ctor_get(v_l_3960_, 0);
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = lean_nat_add(v___x_3969_, v_size_3962_);
lean_dec(v_size_3962_);
v___x_3971_ = lean_nat_add(v___x_3969_, v_size_3968_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 4, v_l_3960_);
lean_ctor_set(v___x_3966_, 3, v_l_3856_);
lean_ctor_set(v___x_3966_, 2, v_v_3855_);
lean_ctor_set(v___x_3966_, 1, v_k_3854_);
lean_ctor_set(v___x_3966_, 0, v___x_3971_);
v___x_3973_ = v___x_3966_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3971_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v_l_3960_);
v___x_3973_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
lean_object* v___x_3975_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_r_3961_);
lean_ctor_set(v___x_3859_, 3, v___x_3973_);
lean_ctor_set(v___x_3859_, 2, v_v_3964_);
lean_ctor_set(v___x_3859_, 1, v_k_3963_);
lean_ctor_set(v___x_3859_, 0, v___x_3970_);
v___x_3975_ = v___x_3859_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v_k_3963_);
lean_ctor_set(v_reuseFailAlloc_3976_, 2, v_v_3964_);
lean_ctor_set(v_reuseFailAlloc_3976_, 3, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3976_, 4, v_r_3961_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
else
{
lean_object* v_k_3981_; lean_object* v_v_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4006_; 
v_k_3981_ = lean_ctor_get(v___x_3863_, 1);
v_v_3982_ = lean_ctor_get(v___x_3863_, 2);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; lean_object* v_unused_4008_; lean_object* v_unused_4009_; 
v_unused_4007_ = lean_ctor_get(v___x_3863_, 4);
lean_dec(v_unused_4007_);
v_unused_4008_ = lean_ctor_get(v___x_3863_, 3);
lean_dec(v_unused_4008_);
v_unused_4009_ = lean_ctor_get(v___x_3863_, 0);
lean_dec(v_unused_4009_);
v___x_3984_ = v___x_3863_;
v_isShared_3985_ = v_isSharedCheck_4006_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_v_3982_);
lean_inc(v_k_3981_);
lean_dec(v___x_3863_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4006_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v_k_3986_; lean_object* v_v_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4002_; 
v_k_3986_ = lean_ctor_get(v_l_3960_, 1);
v_v_3987_ = lean_ctor_get(v_l_3960_, 2);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_l_3960_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; lean_object* v_unused_4004_; lean_object* v_unused_4005_; 
v_unused_4003_ = lean_ctor_get(v_l_3960_, 4);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_l_3960_, 3);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_l_3960_, 0);
lean_dec(v_unused_4005_);
v___x_3989_ = v_l_3960_;
v_isShared_3990_ = v_isSharedCheck_4002_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_v_3987_);
lean_inc(v_k_3986_);
lean_dec(v_l_3960_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4002_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3991_ = lean_unsigned_to_nat(3u);
v___x_3992_ = lean_unsigned_to_nat(1u);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 4, v_r_3961_);
lean_ctor_set(v___x_3989_, 3, v_r_3961_);
lean_ctor_set(v___x_3989_, 2, v_v_3855_);
lean_ctor_set(v___x_3989_, 1, v_k_3854_);
lean_ctor_set(v___x_3989_, 0, v___x_3992_);
v___x_3994_ = v___x_3989_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v_r_3961_);
lean_ctor_set(v_reuseFailAlloc_4001_, 4, v_r_3961_);
v___x_3994_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 3, v_r_3961_);
lean_ctor_set(v___x_3984_, 0, v___x_3992_);
v___x_3996_ = v___x_3984_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v_k_3981_);
lean_ctor_set(v_reuseFailAlloc_4000_, 2, v_v_3982_);
lean_ctor_set(v_reuseFailAlloc_4000_, 3, v_r_3961_);
lean_ctor_set(v_reuseFailAlloc_4000_, 4, v_r_3961_);
v___x_3996_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3998_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_3996_);
lean_ctor_set(v___x_3859_, 3, v___x_3994_);
lean_ctor_set(v___x_3859_, 2, v_v_3987_);
lean_ctor_set(v___x_3859_, 1, v_k_3986_);
lean_ctor_set(v___x_3859_, 0, v___x_3991_);
v___x_3998_ = v___x_3859_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_k_3986_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v_v_3987_);
lean_ctor_set(v_reuseFailAlloc_3999_, 3, v___x_3994_);
lean_ctor_set(v_reuseFailAlloc_3999_, 4, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_4010_; 
v_r_4010_ = lean_ctor_get(v___x_3863_, 4);
lean_inc(v_r_4010_);
if (lean_obj_tag(v_r_4010_) == 0)
{
lean_object* v_k_4011_; lean_object* v_v_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4024_; 
v_k_4011_ = lean_ctor_get(v___x_3863_, 1);
v_v_4012_ = lean_ctor_get(v___x_3863_, 2);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; lean_object* v_unused_4026_; lean_object* v_unused_4027_; 
v_unused_4025_ = lean_ctor_get(v___x_3863_, 4);
lean_dec(v_unused_4025_);
v_unused_4026_ = lean_ctor_get(v___x_3863_, 3);
lean_dec(v_unused_4026_);
v_unused_4027_ = lean_ctor_get(v___x_3863_, 0);
lean_dec(v_unused_4027_);
v___x_4014_ = v___x_3863_;
v_isShared_4015_ = v_isSharedCheck_4024_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_v_4012_);
lean_inc(v_k_4011_);
lean_dec(v___x_3863_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4024_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4019_; 
v___x_4016_ = lean_unsigned_to_nat(3u);
v___x_4017_ = lean_unsigned_to_nat(1u);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 4, v_l_3960_);
lean_ctor_set(v___x_4014_, 2, v_v_3855_);
lean_ctor_set(v___x_4014_, 1, v_k_3854_);
lean_ctor_set(v___x_4014_, 0, v___x_4017_);
v___x_4019_ = v___x_4014_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4017_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4023_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4023_, 3, v_l_3960_);
lean_ctor_set(v_reuseFailAlloc_4023_, 4, v_l_3960_);
v___x_4019_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4021_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_r_4010_);
lean_ctor_set(v___x_3859_, 3, v___x_4019_);
lean_ctor_set(v___x_3859_, 2, v_v_4012_);
lean_ctor_set(v___x_3859_, 1, v_k_4011_);
lean_ctor_set(v___x_3859_, 0, v___x_4016_);
v___x_4021_ = v___x_3859_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_k_4011_);
lean_ctor_set(v_reuseFailAlloc_4022_, 2, v_v_4012_);
lean_ctor_set(v_reuseFailAlloc_4022_, 3, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4022_, 4, v_r_4010_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4028_ = lean_unsigned_to_nat(2u);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_3863_);
lean_ctor_set(v___x_3859_, 3, v_r_4010_);
lean_ctor_set(v___x_3859_, 0, v___x_4028_);
v___x_4030_ = v___x_3859_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4031_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4031_, 3, v_r_4010_);
lean_ctor_set(v_reuseFailAlloc_4031_, 4, v___x_3863_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4032_ = lean_unsigned_to_nat(1u);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_3863_);
lean_ctor_set(v___x_3859_, 3, v___x_3863_);
lean_ctor_set(v___x_3859_, 0, v___x_4032_);
v___x_4034_ = v___x_3859_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4035_, 3, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_4035_, 4, v___x_3863_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
else
{
lean_object* v___x_4037_; 
lean_dec(v_v_3855_);
lean_dec(v_k_3854_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 2, v_v_3851_);
lean_ctor_set(v___x_3859_, 1, v_k_3850_);
v___x_4037_ = v___x_3859_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_size_3853_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v_k_3850_);
lean_ctor_set(v_reuseFailAlloc_4038_, 2, v_v_3851_);
lean_ctor_set(v_reuseFailAlloc_4038_, 3, v_l_3856_);
lean_ctor_set(v_reuseFailAlloc_4038_, 4, v_r_3857_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
else
{
lean_object* v___x_4039_; 
lean_dec(v_size_3853_);
v___x_4039_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg(v_k_3850_, v_v_3851_, v_l_3856_);
if (lean_obj_tag(v_r_3857_) == 0)
{
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_size_4040_; lean_object* v_size_4041_; lean_object* v_k_4042_; lean_object* v_v_4043_; lean_object* v_l_4044_; lean_object* v_r_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; 
v_size_4040_ = lean_ctor_get(v_r_3857_, 0);
v_size_4041_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_size_4041_);
v_k_4042_ = lean_ctor_get(v___x_4039_, 1);
lean_inc(v_k_4042_);
v_v_4043_ = lean_ctor_get(v___x_4039_, 2);
lean_inc(v_v_4043_);
v_l_4044_ = lean_ctor_get(v___x_4039_, 3);
lean_inc(v_l_4044_);
v_r_4045_ = lean_ctor_get(v___x_4039_, 4);
lean_inc(v_r_4045_);
v___x_4046_ = lean_unsigned_to_nat(3u);
v___x_4047_ = lean_nat_mul(v___x_4046_, v_size_4040_);
v___x_4048_ = lean_nat_dec_lt(v___x_4047_, v_size_4041_);
lean_dec(v___x_4047_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4053_; 
lean_dec(v_r_4045_);
lean_dec(v_l_4044_);
lean_dec(v_v_4043_);
lean_dec(v_k_4042_);
v___x_4049_ = lean_unsigned_to_nat(1u);
v___x_4050_ = lean_nat_add(v___x_4049_, v_size_4041_);
lean_dec(v_size_4041_);
v___x_4051_ = lean_nat_add(v___x_4050_, v_size_4040_);
lean_dec(v___x_4050_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 3, v___x_4039_);
lean_ctor_set(v___x_3859_, 0, v___x_4051_);
v___x_4053_ = v___x_3859_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4054_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4054_, 3, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4054_, 4, v_r_3857_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
else
{
lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4126_; 
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4126_ == 0)
{
lean_object* v_unused_4127_; lean_object* v_unused_4128_; lean_object* v_unused_4129_; lean_object* v_unused_4130_; lean_object* v_unused_4131_; 
v_unused_4127_ = lean_ctor_get(v___x_4039_, 4);
lean_dec(v_unused_4127_);
v_unused_4128_ = lean_ctor_get(v___x_4039_, 3);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v___x_4039_, 2);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v___x_4039_, 1);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v___x_4039_, 0);
lean_dec(v_unused_4131_);
v___x_4056_ = v___x_4039_;
v_isShared_4057_ = v_isSharedCheck_4126_;
goto v_resetjp_4055_;
}
else
{
lean_dec(v___x_4039_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4126_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
if (lean_obj_tag(v_l_4044_) == 0)
{
if (lean_obj_tag(v_r_4045_) == 0)
{
lean_object* v_size_4058_; lean_object* v_size_4059_; lean_object* v_k_4060_; lean_object* v_v_4061_; lean_object* v_l_4062_; lean_object* v_r_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_size_4058_ = lean_ctor_get(v_l_4044_, 0);
v_size_4059_ = lean_ctor_get(v_r_4045_, 0);
v_k_4060_ = lean_ctor_get(v_r_4045_, 1);
v_v_4061_ = lean_ctor_get(v_r_4045_, 2);
v_l_4062_ = lean_ctor_get(v_r_4045_, 3);
v_r_4063_ = lean_ctor_get(v_r_4045_, 4);
v___x_4064_ = lean_unsigned_to_nat(2u);
v___x_4065_ = lean_nat_mul(v___x_4064_, v_size_4058_);
v___x_4066_ = lean_nat_dec_lt(v_size_4059_, v___x_4065_);
lean_dec(v___x_4065_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4096_; 
lean_inc(v_r_4063_);
lean_inc(v_l_4062_);
lean_inc(v_v_4061_);
lean_inc(v_k_4060_);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_r_4045_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; lean_object* v_unused_4098_; lean_object* v_unused_4099_; lean_object* v_unused_4100_; lean_object* v_unused_4101_; 
v_unused_4097_ = lean_ctor_get(v_r_4045_, 4);
lean_dec(v_unused_4097_);
v_unused_4098_ = lean_ctor_get(v_r_4045_, 3);
lean_dec(v_unused_4098_);
v_unused_4099_ = lean_ctor_get(v_r_4045_, 2);
lean_dec(v_unused_4099_);
v_unused_4100_ = lean_ctor_get(v_r_4045_, 1);
lean_dec(v_unused_4100_);
v_unused_4101_ = lean_ctor_get(v_r_4045_, 0);
lean_dec(v_unused_4101_);
v___x_4068_ = v_r_4045_;
v_isShared_4069_ = v_isSharedCheck_4096_;
goto v_resetjp_4067_;
}
else
{
lean_dec(v_r_4045_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4096_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___x_4084_; lean_object* v___y_4086_; 
v___x_4070_ = lean_unsigned_to_nat(1u);
v___x_4071_ = lean_nat_add(v___x_4070_, v_size_4041_);
lean_dec(v_size_4041_);
v___x_4072_ = lean_nat_add(v___x_4071_, v_size_4040_);
lean_dec(v___x_4071_);
v___x_4084_ = lean_nat_add(v___x_4070_, v_size_4058_);
if (lean_obj_tag(v_l_4062_) == 0)
{
lean_object* v_size_4094_; 
v_size_4094_ = lean_ctor_get(v_l_4062_, 0);
lean_inc(v_size_4094_);
v___y_4086_ = v_size_4094_;
goto v___jp_4085_;
}
else
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_unsigned_to_nat(0u);
v___y_4086_ = v___x_4095_;
goto v___jp_4085_;
}
v___jp_4073_:
{
lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4077_ = lean_nat_add(v___y_4074_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec(v___y_4074_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 4, v_r_3857_);
lean_ctor_set(v___x_4068_, 3, v_r_4063_);
lean_ctor_set(v___x_4068_, 2, v_v_3855_);
lean_ctor_set(v___x_4068_, 1, v_k_3854_);
lean_ctor_set(v___x_4068_, 0, v___x_4077_);
v___x_4079_ = v___x_4068_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4083_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4083_, 3, v_r_4063_);
lean_ctor_set(v_reuseFailAlloc_4083_, 4, v_r_3857_);
v___x_4079_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
lean_object* v___x_4081_; 
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 4, v___x_4079_);
lean_ctor_set(v___x_4056_, 3, v___y_4075_);
lean_ctor_set(v___x_4056_, 2, v_v_4061_);
lean_ctor_set(v___x_4056_, 1, v_k_4060_);
lean_ctor_set(v___x_4056_, 0, v___x_4072_);
v___x_4081_ = v___x_4056_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_k_4060_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_v_4061_);
lean_ctor_set(v_reuseFailAlloc_4082_, 3, v___y_4075_);
lean_ctor_set(v_reuseFailAlloc_4082_, 4, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
v___jp_4085_:
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
v___x_4087_ = lean_nat_add(v___x_4084_, v___y_4086_);
lean_dec(v___y_4086_);
lean_dec(v___x_4084_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_l_4062_);
lean_ctor_set(v___x_3859_, 3, v_l_4044_);
lean_ctor_set(v___x_3859_, 2, v_v_4043_);
lean_ctor_set(v___x_3859_, 1, v_k_4042_);
lean_ctor_set(v___x_3859_, 0, v___x_4087_);
v___x_4089_ = v___x_3859_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4087_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_k_4042_);
lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_v_4043_);
lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_l_4044_);
lean_ctor_set(v_reuseFailAlloc_4093_, 4, v_l_4062_);
v___x_4089_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
lean_object* v___x_4090_; 
v___x_4090_ = lean_nat_add(v___x_4070_, v_size_4040_);
if (lean_obj_tag(v_r_4063_) == 0)
{
lean_object* v_size_4091_; 
v_size_4091_ = lean_ctor_get(v_r_4063_, 0);
lean_inc(v_size_4091_);
v___y_4074_ = v___x_4090_;
v___y_4075_ = v___x_4089_;
v___y_4076_ = v_size_4091_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4092_; 
v___x_4092_ = lean_unsigned_to_nat(0u);
v___y_4074_ = v___x_4090_;
v___y_4075_ = v___x_4089_;
v___y_4076_ = v___x_4092_;
goto v___jp_4073_;
}
}
}
}
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
lean_del_object(v___x_3859_);
v___x_4102_ = lean_unsigned_to_nat(1u);
v___x_4103_ = lean_nat_add(v___x_4102_, v_size_4041_);
lean_dec(v_size_4041_);
v___x_4104_ = lean_nat_add(v___x_4103_, v_size_4040_);
lean_dec(v___x_4103_);
v___x_4105_ = lean_nat_add(v___x_4102_, v_size_4040_);
v___x_4106_ = lean_nat_add(v___x_4105_, v_size_4059_);
lean_dec(v___x_4105_);
lean_inc_ref(v_r_3857_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 4, v_r_3857_);
lean_ctor_set(v___x_4056_, 3, v_r_4045_);
lean_ctor_set(v___x_4056_, 2, v_v_3855_);
lean_ctor_set(v___x_4056_, 1, v_k_3854_);
lean_ctor_set(v___x_4056_, 0, v___x_4106_);
v___x_4108_ = v___x_4056_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4106_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4121_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4121_, 3, v_r_4045_);
lean_ctor_set(v_reuseFailAlloc_4121_, 4, v_r_3857_);
v___x_4108_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
v_isSharedCheck_4115_ = !lean_is_exclusive(v_r_3857_);
if (v_isSharedCheck_4115_ == 0)
{
lean_object* v_unused_4116_; lean_object* v_unused_4117_; lean_object* v_unused_4118_; lean_object* v_unused_4119_; lean_object* v_unused_4120_; 
v_unused_4116_ = lean_ctor_get(v_r_3857_, 4);
lean_dec(v_unused_4116_);
v_unused_4117_ = lean_ctor_get(v_r_3857_, 3);
lean_dec(v_unused_4117_);
v_unused_4118_ = lean_ctor_get(v_r_3857_, 2);
lean_dec(v_unused_4118_);
v_unused_4119_ = lean_ctor_get(v_r_3857_, 1);
lean_dec(v_unused_4119_);
v_unused_4120_ = lean_ctor_get(v_r_3857_, 0);
lean_dec(v_unused_4120_);
v___x_4110_ = v_r_3857_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v_r_3857_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 4, v___x_4108_);
lean_ctor_set(v___x_4110_, 3, v_l_4044_);
lean_ctor_set(v___x_4110_, 2, v_v_4043_);
lean_ctor_set(v___x_4110_, 1, v_k_4042_);
lean_ctor_set(v___x_4110_, 0, v___x_4104_);
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4104_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_k_4042_);
lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_v_4043_);
lean_ctor_set(v_reuseFailAlloc_4114_, 3, v_l_4044_);
lean_ctor_set(v_reuseFailAlloc_4114_, 4, v___x_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
else
{
lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_dec_ref(v_l_4044_);
lean_del_object(v___x_4056_);
lean_dec(v_v_4043_);
lean_dec(v_k_4042_);
lean_dec(v_size_4041_);
lean_dec_ref(v_r_3857_);
lean_del_object(v___x_3859_);
lean_dec(v_v_3855_);
lean_dec(v_k_3854_);
v___x_4122_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__7);
v___x_4123_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17___redArg(v___x_4122_);
return v___x_4123_;
}
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_del_object(v___x_4056_);
lean_dec(v_r_4045_);
lean_dec(v_v_4043_);
lean_dec(v_k_4042_);
lean_dec(v_size_4041_);
lean_dec_ref(v_r_3857_);
lean_del_object(v___x_3859_);
lean_dec(v_v_3855_);
lean_dec(v_k_3854_);
v___x_4124_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg___closed__8);
v___x_4125_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17___redArg(v___x_4124_);
return v___x_4125_;
}
}
}
}
else
{
lean_object* v_size_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v_size_4132_ = lean_ctor_get(v_r_3857_, 0);
v___x_4133_ = lean_unsigned_to_nat(1u);
v___x_4134_ = lean_nat_add(v___x_4133_, v_size_4132_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 3, v___x_4039_);
lean_ctor_set(v___x_3859_, 0, v___x_4134_);
v___x_4136_ = v___x_3859_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
lean_ctor_set(v_reuseFailAlloc_4137_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4137_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4137_, 3, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4137_, 4, v_r_3857_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
else
{
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_l_4138_; 
v_l_4138_ = lean_ctor_get(v___x_4039_, 3);
lean_inc(v_l_4138_);
if (lean_obj_tag(v_l_4138_) == 0)
{
lean_object* v_r_4139_; 
v_r_4139_ = lean_ctor_get(v___x_4039_, 4);
lean_inc(v_r_4139_);
if (lean_obj_tag(v_r_4139_) == 0)
{
lean_object* v_size_4140_; lean_object* v_k_4141_; lean_object* v_v_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4156_; 
v_size_4140_ = lean_ctor_get(v___x_4039_, 0);
v_k_4141_ = lean_ctor_get(v___x_4039_, 1);
v_v_4142_ = lean_ctor_get(v___x_4039_, 2);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; lean_object* v_unused_4158_; 
v_unused_4157_ = lean_ctor_get(v___x_4039_, 4);
lean_dec(v_unused_4157_);
v_unused_4158_ = lean_ctor_get(v___x_4039_, 3);
lean_dec(v_unused_4158_);
v___x_4144_ = v___x_4039_;
v_isShared_4145_ = v_isSharedCheck_4156_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_v_4142_);
lean_inc(v_k_4141_);
lean_inc(v_size_4140_);
lean_dec(v___x_4039_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4156_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v_size_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; 
v_size_4146_ = lean_ctor_get(v_r_4139_, 0);
v___x_4147_ = lean_unsigned_to_nat(1u);
v___x_4148_ = lean_nat_add(v___x_4147_, v_size_4140_);
lean_dec(v_size_4140_);
v___x_4149_ = lean_nat_add(v___x_4147_, v_size_4146_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 4, v_r_3857_);
lean_ctor_set(v___x_4144_, 3, v_r_4139_);
lean_ctor_set(v___x_4144_, 2, v_v_3855_);
lean_ctor_set(v___x_4144_, 1, v_k_3854_);
lean_ctor_set(v___x_4144_, 0, v___x_4149_);
v___x_4151_ = v___x_4144_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4155_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4155_, 3, v_r_4139_);
lean_ctor_set(v_reuseFailAlloc_4155_, 4, v_r_3857_);
v___x_4151_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4153_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4151_);
lean_ctor_set(v___x_3859_, 3, v_l_4138_);
lean_ctor_set(v___x_3859_, 2, v_v_4142_);
lean_ctor_set(v___x_3859_, 1, v_k_4141_);
lean_ctor_set(v___x_3859_, 0, v___x_4148_);
v___x_4153_ = v___x_3859_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4148_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_k_4141_);
lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_v_4142_);
lean_ctor_set(v_reuseFailAlloc_4154_, 3, v_l_4138_);
lean_ctor_set(v_reuseFailAlloc_4154_, 4, v___x_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v_k_4159_; lean_object* v_v_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4172_; 
v_k_4159_ = lean_ctor_get(v___x_4039_, 1);
v_v_4160_ = lean_ctor_get(v___x_4039_, 2);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4172_ == 0)
{
lean_object* v_unused_4173_; lean_object* v_unused_4174_; lean_object* v_unused_4175_; 
v_unused_4173_ = lean_ctor_get(v___x_4039_, 4);
lean_dec(v_unused_4173_);
v_unused_4174_ = lean_ctor_get(v___x_4039_, 3);
lean_dec(v_unused_4174_);
v_unused_4175_ = lean_ctor_get(v___x_4039_, 0);
lean_dec(v_unused_4175_);
v___x_4162_ = v___x_4039_;
v_isShared_4163_ = v_isSharedCheck_4172_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_v_4160_);
lean_inc(v_k_4159_);
lean_dec(v___x_4039_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4172_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4164_ = lean_unsigned_to_nat(3u);
v___x_4165_ = lean_unsigned_to_nat(1u);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 3, v_r_4139_);
lean_ctor_set(v___x_4162_, 2, v_v_3855_);
lean_ctor_set(v___x_4162_, 1, v_k_3854_);
lean_ctor_set(v___x_4162_, 0, v___x_4165_);
v___x_4167_ = v___x_4162_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4165_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4171_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4171_, 3, v_r_4139_);
lean_ctor_set(v_reuseFailAlloc_4171_, 4, v_r_4139_);
v___x_4167_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
lean_object* v___x_4169_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4167_);
lean_ctor_set(v___x_3859_, 3, v_l_4138_);
lean_ctor_set(v___x_3859_, 2, v_v_4160_);
lean_ctor_set(v___x_3859_, 1, v_k_4159_);
lean_ctor_set(v___x_3859_, 0, v___x_4164_);
v___x_4169_ = v___x_3859_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v_k_4159_);
lean_ctor_set(v_reuseFailAlloc_4170_, 2, v_v_4160_);
lean_ctor_set(v_reuseFailAlloc_4170_, 3, v_l_4138_);
lean_ctor_set(v_reuseFailAlloc_4170_, 4, v___x_4167_);
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
}
else
{
lean_object* v_r_4176_; 
v_r_4176_ = lean_ctor_get(v___x_4039_, 4);
lean_inc(v_r_4176_);
if (lean_obj_tag(v_r_4176_) == 0)
{
lean_object* v_k_4177_; lean_object* v_v_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4202_; 
v_k_4177_ = lean_ctor_get(v___x_4039_, 1);
v_v_4178_ = lean_ctor_get(v___x_4039_, 2);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4202_ == 0)
{
lean_object* v_unused_4203_; lean_object* v_unused_4204_; lean_object* v_unused_4205_; 
v_unused_4203_ = lean_ctor_get(v___x_4039_, 4);
lean_dec(v_unused_4203_);
v_unused_4204_ = lean_ctor_get(v___x_4039_, 3);
lean_dec(v_unused_4204_);
v_unused_4205_ = lean_ctor_get(v___x_4039_, 0);
lean_dec(v_unused_4205_);
v___x_4180_ = v___x_4039_;
v_isShared_4181_ = v_isSharedCheck_4202_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_v_4178_);
lean_inc(v_k_4177_);
lean_dec(v___x_4039_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4202_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v_k_4182_; lean_object* v_v_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4198_; 
v_k_4182_ = lean_ctor_get(v_r_4176_, 1);
v_v_4183_ = lean_ctor_get(v_r_4176_, 2);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_r_4176_);
if (v_isSharedCheck_4198_ == 0)
{
lean_object* v_unused_4199_; lean_object* v_unused_4200_; lean_object* v_unused_4201_; 
v_unused_4199_ = lean_ctor_get(v_r_4176_, 4);
lean_dec(v_unused_4199_);
v_unused_4200_ = lean_ctor_get(v_r_4176_, 3);
lean_dec(v_unused_4200_);
v_unused_4201_ = lean_ctor_get(v_r_4176_, 0);
lean_dec(v_unused_4201_);
v___x_4185_ = v_r_4176_;
v_isShared_4186_ = v_isSharedCheck_4198_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_v_4183_);
lean_inc(v_k_4182_);
lean_dec(v_r_4176_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4198_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4187_ = lean_unsigned_to_nat(3u);
v___x_4188_ = lean_unsigned_to_nat(1u);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 4, v_l_4138_);
lean_ctor_set(v___x_4185_, 3, v_l_4138_);
lean_ctor_set(v___x_4185_, 2, v_v_4178_);
lean_ctor_set(v___x_4185_, 1, v_k_4177_);
lean_ctor_set(v___x_4185_, 0, v___x_4188_);
v___x_4190_ = v___x_4185_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_k_4177_);
lean_ctor_set(v_reuseFailAlloc_4197_, 2, v_v_4178_);
lean_ctor_set(v_reuseFailAlloc_4197_, 3, v_l_4138_);
lean_ctor_set(v_reuseFailAlloc_4197_, 4, v_l_4138_);
v___x_4190_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
lean_object* v___x_4192_; 
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 4, v_l_4138_);
lean_ctor_set(v___x_4180_, 2, v_v_3855_);
lean_ctor_set(v___x_4180_, 1, v_k_3854_);
lean_ctor_set(v___x_4180_, 0, v___x_4188_);
v___x_4192_ = v___x_4180_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4196_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4196_, 3, v_l_4138_);
lean_ctor_set(v_reuseFailAlloc_4196_, 4, v_l_4138_);
v___x_4192_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
lean_object* v___x_4194_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4192_);
lean_ctor_set(v___x_3859_, 3, v___x_4190_);
lean_ctor_set(v___x_3859_, 2, v_v_4183_);
lean_ctor_set(v___x_3859_, 1, v_k_4182_);
lean_ctor_set(v___x_3859_, 0, v___x_4187_);
v___x_4194_ = v___x_3859_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4187_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_k_4182_);
lean_ctor_set(v_reuseFailAlloc_4195_, 2, v_v_4183_);
lean_ctor_set(v_reuseFailAlloc_4195_, 3, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4195_, 4, v___x_4192_);
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
else
{
lean_object* v___x_4206_; lean_object* v___x_4208_; 
v___x_4206_ = lean_unsigned_to_nat(2u);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v_r_4176_);
lean_ctor_set(v___x_3859_, 3, v___x_4039_);
lean_ctor_set(v___x_3859_, 0, v___x_4206_);
v___x_4208_ = v___x_3859_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4209_, 3, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4209_, 4, v_r_4176_);
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
else
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = lean_unsigned_to_nat(1u);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 4, v___x_4039_);
lean_ctor_set(v___x_3859_, 3, v___x_4039_);
lean_ctor_set(v___x_3859_, 0, v___x_4210_);
v___x_4212_ = v___x_3859_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v_k_3854_);
lean_ctor_set(v_reuseFailAlloc_4213_, 2, v_v_3855_);
lean_ctor_set(v_reuseFailAlloc_4213_, 3, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4213_, 4, v___x_4039_);
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
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_unsigned_to_nat(1u);
v___x_4216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4215_);
lean_ctor_set(v___x_4216_, 1, v_k_3850_);
lean_ctor_set(v___x_4216_, 2, v_v_3851_);
lean_ctor_set(v___x_4216_, 3, v_t_3852_);
lean_ctor_set(v___x_4216_, 4, v_t_3852_);
return v___x_4216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__11_spec__19(lean_object* v_init_4217_, lean_object* v_x_4218_){
_start:
{
if (lean_obj_tag(v_x_4218_) == 0)
{
lean_object* v_k_4219_; lean_object* v_v_4220_; lean_object* v_l_4221_; lean_object* v_r_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_k_4219_ = lean_ctor_get(v_x_4218_, 1);
lean_inc(v_k_4219_);
v_v_4220_ = lean_ctor_get(v_x_4218_, 2);
lean_inc(v_v_4220_);
v_l_4221_ = lean_ctor_get(v_x_4218_, 3);
lean_inc(v_l_4221_);
v_r_4222_ = lean_ctor_get(v_x_4218_, 4);
lean_inc(v_r_4222_);
lean_dec_ref(v_x_4218_);
v___x_4223_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__11_spec__19(v_init_4217_, v_l_4221_);
v___x_4224_ = 1;
v___x_4225_ = l_Lean_Name_toString(v_k_4219_, v___x_4224_);
v___x_4226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4226_, 0, v_v_4220_);
v___x_4227_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg(v___x_4225_, v___x_4226_, v___x_4223_);
v_init_4217_ = v___x_4227_;
v_x_4218_ = v_r_4222_;
goto _start;
}
else
{
return v_init_4217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_m_4229_){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4230_ = lean_box(1);
v___x_4231_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__11_spec__19(v___x_4230_, v_m_4229_);
v___x_4232_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v___x_4235_, uint8_t v_updateToolchain_4236_, lean_object* v_ws_4237_, size_t v_sz_4238_, size_t v_i_4239_, lean_object* v_bs_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
uint8_t v___x_4244_; 
v___x_4244_ = lean_usize_dec_lt(v_i_4239_, v_sz_4238_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_dec_ref(v_ws_4237_);
lean_dec_ref(v___x_4235_);
v___x_4245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4245_, 0, v_bs_4240_);
lean_ctor_set(v___x_4245_, 1, v___y_4241_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
else
{
lean_object* v_baseName_4247_; lean_object* v_v_4248_; lean_object* v_name_4249_; lean_object* v_opts_4250_; uint8_t v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_baseName_4247_ = lean_ctor_get(v___x_4235_, 1);
v_v_4248_ = lean_array_uget_borrowed(v_bs_4240_, v_i_4239_);
v_name_4249_ = lean_ctor_get(v_v_4248_, 0);
v_opts_4250_ = lean_ctor_get(v_v_4248_, 4);
v___x_4251_ = 0;
lean_inc(v_baseName_4247_);
v___x_4252_ = l_Lean_Name_toString(v_baseName_4247_, v___x_4251_);
v___x_4253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__0));
v___x_4254_ = lean_string_append(v___x_4252_, v___x_4253_);
lean_inc(v_name_4249_);
v___x_4255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4249_, v_updateToolchain_4236_);
v___x_4256_ = lean_string_append(v___x_4254_, v___x_4255_);
lean_dec_ref(v___x_4255_);
v___x_4257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___closed__1));
v___x_4258_ = lean_string_append(v___x_4256_, v___x_4257_);
lean_inc(v_opts_4250_);
v___x_4259_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_opts_4250_);
v___x_4260_ = lean_unsigned_to_nat(80u);
v___x_4261_ = l_Lean_Json_pretty(v___x_4259_, v___x_4260_);
v___x_4262_ = lean_string_append(v___x_4258_, v___x_4261_);
lean_dec_ref(v___x_4261_);
v___x_4263_ = 0;
v___x_4264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set_uint8(v___x_4264_, sizeof(void*)*1, v___x_4263_);
lean_inc_ref(v___y_4242_);
v___x_4265_ = lean_apply_2(v___y_4242_, v___x_4264_, lean_box(0));
lean_inc(v_v_4248_);
lean_inc_ref(v___x_4235_);
lean_inc_ref(v_ws_4237_);
v___x_4266_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_4237_, v___x_4235_, v_v_4248_, v___y_4241_, v___y_4242_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v_fst_4268_; lean_object* v_snd_4269_; lean_object* v___x_4270_; lean_object* v_bs_x27_4271_; size_t v___x_4272_; size_t v___x_4273_; lean_object* v___x_4274_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref(v___x_4266_);
v_fst_4268_ = lean_ctor_get(v_a_4267_, 0);
lean_inc(v_fst_4268_);
v_snd_4269_ = lean_ctor_get(v_a_4267_, 1);
lean_inc(v_snd_4269_);
lean_dec(v_a_4267_);
v___x_4270_ = lean_unsigned_to_nat(0u);
v_bs_x27_4271_ = lean_array_uset(v_bs_4240_, v_i_4239_, v___x_4270_);
v___x_4272_ = ((size_t)1ULL);
v___x_4273_ = lean_usize_add(v_i_4239_, v___x_4272_);
v___x_4274_ = lean_array_uset(v_bs_x27_4271_, v_i_4239_, v_fst_4268_);
v_i_4239_ = v___x_4273_;
v_bs_4240_ = v___x_4274_;
v___y_4241_ = v_snd_4269_;
goto _start;
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec_ref(v_bs_4240_);
lean_dec_ref(v_ws_4237_);
lean_dec_ref(v___x_4235_);
v_a_4276_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4266_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4266_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7___boxed(lean_object* v___x_4284_, lean_object* v_updateToolchain_4285_, lean_object* v_ws_4286_, lean_object* v_sz_4287_, lean_object* v_i_4288_, lean_object* v_bs_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
uint8_t v_updateToolchain_boxed_4293_; size_t v_sz_boxed_4294_; size_t v_i_boxed_4295_; lean_object* v_res_4296_; 
v_updateToolchain_boxed_4293_ = lean_unbox(v_updateToolchain_4285_);
v_sz_boxed_4294_ = lean_unbox_usize(v_sz_4287_);
lean_dec(v_sz_4287_);
v_i_boxed_4295_ = lean_unbox_usize(v_i_4288_);
lean_dec(v_i_4288_);
v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v___x_4284_, v_updateToolchain_boxed_4293_, v_ws_4286_, v_sz_boxed_4294_, v_i_boxed_4295_, v_bs_4289_, v___y_4290_, v___y_4291_);
lean_dec_ref(v___y_4291_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4297_, lean_object* v_toUpdate_4298_, lean_object* v_leanOpts_4299_, uint8_t v_updateToolchain_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4303_ = lean_box(1);
lean_inc_ref(v_ws_4297_);
v___x_4304_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4301_, v_ws_4297_, v_toUpdate_4298_, v___x_4303_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4305_);
lean_dec_ref(v___x_4304_);
if (v_updateToolchain_4300_ == 0)
{
lean_object* v_snd_4306_; lean_object* v_root_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_snd_4306_ = lean_ctor_get(v_a_4305_, 1);
lean_inc(v_snd_4306_);
lean_dec(v_a_4305_);
v_root_4307_ = lean_ctor_get(v_ws_4297_, 0);
lean_inc_ref(v_root_4307_);
v___x_4308_ = lean_box(0);
v___x_4309_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_leanOpts_4299_, v_ws_4297_, v_root_4307_, v___x_4308_, v_snd_4306_, v_a_4301_);
return v___x_4309_;
}
else
{
lean_object* v_snd_4310_; lean_object* v_root_4311_; lean_object* v_packages_4312_; lean_object* v___y_4314_; lean_object* v_fst_4315_; lean_object* v_packages_4316_; lean_object* v_snd_4317_; lean_object* v___y_4329_; lean_object* v_depConfigs_4334_; lean_object* v___x_4335_; size_t v_sz_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v_snd_4310_ = lean_ctor_get(v_a_4305_, 1);
lean_inc(v_snd_4310_);
lean_dec(v_a_4305_);
v_root_4311_ = lean_ctor_get(v_ws_4297_, 0);
v_packages_4312_ = lean_ctor_get(v_ws_4297_, 5);
lean_inc_ref(v_packages_4312_);
v_depConfigs_4334_ = lean_ctor_get(v_root_4311_, 12);
lean_inc_ref(v_depConfigs_4334_);
v___x_4335_ = l_Array_reverse___redArg(v_depConfigs_4334_);
v_sz_4336_ = lean_array_size(v___x_4335_);
v___x_4337_ = ((size_t)0ULL);
lean_inc_ref(v___x_4335_);
lean_inc_ref(v_ws_4297_);
lean_inc_ref(v_root_4311_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_root_4311_, v_updateToolchain_4300_, v_ws_4297_, v_sz_4336_, v___x_4337_, v___x_4335_, v_snd_4310_, v_a_4301_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v_fst_4340_; lean_object* v_snd_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4380_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
lean_dec_ref(v___x_4338_);
v_fst_4340_ = lean_ctor_get(v_a_4339_, 0);
v_snd_4341_ = lean_ctor_get(v_a_4339_, 1);
v_isSharedCheck_4380_ = !lean_is_exclusive(v_a_4339_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4343_ = v_a_4339_;
v_isShared_4344_ = v_isSharedCheck_4380_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_snd_4341_);
lean_inc(v_fst_4340_);
lean_dec(v_a_4339_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4380_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4345_; 
lean_inc_ref(v_ws_4297_);
v___x_4345_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_a_4301_, v_ws_4297_, v_fst_4340_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4370_; 
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4370_ == 0)
{
lean_object* v_unused_4371_; 
v_unused_4371_ = lean_ctor_get(v___x_4345_, 0);
lean_dec(v_unused_4371_);
v___x_4347_ = v___x_4345_;
v_isShared_4348_ = v_isSharedCheck_4370_;
goto v_resetjp_4346_;
}
else
{
lean_dec(v___x_4345_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4370_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4349_ = l_Array_zip___redArg(v___x_4335_, v_fst_4340_);
lean_dec(v_fst_4340_);
lean_dec_ref(v___x_4335_);
v___x_4350_ = lean_unsigned_to_nat(0u);
v___x_4351_ = lean_array_get_size(v___x_4349_);
v___x_4352_ = lean_nat_dec_lt(v___x_4350_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4354_; 
lean_dec_ref(v___x_4349_);
lean_inc(v_snd_4341_);
lean_inc_ref(v_ws_4297_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v_ws_4297_);
v___x_4354_ = v___x_4343_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_ws_4297_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v_snd_4341_);
v___x_4354_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4356_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4354_);
v___x_4356_ = v___x_4347_;
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
lean_inc_ref(v_packages_4312_);
v___y_4314_ = v___x_4356_;
v_fst_4315_ = v_ws_4297_;
v_packages_4316_ = v_packages_4312_;
v_snd_4317_ = v_snd_4341_;
goto v___jp_4313_;
}
}
}
else
{
uint8_t v___x_4359_; 
v___x_4359_ = lean_nat_dec_le(v___x_4351_, v___x_4351_);
if (v___x_4359_ == 0)
{
if (v___x_4352_ == 0)
{
lean_object* v___x_4361_; 
lean_dec_ref(v___x_4349_);
lean_inc(v_snd_4341_);
lean_inc_ref(v_ws_4297_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 0, v_ws_4297_);
v___x_4361_ = v___x_4343_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_ws_4297_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_snd_4341_);
v___x_4361_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4363_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4361_);
v___x_4363_ = v___x_4347_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_inc_ref(v_packages_4312_);
v___y_4314_ = v___x_4363_;
v_fst_4315_ = v_ws_4297_;
v_packages_4316_ = v_packages_4312_;
v_snd_4317_ = v_snd_4341_;
goto v___jp_4313_;
}
}
}
else
{
size_t v___x_4366_; lean_object* v___x_4367_; 
lean_del_object(v___x_4347_);
lean_del_object(v___x_4343_);
v___x_4366_ = lean_usize_of_nat(v___x_4351_);
lean_inc_ref(v_leanOpts_4299_);
v___x_4367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(v_leanOpts_4299_, v___x_4349_, v___x_4337_, v___x_4366_, v_ws_4297_, v_snd_4341_, v_a_4301_);
lean_dec_ref(v___x_4349_);
v___y_4329_ = v___x_4367_;
goto v___jp_4328_;
}
}
else
{
size_t v___x_4368_; lean_object* v___x_4369_; 
lean_del_object(v___x_4347_);
lean_del_object(v___x_4343_);
v___x_4368_ = lean_usize_of_nat(v___x_4351_);
lean_inc_ref(v_leanOpts_4299_);
v___x_4369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(v_leanOpts_4299_, v___x_4349_, v___x_4337_, v___x_4368_, v_ws_4297_, v_snd_4341_, v_a_4301_);
lean_dec_ref(v___x_4349_);
v___y_4329_ = v___x_4369_;
goto v___jp_4328_;
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_del_object(v___x_4343_);
lean_dec(v_snd_4341_);
lean_dec(v_fst_4340_);
lean_dec_ref(v___x_4335_);
lean_dec_ref(v_packages_4312_);
lean_dec_ref(v_leanOpts_4299_);
lean_dec_ref(v_ws_4297_);
v_a_4372_ = lean_ctor_get(v___x_4345_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4345_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4345_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4345_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v___x_4335_);
lean_dec_ref(v_packages_4312_);
lean_dec_ref(v_leanOpts_4299_);
lean_dec_ref(v_ws_4297_);
v_a_4381_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4338_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4338_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
v___jp_4313_:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v___x_4318_ = lean_array_get_size(v_packages_4312_);
lean_dec_ref(v_packages_4312_);
v___x_4319_ = lean_array_get_size(v_packages_4316_);
v___x_4320_ = lean_nat_dec_lt(v___x_4318_, v___x_4319_);
if (v___x_4320_ == 0)
{
lean_dec(v_snd_4317_);
lean_dec_ref(v_packages_4316_);
lean_dec_ref(v_fst_4315_);
lean_dec_ref(v_leanOpts_4299_);
return v___y_4314_;
}
else
{
uint8_t v___x_4321_; 
v___x_4321_ = lean_nat_dec_le(v___x_4319_, v___x_4319_);
if (v___x_4321_ == 0)
{
if (v___x_4320_ == 0)
{
lean_dec(v_snd_4317_);
lean_dec_ref(v_packages_4316_);
lean_dec_ref(v_fst_4315_);
lean_dec_ref(v_leanOpts_4299_);
return v___y_4314_;
}
else
{
size_t v___x_4322_; size_t v___x_4323_; lean_object* v___x_4324_; 
lean_dec_ref(v___y_4314_);
v___x_4322_ = lean_usize_of_nat(v___x_4318_);
v___x_4323_ = lean_usize_of_nat(v___x_4319_);
v___x_4324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_leanOpts_4299_, v_packages_4316_, v___x_4322_, v___x_4323_, v_fst_4315_, v_snd_4317_, v_a_4301_);
lean_dec_ref(v_packages_4316_);
return v___x_4324_;
}
}
else
{
size_t v___x_4325_; size_t v___x_4326_; lean_object* v___x_4327_; 
lean_dec_ref(v___y_4314_);
v___x_4325_ = lean_usize_of_nat(v___x_4318_);
v___x_4326_ = lean_usize_of_nat(v___x_4319_);
v___x_4327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_leanOpts_4299_, v_packages_4316_, v___x_4325_, v___x_4326_, v_fst_4315_, v_snd_4317_, v_a_4301_);
lean_dec_ref(v_packages_4316_);
return v___x_4327_;
}
}
}
v___jp_4328_:
{
if (lean_obj_tag(v___y_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v_fst_4331_; lean_object* v_snd_4332_; lean_object* v_packages_4333_; 
v_a_4330_ = lean_ctor_get(v___y_4329_, 0);
v_fst_4331_ = lean_ctor_get(v_a_4330_, 0);
lean_inc(v_fst_4331_);
v_snd_4332_ = lean_ctor_get(v_a_4330_, 1);
lean_inc(v_snd_4332_);
v_packages_4333_ = lean_ctor_get(v_fst_4331_, 5);
lean_inc_ref(v_packages_4333_);
v___y_4314_ = v___y_4329_;
v_fst_4315_ = v_fst_4331_;
v_packages_4316_ = v_packages_4333_;
v_snd_4317_ = v_snd_4332_;
goto v___jp_4313_;
}
else
{
lean_dec_ref(v_packages_4312_);
lean_dec_ref(v_leanOpts_4299_);
return v___y_4329_;
}
}
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v_leanOpts_4299_);
lean_dec_ref(v_ws_4297_);
v_a_4389_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4304_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4304_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4397_, lean_object* v_toUpdate_4398_, lean_object* v_leanOpts_4399_, lean_object* v_updateToolchain_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
uint8_t v_updateToolchain_boxed_4403_; lean_object* v_res_4404_; 
v_updateToolchain_boxed_4403_ = lean_unbox(v_updateToolchain_4400_);
v_res_4404_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4397_, v_toUpdate_4398_, v_leanOpts_4399_, v_updateToolchain_boxed_4403_, v_a_4401_);
lean_dec_ref(v_a_4401_);
lean_dec(v_toUpdate_4398_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(lean_object* v___y_4405_, lean_object* v_as_4406_, size_t v_i_4407_, size_t v_stop_4408_, lean_object* v_b_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v___x_4415_; 
v___x_4415_ = lean_usize_dec_eq(v_i_4407_, v_stop_4408_);
if (v___x_4415_ == 0)
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4416_ = lean_array_uget_borrowed(v_as_4406_, v_i_4407_);
lean_inc_ref(v___y_4405_);
lean_inc_ref(v___y_4413_);
lean_inc(v___y_4410_);
lean_inc(v___x_4416_);
v___x_4417_ = lean_apply_6(v___y_4405_, v___x_4416_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, lean_box(0));
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v_fst_4419_; lean_object* v_snd_4420_; lean_object* v_fst_4421_; lean_object* v_snd_4422_; size_t v___x_4423_; size_t v___x_4424_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref(v___x_4417_);
v_fst_4419_ = lean_ctor_get(v_a_4418_, 0);
lean_inc(v_fst_4419_);
v_snd_4420_ = lean_ctor_get(v_a_4418_, 1);
lean_inc(v_snd_4420_);
lean_dec(v_a_4418_);
v_fst_4421_ = lean_ctor_get(v_fst_4419_, 0);
lean_inc(v_fst_4421_);
v_snd_4422_ = lean_ctor_get(v_fst_4419_, 1);
lean_inc(v_snd_4422_);
lean_dec(v_fst_4419_);
v___x_4423_ = ((size_t)1ULL);
v___x_4424_ = lean_usize_add(v_i_4407_, v___x_4423_);
v_i_4407_ = v___x_4424_;
v_b_4409_ = v_fst_4421_;
v___y_4411_ = v_snd_4422_;
v___y_4412_ = v_snd_4420_;
goto _start;
}
else
{
lean_dec_ref(v___y_4405_);
return v___x_4417_;
}
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
lean_dec_ref(v___y_4405_);
v___x_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4426_, 0, v_b_4409_);
lean_ctor_set(v___x_4426_, 1, v___y_4411_);
v___x_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
lean_ctor_set(v___x_4427_, 1, v___y_4412_);
v___x_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
return v___x_4428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5___boxed(lean_object* v___y_4429_, lean_object* v_as_4430_, lean_object* v_i_4431_, lean_object* v_stop_4432_, lean_object* v_b_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
size_t v_i_boxed_4439_; size_t v_stop_boxed_4440_; lean_object* v_res_4441_; 
v_i_boxed_4439_ = lean_unbox_usize(v_i_4431_);
lean_dec(v_i_4431_);
v_stop_boxed_4440_ = lean_unbox_usize(v_stop_4432_);
lean_dec(v_stop_4432_);
v_res_4441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(v___y_4429_, v_as_4430_, v_i_boxed_4439_, v_stop_boxed_4440_, v_b_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4434_);
lean_dec_ref(v_as_4430_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v___y_4442_, lean_object* v_leanOpts_4443_, uint8_t v_reconfigure_4444_, lean_object* v_pkg_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_packages_4451_; lean_object* v_depConfigs_4452_; lean_object* v___x_4453_; lean_object* v_snd_4455_; lean_object* v_packages_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v_____x_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v_packages_4451_ = lean_ctor_get(v_a_4447_, 5);
v_depConfigs_4452_ = lean_ctor_get(v_pkg_4445_, 12);
lean_inc_ref(v_depConfigs_4452_);
v___x_4453_ = lean_array_get_size(v_packages_4451_);
v___x_4481_ = lean_array_get_size(v_depConfigs_4452_);
v___x_4482_ = lean_unsigned_to_nat(0u);
v___x_4483_ = lean_box(0);
v___x_4484_ = lean_nat_dec_le(v___x_4481_, v___x_4481_);
if (v___x_4484_ == 0)
{
uint8_t v___x_4485_; 
v___x_4485_ = lean_nat_dec_lt(v___x_4482_, v___x_4481_);
if (v___x_4485_ == 0)
{
uint8_t v___x_4486_; 
lean_dec_ref(v_depConfigs_4452_);
lean_dec_ref(v_pkg_4445_);
lean_dec_ref(v_leanOpts_4443_);
v___x_4486_ = lean_nat_dec_lt(v___x_4453_, v___x_4453_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
lean_dec_ref(v___y_4442_);
v___x_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4483_);
lean_ctor_set(v___x_4487_, 1, v_a_4447_);
v___x_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
lean_ctor_set(v___x_4488_, 1, v___y_4448_);
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
return v___x_4489_;
}
else
{
uint8_t v___x_4490_; 
v___x_4490_ = lean_nat_dec_le(v___x_4453_, v___x_4453_);
if (v___x_4490_ == 0)
{
if (v___x_4486_ == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
lean_dec_ref(v___y_4442_);
v___x_4491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4483_);
lean_ctor_set(v___x_4491_, 1, v_a_4447_);
v___x_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set(v___x_4492_, 1, v___y_4448_);
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
return v___x_4493_;
}
else
{
size_t v___x_4494_; lean_object* v___x_4495_; 
lean_inc_ref(v_packages_4451_);
v___x_4494_ = lean_usize_of_nat(v___x_4453_);
v___x_4495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(v___y_4442_, v_packages_4451_, v___x_4494_, v___x_4494_, v___x_4483_, v_a_4446_, v_a_4447_, v___y_4448_, v___y_4449_);
lean_dec_ref(v_packages_4451_);
return v___x_4495_;
}
}
else
{
size_t v___x_4496_; lean_object* v___x_4497_; 
lean_inc_ref(v_packages_4451_);
v___x_4496_ = lean_usize_of_nat(v___x_4453_);
v___x_4497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(v___y_4442_, v_packages_4451_, v___x_4496_, v___x_4496_, v___x_4483_, v_a_4446_, v_a_4447_, v___y_4448_, v___y_4449_);
lean_dec_ref(v_packages_4451_);
return v___x_4497_;
}
}
}
else
{
size_t v___x_4498_; size_t v___x_4499_; lean_object* v___x_4500_; 
v___x_4498_ = lean_usize_of_nat(v___x_4481_);
v___x_4499_ = ((size_t)0ULL);
v___x_4500_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_4445_, v_leanOpts_4443_, v_reconfigure_4444_, v_depConfigs_4452_, v___x_4498_, v___x_4499_, v___x_4483_, v_a_4447_, v___y_4448_, v___y_4449_);
lean_dec_ref(v_depConfigs_4452_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v_fst_4502_; lean_object* v_snd_4503_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref(v___x_4500_);
v_fst_4502_ = lean_ctor_get(v_a_4501_, 0);
lean_inc(v_fst_4502_);
v_snd_4503_ = lean_ctor_get(v_a_4501_, 1);
lean_inc(v_snd_4503_);
lean_dec(v_a_4501_);
v_____x_4476_ = v_fst_4502_;
v___y_4477_ = v_snd_4503_;
v___y_4478_ = v___y_4449_;
goto v___jp_4475_;
}
else
{
lean_dec_ref(v___y_4442_);
return v___x_4500_;
}
}
}
else
{
uint8_t v___x_4504_; 
v___x_4504_ = lean_nat_dec_lt(v___x_4482_, v___x_4481_);
if (v___x_4504_ == 0)
{
lean_inc_ref(v_packages_4451_);
lean_dec_ref(v_depConfigs_4452_);
lean_dec_ref(v_pkg_4445_);
lean_dec_ref(v_leanOpts_4443_);
v_snd_4455_ = v_a_4447_;
v_packages_4456_ = v_packages_4451_;
v___y_4457_ = v___y_4448_;
v___y_4458_ = v___y_4449_;
goto v___jp_4454_;
}
else
{
size_t v___x_4505_; size_t v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = lean_usize_of_nat(v___x_4481_);
v___x_4506_ = ((size_t)0ULL);
v___x_4507_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_4445_, v_leanOpts_4443_, v_reconfigure_4444_, v_depConfigs_4452_, v___x_4505_, v___x_4506_, v___x_4483_, v_a_4447_, v___y_4448_, v___y_4449_);
lean_dec_ref(v_depConfigs_4452_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v_fst_4509_; lean_object* v_snd_4510_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref(v___x_4507_);
v_fst_4509_ = lean_ctor_get(v_a_4508_, 0);
lean_inc(v_fst_4509_);
v_snd_4510_ = lean_ctor_get(v_a_4508_, 1);
lean_inc(v_snd_4510_);
lean_dec(v_a_4508_);
v_____x_4476_ = v_fst_4509_;
v___y_4477_ = v_snd_4510_;
v___y_4478_ = v___y_4449_;
goto v___jp_4475_;
}
else
{
lean_dec_ref(v___y_4442_);
return v___x_4507_;
}
}
}
v___jp_4454_:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; uint8_t v___x_4461_; 
v___x_4459_ = lean_array_get_size(v_packages_4456_);
v___x_4460_ = lean_box(0);
v___x_4461_ = lean_nat_dec_lt(v___x_4453_, v___x_4459_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; 
lean_dec_ref(v_packages_4456_);
lean_dec_ref(v___y_4442_);
v___x_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4460_);
lean_ctor_set(v___x_4462_, 1, v_snd_4455_);
v___x_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
lean_ctor_set(v___x_4463_, 1, v___y_4457_);
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
return v___x_4464_;
}
else
{
uint8_t v___x_4465_; 
v___x_4465_ = lean_nat_dec_le(v___x_4459_, v___x_4459_);
if (v___x_4465_ == 0)
{
if (v___x_4461_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_packages_4456_);
lean_dec_ref(v___y_4442_);
v___x_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4460_);
lean_ctor_set(v___x_4466_, 1, v_snd_4455_);
v___x_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
lean_ctor_set(v___x_4467_, 1, v___y_4457_);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
else
{
size_t v___x_4469_; size_t v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = lean_usize_of_nat(v___x_4453_);
v___x_4470_ = lean_usize_of_nat(v___x_4459_);
v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(v___y_4442_, v_packages_4456_, v___x_4469_, v___x_4470_, v___x_4460_, v_a_4446_, v_snd_4455_, v___y_4457_, v___y_4458_);
lean_dec_ref(v_packages_4456_);
return v___x_4471_;
}
}
else
{
size_t v___x_4472_; size_t v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = lean_usize_of_nat(v___x_4453_);
v___x_4473_ = lean_usize_of_nat(v___x_4459_);
v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__5(v___y_4442_, v_packages_4456_, v___x_4472_, v___x_4473_, v___x_4460_, v_a_4446_, v_snd_4455_, v___y_4457_, v___y_4458_);
lean_dec_ref(v_packages_4456_);
return v___x_4474_;
}
}
}
v___jp_4475_:
{
lean_object* v_snd_4479_; lean_object* v_packages_4480_; 
v_snd_4479_ = lean_ctor_get(v_____x_4476_, 1);
lean_inc(v_snd_4479_);
lean_dec_ref(v_____x_4476_);
v_packages_4480_ = lean_ctor_get(v_snd_4479_, 5);
lean_inc_ref(v_packages_4480_);
v_snd_4455_ = v_snd_4479_;
v_packages_4456_ = v_packages_4480_;
v___y_4457_ = v___y_4477_;
v___y_4458_ = v___y_4478_;
goto v___jp_4454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v___y_4511_, lean_object* v_leanOpts_4512_, lean_object* v_reconfigure_4513_, lean_object* v_pkg_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v_reconfigure_boxed_4520_; lean_object* v_res_4521_; 
v_reconfigure_boxed_4520_ = lean_unbox(v_reconfigure_4513_);
v_res_4521_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v___y_4511_, v_leanOpts_4512_, v_reconfigure_boxed_4520_, v_pkg_4514_, v_a_4515_, v_a_4516_, v___y_4517_, v___y_4518_);
lean_dec_ref(v___y_4518_);
lean_dec(v_a_4515_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(lean_object* v_pkg_4522_, lean_object* v_leanOpts_4523_, uint8_t v_reconfigure_4524_, lean_object* v_as_4525_, size_t v_i_4526_, size_t v_stop_4527_, lean_object* v_b_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_4522_, v_leanOpts_4523_, v_reconfigure_4524_, v_as_4525_, v_i_4526_, v_stop_4527_, v_b_4528_, v___y_4530_, v___y_4531_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___boxed(lean_object* v_pkg_4535_, lean_object* v_leanOpts_4536_, lean_object* v_reconfigure_4537_, lean_object* v_as_4538_, lean_object* v_i_4539_, lean_object* v_stop_4540_, lean_object* v_b_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
uint8_t v_reconfigure_boxed_4547_; size_t v_i_boxed_4548_; size_t v_stop_boxed_4549_; lean_object* v_res_4550_; 
v_reconfigure_boxed_4547_ = lean_unbox(v_reconfigure_4537_);
v_i_boxed_4548_ = lean_unbox_usize(v_i_4539_);
lean_dec(v_i_4539_);
v_stop_boxed_4549_ = lean_unbox_usize(v_stop_4540_);
lean_dec(v_stop_4540_);
v_res_4550_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6(v_pkg_4535_, v_leanOpts_4536_, v_reconfigure_boxed_4547_, v_as_4538_, v_i_boxed_4548_, v_stop_boxed_4549_, v_b_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4542_);
lean_dec_ref(v_as_4538_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8(lean_object* v_leanOpts_4551_, lean_object* v_a_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v___x_4558_; 
v___x_4558_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg(v_leanOpts_4551_, v_a_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8___boxed(lean_object* v_leanOpts_4559_, lean_object* v_a_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8(v_leanOpts_4559_, v_a_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17(lean_object* v_00_u03b2_4567_, lean_object* v_msg_4568_){
_start:
{
lean_object* v___x_4569_; 
v___x_4569_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10_spec__17___redArg(v_msg_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10(lean_object* v_00_u03b2_4570_, lean_object* v_k_4571_, lean_object* v_v_4572_, lean_object* v_t_4573_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__10___redArg(v_k_4571_, v_v_4572_, v_t_4573_);
return v___x_4574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__11(lean_object* v_init_4575_, lean_object* v_t_4576_){
_start:
{
lean_object* v___x_4577_; 
v___x_4577_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__11_spec__19(v_init_4575_, v_t_4576_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(lean_object* v___y_4578_, lean_object* v___x_4579_, lean_object* v_as_4580_, size_t v_i_4581_, size_t v_stop_4582_, lean_object* v_b_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
uint8_t v___x_4588_; 
v___x_4588_ = lean_usize_dec_eq(v_i_4581_, v_stop_4582_);
if (v___x_4588_ == 0)
{
lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4589_ = lean_array_uget_borrowed(v_as_4580_, v_i_4581_);
lean_inc_ref(v___y_4578_);
lean_inc_ref(v___y_4586_);
lean_inc(v___x_4579_);
lean_inc(v___x_4589_);
v___x_4590_ = lean_apply_6(v___y_4578_, v___x_4589_, v___x_4579_, v___y_4584_, v___y_4585_, v___y_4586_, lean_box(0));
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v_fst_4592_; lean_object* v_snd_4593_; lean_object* v_fst_4594_; lean_object* v_snd_4595_; size_t v___x_4596_; size_t v___x_4597_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref(v___x_4590_);
v_fst_4592_ = lean_ctor_get(v_a_4591_, 0);
lean_inc(v_fst_4592_);
v_snd_4593_ = lean_ctor_get(v_a_4591_, 1);
lean_inc(v_snd_4593_);
lean_dec(v_a_4591_);
v_fst_4594_ = lean_ctor_get(v_fst_4592_, 0);
lean_inc(v_fst_4594_);
v_snd_4595_ = lean_ctor_get(v_fst_4592_, 1);
lean_inc(v_snd_4595_);
lean_dec(v_fst_4592_);
v___x_4596_ = ((size_t)1ULL);
v___x_4597_ = lean_usize_add(v_i_4581_, v___x_4596_);
v_i_4581_ = v___x_4597_;
v_b_4583_ = v_fst_4594_;
v___y_4584_ = v_snd_4595_;
v___y_4585_ = v_snd_4593_;
goto _start;
}
else
{
lean_dec(v___x_4579_);
lean_dec_ref(v___y_4578_);
return v___x_4590_;
}
}
else
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
lean_dec(v___x_4579_);
lean_dec_ref(v___y_4578_);
v___x_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4599_, 0, v_b_4583_);
lean_ctor_set(v___x_4599_, 1, v___y_4584_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
lean_ctor_set(v___x_4600_, 1, v___y_4585_);
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
return v___x_4601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg___boxed(lean_object* v___y_4602_, lean_object* v___x_4603_, lean_object* v_as_4604_, lean_object* v_i_4605_, lean_object* v_stop_4606_, lean_object* v_b_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
size_t v_i_boxed_4612_; size_t v_stop_boxed_4613_; lean_object* v_res_4614_; 
v_i_boxed_4612_ = lean_unbox_usize(v_i_4605_);
lean_dec(v_i_4605_);
v_stop_boxed_4613_ = lean_unbox_usize(v_stop_4606_);
lean_dec(v_stop_4606_);
v_res_4614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(v___y_4602_, v___x_4603_, v_as_4604_, v_i_boxed_4612_, v_stop_boxed_4613_, v_b_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec_ref(v___y_4610_);
lean_dec_ref(v_as_4604_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11(lean_object* v___y_4615_, lean_object* v___x_4616_, lean_object* v_leanOpts_4617_, uint8_t v_reconfigure_4618_, lean_object* v_pkg_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_packages_4625_; lean_object* v_depConfigs_4626_; lean_object* v___x_4627_; lean_object* v_snd_4629_; lean_object* v_packages_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v_____x_4650_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; uint8_t v___x_4658_; 
v_packages_4625_ = lean_ctor_get(v_a_4621_, 5);
v_depConfigs_4626_ = lean_ctor_get(v_pkg_4619_, 12);
lean_inc_ref(v_depConfigs_4626_);
v___x_4627_ = lean_array_get_size(v_packages_4625_);
v___x_4655_ = lean_array_get_size(v_depConfigs_4626_);
v___x_4656_ = lean_unsigned_to_nat(0u);
v___x_4657_ = lean_box(0);
v___x_4658_ = lean_nat_dec_le(v___x_4655_, v___x_4655_);
if (v___x_4658_ == 0)
{
uint8_t v___x_4659_; 
v___x_4659_ = lean_nat_dec_lt(v___x_4656_, v___x_4655_);
if (v___x_4659_ == 0)
{
uint8_t v___x_4660_; 
lean_dec_ref(v_depConfigs_4626_);
lean_dec_ref(v_pkg_4619_);
lean_dec_ref(v_leanOpts_4617_);
v___x_4660_ = lean_nat_dec_lt(v___x_4627_, v___x_4627_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
lean_dec(v___x_4616_);
lean_dec_ref(v___y_4615_);
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4657_);
lean_ctor_set(v___x_4661_, 1, v_a_4621_);
v___x_4662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4661_);
lean_ctor_set(v___x_4662_, 1, v___y_4622_);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
return v___x_4663_;
}
else
{
uint8_t v___x_4664_; 
v___x_4664_ = lean_nat_dec_le(v___x_4627_, v___x_4627_);
if (v___x_4664_ == 0)
{
if (v___x_4660_ == 0)
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
lean_dec(v___x_4616_);
lean_dec_ref(v___y_4615_);
v___x_4665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4657_);
lean_ctor_set(v___x_4665_, 1, v_a_4621_);
v___x_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
lean_ctor_set(v___x_4666_, 1, v___y_4622_);
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
return v___x_4667_;
}
else
{
size_t v___x_4668_; lean_object* v___x_4669_; 
lean_inc_ref(v_packages_4625_);
v___x_4668_ = lean_usize_of_nat(v___x_4627_);
v___x_4669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(v___y_4615_, v___x_4616_, v_packages_4625_, v___x_4668_, v___x_4668_, v___x_4657_, v_a_4621_, v___y_4622_, v___y_4623_);
lean_dec_ref(v_packages_4625_);
return v___x_4669_;
}
}
else
{
size_t v___x_4670_; lean_object* v___x_4671_; 
lean_inc_ref(v_packages_4625_);
v___x_4670_ = lean_usize_of_nat(v___x_4627_);
v___x_4671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(v___y_4615_, v___x_4616_, v_packages_4625_, v___x_4670_, v___x_4670_, v___x_4657_, v_a_4621_, v___y_4622_, v___y_4623_);
lean_dec_ref(v_packages_4625_);
return v___x_4671_;
}
}
}
else
{
size_t v___x_4672_; size_t v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = lean_usize_of_nat(v___x_4655_);
v___x_4673_ = ((size_t)0ULL);
v___x_4674_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_4619_, v_leanOpts_4617_, v_reconfigure_4618_, v_depConfigs_4626_, v___x_4672_, v___x_4673_, v___x_4657_, v_a_4621_, v___y_4622_, v___y_4623_);
lean_dec_ref(v_depConfigs_4626_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v_fst_4676_; lean_object* v_snd_4677_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref(v___x_4674_);
v_fst_4676_ = lean_ctor_get(v_a_4675_, 0);
lean_inc(v_fst_4676_);
v_snd_4677_ = lean_ctor_get(v_a_4675_, 1);
lean_inc(v_snd_4677_);
lean_dec(v_a_4675_);
v_____x_4650_ = v_fst_4676_;
v___y_4651_ = v_snd_4677_;
v___y_4652_ = v___y_4623_;
goto v___jp_4649_;
}
else
{
lean_dec(v___x_4616_);
lean_dec_ref(v___y_4615_);
return v___x_4674_;
}
}
}
else
{
uint8_t v___x_4678_; 
v___x_4678_ = lean_nat_dec_lt(v___x_4656_, v___x_4655_);
if (v___x_4678_ == 0)
{
lean_inc_ref(v_packages_4625_);
lean_dec_ref(v_depConfigs_4626_);
lean_dec_ref(v_pkg_4619_);
lean_dec_ref(v_leanOpts_4617_);
v_snd_4629_ = v_a_4621_;
v_packages_4630_ = v_packages_4625_;
v___y_4631_ = v___y_4622_;
v___y_4632_ = v___y_4623_;
goto v___jp_4628_;
}
else
{
size_t v___x_4679_; size_t v___x_4680_; lean_object* v___x_4681_; 
v___x_4679_ = lean_usize_of_nat(v___x_4655_);
v___x_4680_ = ((size_t)0ULL);
v___x_4681_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__6___redArg(v_pkg_4619_, v_leanOpts_4617_, v_reconfigure_4618_, v_depConfigs_4626_, v___x_4679_, v___x_4680_, v___x_4657_, v_a_4621_, v___y_4622_, v___y_4623_);
lean_dec_ref(v_depConfigs_4626_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v_fst_4683_; lean_object* v_snd_4684_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref(v___x_4681_);
v_fst_4683_ = lean_ctor_get(v_a_4682_, 0);
lean_inc(v_fst_4683_);
v_snd_4684_ = lean_ctor_get(v_a_4682_, 1);
lean_inc(v_snd_4684_);
lean_dec(v_a_4682_);
v_____x_4650_ = v_fst_4683_;
v___y_4651_ = v_snd_4684_;
v___y_4652_ = v___y_4623_;
goto v___jp_4649_;
}
else
{
lean_dec(v___x_4616_);
lean_dec_ref(v___y_4615_);
return v___x_4681_;
}
}
}
v___jp_4628_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; uint8_t v___x_4635_; 
v___x_4633_ = lean_array_get_size(v_packages_4630_);
v___x_4634_ = lean_box(0);
v___x_4635_ = lean_nat_dec_lt(v___x_4627_, v___x_4633_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
lean_dec_ref(v_packages_4630_);
lean_dec(v___x_4616_);
lean_dec_ref(v___y_4615_);
v___x_4636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4634_);
lean_ctor_set(v___x_4636_, 1, v_snd_4629_);
v___x_4637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
lean_ctor_set(v___x_4637_, 1, v___y_4631_);
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
else
{
uint8_t v___x_4639_; 
v___x_4639_ = lean_nat_dec_le(v___x_4633_, v___x_4633_);
if (v___x_4639_ == 0)
{
if (v___x_4635_ == 0)
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; 
lean_dec_ref(v_packages_4630_);
lean_dec(v___x_4616_);
lean_dec_ref(v___y_4615_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4634_);
lean_ctor_set(v___x_4640_, 1, v_snd_4629_);
v___x_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4640_);
lean_ctor_set(v___x_4641_, 1, v___y_4631_);
v___x_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
return v___x_4642_;
}
else
{
size_t v___x_4643_; size_t v___x_4644_; lean_object* v___x_4645_; 
v___x_4643_ = lean_usize_of_nat(v___x_4627_);
v___x_4644_ = lean_usize_of_nat(v___x_4633_);
v___x_4645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(v___y_4615_, v___x_4616_, v_packages_4630_, v___x_4643_, v___x_4644_, v___x_4634_, v_snd_4629_, v___y_4631_, v___y_4632_);
lean_dec_ref(v_packages_4630_);
return v___x_4645_;
}
}
else
{
size_t v___x_4646_; size_t v___x_4647_; lean_object* v___x_4648_; 
v___x_4646_ = lean_usize_of_nat(v___x_4627_);
v___x_4647_ = lean_usize_of_nat(v___x_4633_);
v___x_4648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(v___y_4615_, v___x_4616_, v_packages_4630_, v___x_4646_, v___x_4647_, v___x_4634_, v_snd_4629_, v___y_4631_, v___y_4632_);
lean_dec_ref(v_packages_4630_);
return v___x_4648_;
}
}
}
v___jp_4649_:
{
lean_object* v_snd_4653_; lean_object* v_packages_4654_; 
v_snd_4653_ = lean_ctor_get(v_____x_4650_, 1);
lean_inc(v_snd_4653_);
lean_dec_ref(v_____x_4650_);
v_packages_4654_ = lean_ctor_get(v_snd_4653_, 5);
lean_inc_ref(v_packages_4654_);
v_snd_4629_ = v_snd_4653_;
v_packages_4630_ = v_packages_4654_;
v___y_4631_ = v___y_4651_;
v___y_4632_ = v___y_4652_;
goto v___jp_4628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___boxed(lean_object* v___y_4685_, lean_object* v___x_4686_, lean_object* v_leanOpts_4687_, lean_object* v_reconfigure_4688_, lean_object* v_pkg_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
uint8_t v_reconfigure_boxed_4695_; lean_object* v_res_4696_; 
v_reconfigure_boxed_4695_ = lean_unbox(v_reconfigure_4688_);
v_res_4696_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11(v___y_4685_, v___x_4686_, v_leanOpts_4687_, v_reconfigure_boxed_4695_, v_pkg_4689_, v_a_4690_, v_a_4691_, v___y_4692_, v___y_4693_);
lean_dec_ref(v___y_4693_);
lean_dec(v_a_4690_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13(lean_object* v_00_u03b1_4697_, lean_object* v_cycle_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___redArg(v_cycle_4698_, v___y_4702_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03b1_4705_, lean_object* v_cycle_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13(v_00_u03b1_4705_, v_cycle_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16(lean_object* v___y_4713_, lean_object* v___x_4714_, lean_object* v_as_4715_, size_t v_i_4716_, size_t v_stop_4717_, lean_object* v_b_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v___x_4724_; 
v___x_4724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___redArg(v___y_4713_, v___x_4714_, v_as_4715_, v_i_4716_, v_stop_4717_, v_b_4718_, v___y_4720_, v___y_4721_, v___y_4722_);
return v___x_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16___boxed(lean_object* v___y_4725_, lean_object* v___x_4726_, lean_object* v_as_4727_, lean_object* v_i_4728_, lean_object* v_stop_4729_, lean_object* v_b_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
size_t v_i_boxed_4736_; size_t v_stop_boxed_4737_; lean_object* v_res_4738_; 
v_i_boxed_4736_ = lean_unbox_usize(v_i_4728_);
lean_dec(v_i_4728_);
v_stop_boxed_4737_ = lean_unbox_usize(v_stop_4729_);
lean_dec(v_stop_4729_);
v_res_4738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11_spec__16(v___y_4725_, v___x_4726_, v_as_4727_, v_i_boxed_4736_, v_stop_boxed_4737_, v_b_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
lean_dec_ref(v___y_4734_);
lean_dec(v___y_4731_);
lean_dec_ref(v_as_4727_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14(lean_object* v_leanOpts_4739_, lean_object* v_inst_4740_, lean_object* v_a_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v___x_4747_; 
v___x_4747_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg(v_leanOpts_4739_, v_a_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___boxed(lean_object* v_leanOpts_4748_, lean_object* v_inst_4749_, lean_object* v_a_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14(v_leanOpts_4748_, v_inst_4749_, v_a_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4751_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27(lean_object* v_leanOpts_4757_, lean_object* v___x_4758_, lean_object* v_as_4759_, size_t v_i_4760_, size_t v_stop_4761_, lean_object* v_b_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v___x_4768_; 
v___x_4768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___redArg(v_leanOpts_4757_, v___x_4758_, v_as_4759_, v_i_4760_, v_stop_4761_, v_b_4762_, v___y_4764_, v___y_4765_, v___y_4766_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27___boxed(lean_object* v_leanOpts_4769_, lean_object* v___x_4770_, lean_object* v_as_4771_, lean_object* v_i_4772_, lean_object* v_stop_4773_, lean_object* v_b_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
size_t v_i_boxed_4780_; size_t v_stop_boxed_4781_; lean_object* v_res_4782_; 
v_i_boxed_4780_ = lean_unbox_usize(v_i_4772_);
lean_dec(v_i_4772_);
v_stop_boxed_4781_ = lean_unbox_usize(v_stop_4773_);
lean_dec(v_stop_4773_);
v_res_4782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__11___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14_spec__26_spec__27(v_leanOpts_4769_, v___x_4770_, v_as_4771_, v_i_boxed_4780_, v_stop_boxed_4781_, v_b_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec_ref(v___y_4778_);
lean_dec(v___y_4775_);
lean_dec_ref(v_as_4771_);
lean_dec(v___x_4770_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_4783_, lean_object* v_as_4784_, size_t v_i_4785_, size_t v_stop_4786_, lean_object* v_b_4787_){
_start:
{
lean_object* v___y_4789_; uint8_t v___x_4793_; 
v___x_4793_ = lean_usize_dec_eq(v_i_4785_, v_stop_4786_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v_baseName_4795_; lean_object* v_relConfigFile_4796_; lean_object* v_relManifestFile_4797_; lean_object* v___x_4798_; 
v___x_4794_ = lean_array_uget_borrowed(v_as_4784_, v_i_4785_);
v_baseName_4795_ = lean_ctor_get(v___x_4794_, 1);
v_relConfigFile_4796_ = lean_ctor_get(v___x_4794_, 8);
v_relManifestFile_4797_ = lean_ctor_get(v___x_4794_, 9);
v___x_4798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_4783_, v_baseName_4795_);
if (lean_obj_tag(v___x_4798_) == 0)
{
v___y_4789_ = v_b_4787_;
goto v___jp_4788_;
}
else
{
lean_object* v_val_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4820_; 
v_val_4799_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4801_ = v___x_4798_;
v_isShared_4802_ = v_isSharedCheck_4820_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_val_4799_);
lean_dec(v___x_4798_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4820_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v_name_4803_; lean_object* v_scope_4804_; uint8_t v_inherited_4805_; lean_object* v_src_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4817_; 
v_name_4803_ = lean_ctor_get(v_val_4799_, 0);
v_scope_4804_ = lean_ctor_get(v_val_4799_, 1);
v_inherited_4805_ = lean_ctor_get_uint8(v_val_4799_, sizeof(void*)*5);
v_src_4806_ = lean_ctor_get(v_val_4799_, 4);
v_isSharedCheck_4817_ = !lean_is_exclusive(v_val_4799_);
if (v_isSharedCheck_4817_ == 0)
{
lean_object* v_unused_4818_; lean_object* v_unused_4819_; 
v_unused_4818_ = lean_ctor_get(v_val_4799_, 3);
lean_dec(v_unused_4818_);
v_unused_4819_ = lean_ctor_get(v_val_4799_, 2);
lean_dec(v_unused_4819_);
v___x_4808_ = v_val_4799_;
v_isShared_4809_ = v_isSharedCheck_4817_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_src_4806_);
lean_inc(v_scope_4804_);
lean_inc(v_name_4803_);
lean_dec(v_val_4799_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4817_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
lean_inc_ref(v_relManifestFile_4797_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 0, v_relManifestFile_4797_);
v___x_4811_ = v___x_4801_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_relManifestFile_4797_);
v___x_4811_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4813_; 
lean_inc_ref(v_relConfigFile_4796_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 3, v___x_4811_);
lean_ctor_set(v___x_4808_, 2, v_relConfigFile_4796_);
v___x_4813_ = v___x_4808_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_name_4803_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_scope_4804_);
lean_ctor_set(v_reuseFailAlloc_4815_, 2, v_relConfigFile_4796_);
lean_ctor_set(v_reuseFailAlloc_4815_, 3, v___x_4811_);
lean_ctor_set(v_reuseFailAlloc_4815_, 4, v_src_4806_);
lean_ctor_set_uint8(v_reuseFailAlloc_4815_, sizeof(void*)*5, v_inherited_4805_);
v___x_4813_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4814_; 
v___x_4814_ = lean_array_push(v_b_4787_, v___x_4813_);
v___y_4789_ = v___x_4814_;
goto v___jp_4788_;
}
}
}
}
}
}
else
{
return v_b_4787_;
}
v___jp_4788_:
{
size_t v___x_4790_; size_t v___x_4791_; 
v___x_4790_ = ((size_t)1ULL);
v___x_4791_ = lean_usize_add(v_i_4785_, v___x_4790_);
v_i_4785_ = v___x_4791_;
v_b_4787_ = v___y_4789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_4821_, lean_object* v_as_4822_, lean_object* v_i_4823_, lean_object* v_stop_4824_, lean_object* v_b_4825_){
_start:
{
size_t v_i_boxed_4826_; size_t v_stop_boxed_4827_; lean_object* v_res_4828_; 
v_i_boxed_4826_ = lean_unbox_usize(v_i_4823_);
lean_dec(v_i_4823_);
v_stop_boxed_4827_ = lean_unbox_usize(v_stop_4824_);
lean_dec(v_stop_4824_);
v_res_4828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4821_, v_as_4822_, v_i_boxed_4826_, v_stop_boxed_4827_, v_b_4825_);
lean_dec_ref(v_as_4822_);
lean_dec(v_entries_4821_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_4829_, lean_object* v_entries_4830_){
_start:
{
lean_object* v_root_4832_; lean_object* v_packages_4833_; lean_object* v___y_4835_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; uint8_t v___x_4851_; 
v_root_4832_ = lean_ctor_get(v_ws_4829_, 0);
lean_inc_ref(v_root_4832_);
v_packages_4833_ = lean_ctor_get(v_ws_4829_, 5);
lean_inc_ref(v_packages_4833_);
lean_dec_ref(v_ws_4829_);
v___x_4848_ = lean_unsigned_to_nat(0u);
v___x_4849_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_mkDepLoadConfig___closed__0));
v___x_4850_ = lean_array_get_size(v_packages_4833_);
v___x_4851_ = lean_nat_dec_lt(v___x_4848_, v___x_4850_);
if (v___x_4851_ == 0)
{
lean_dec_ref(v_packages_4833_);
v___y_4835_ = v___x_4849_;
goto v___jp_4834_;
}
else
{
uint8_t v___x_4852_; 
v___x_4852_ = lean_nat_dec_le(v___x_4850_, v___x_4850_);
if (v___x_4852_ == 0)
{
if (v___x_4851_ == 0)
{
lean_dec_ref(v_packages_4833_);
v___y_4835_ = v___x_4849_;
goto v___jp_4834_;
}
else
{
size_t v___x_4853_; size_t v___x_4854_; lean_object* v___x_4855_; 
v___x_4853_ = ((size_t)0ULL);
v___x_4854_ = lean_usize_of_nat(v___x_4850_);
v___x_4855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4830_, v_packages_4833_, v___x_4853_, v___x_4854_, v___x_4849_);
lean_dec_ref(v_packages_4833_);
v___y_4835_ = v___x_4855_;
goto v___jp_4834_;
}
}
else
{
size_t v___x_4856_; size_t v___x_4857_; lean_object* v___x_4858_; 
v___x_4856_ = ((size_t)0ULL);
v___x_4857_ = lean_usize_of_nat(v___x_4850_);
v___x_4858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_4830_, v_packages_4833_, v___x_4856_, v___x_4857_, v___x_4849_);
lean_dec_ref(v_packages_4833_);
v___y_4835_ = v___x_4858_;
goto v___jp_4834_;
}
}
v___jp_4834_:
{
lean_object* v_config_4836_; lean_object* v_baseName_4837_; lean_object* v_dir_4838_; lean_object* v_relManifestFile_4839_; lean_object* v_toWorkspaceConfig_4840_; uint8_t v_fixedToolchain_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v_manifest_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v_config_4836_ = lean_ctor_get(v_root_4832_, 6);
lean_inc_ref(v_config_4836_);
v_baseName_4837_ = lean_ctor_get(v_root_4832_, 1);
lean_inc(v_baseName_4837_);
v_dir_4838_ = lean_ctor_get(v_root_4832_, 4);
lean_inc_ref(v_dir_4838_);
v_relManifestFile_4839_ = lean_ctor_get(v_root_4832_, 9);
lean_inc_ref(v_relManifestFile_4839_);
lean_dec_ref(v_root_4832_);
v_toWorkspaceConfig_4840_ = lean_ctor_get(v_config_4836_, 0);
lean_inc_ref(v_toWorkspaceConfig_4840_);
v_fixedToolchain_4841_ = lean_ctor_get_uint8(v_config_4836_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_4836_);
v___x_4842_ = l_Lake_defaultLakeDir;
v___x_4843_ = l_System_FilePath_normalize(v_toWorkspaceConfig_4840_);
v___x_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
v_manifest_4845_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_4845_, 0, v_baseName_4837_);
lean_ctor_set(v_manifest_4845_, 1, v___x_4842_);
lean_ctor_set(v_manifest_4845_, 2, v___x_4844_);
lean_ctor_set(v_manifest_4845_, 3, v___y_4835_);
lean_ctor_set_uint8(v_manifest_4845_, sizeof(void*)*4, v_fixedToolchain_4841_);
v___x_4846_ = l_Lake_joinRelative(v_dir_4838_, v_relManifestFile_4839_);
v___x_4847_ = l_Lake_Manifest_save(v_manifest_4845_, v___x_4846_);
lean_dec_ref(v___x_4846_);
return v___x_4847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_4859_, lean_object* v_entries_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_4859_, v_entries_4860_);
lean_dec(v_entries_4860_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_4863_, lean_object* v_as_4864_, size_t v_i_4865_, size_t v_stop_4866_, lean_object* v_b_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v_a_4872_; lean_object* v___y_4877_; uint8_t v___x_4882_; 
v___x_4882_ = lean_usize_dec_eq(v_i_4865_, v_stop_4866_);
if (v___x_4882_ == 0)
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_9315__overap_4885_; lean_object* v___x_4886_; 
v___x_4883_ = lean_unsigned_to_nat(0u);
v___x_4884_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_9315__overap_4885_ = lean_array_uget_borrowed(v_as_4864_, v_i_4865_);
lean_inc(v___x_9315__overap_4885_);
lean_inc(v___y_4868_);
lean_inc_ref(v_pkg_4863_);
v___x_4886_ = lean_apply_4(v___x_9315__overap_4885_, v_pkg_4863_, v___y_4868_, v___x_4884_, lean_box(0));
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v_a_4888_; lean_object* v___x_4889_; uint8_t v___x_4890_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
v_a_4888_ = lean_ctor_get(v___x_4886_, 1);
lean_inc(v_a_4888_);
lean_dec_ref(v___x_4886_);
v___x_4889_ = lean_array_get_size(v_a_4888_);
v___x_4890_ = lean_nat_dec_lt(v___x_4883_, v___x_4889_);
if (v___x_4890_ == 0)
{
lean_dec(v_a_4888_);
v_a_4872_ = v_a_4887_;
goto v___jp_4871_;
}
else
{
lean_object* v___x_4891_; uint8_t v___x_4892_; 
v___x_4891_ = lean_box(0);
v___x_4892_ = lean_nat_dec_le(v___x_4889_, v___x_4889_);
if (v___x_4892_ == 0)
{
if (v___x_4890_ == 0)
{
lean_dec(v_a_4888_);
v_a_4872_ = v_a_4887_;
goto v___jp_4871_;
}
else
{
size_t v___x_4893_; size_t v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = ((size_t)0ULL);
v___x_4894_ = lean_usize_of_nat(v___x_4889_);
v___x_4895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4888_, v___x_4893_, v___x_4894_, v___x_4891_, v___y_4869_);
lean_dec(v_a_4888_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_dec_ref(v___x_4895_);
v_a_4872_ = v_a_4887_;
goto v___jp_4871_;
}
else
{
lean_dec(v_a_4887_);
v___y_4877_ = v___x_4895_;
goto v___jp_4876_;
}
}
}
else
{
size_t v___x_4896_; size_t v___x_4897_; lean_object* v___x_4898_; 
v___x_4896_ = ((size_t)0ULL);
v___x_4897_ = lean_usize_of_nat(v___x_4889_);
v___x_4898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4888_, v___x_4896_, v___x_4897_, v___x_4891_, v___y_4869_);
lean_dec(v_a_4888_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_dec_ref(v___x_4898_);
v_a_4872_ = v_a_4887_;
goto v___jp_4871_;
}
else
{
lean_dec(v_a_4887_);
v___y_4877_ = v___x_4898_;
goto v___jp_4876_;
}
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4900_; uint8_t v___x_4901_; 
v_a_4899_ = lean_ctor_get(v___x_4886_, 1);
lean_inc(v_a_4899_);
lean_dec_ref(v___x_4886_);
v___x_4900_ = lean_array_get_size(v_a_4899_);
v___x_4901_ = lean_nat_dec_lt(v___x_4883_, v___x_4900_);
if (v___x_4901_ == 0)
{
lean_object* v___x_4902_; lean_object* v___x_4903_; 
lean_dec(v_a_4899_);
lean_dec_ref(v_pkg_4863_);
v___x_4902_ = lean_box(0);
v___x_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4902_);
return v___x_4903_;
}
else
{
lean_object* v___x_4904_; uint8_t v___x_4905_; 
v___x_4904_ = lean_box(0);
v___x_4905_ = lean_nat_dec_le(v___x_4900_, v___x_4900_);
if (v___x_4905_ == 0)
{
if (v___x_4901_ == 0)
{
lean_dec(v_a_4899_);
lean_dec_ref(v_pkg_4863_);
goto v___jp_4879_;
}
else
{
size_t v___x_4906_; size_t v___x_4907_; lean_object* v___x_4908_; 
v___x_4906_ = ((size_t)0ULL);
v___x_4907_ = lean_usize_of_nat(v___x_4900_);
v___x_4908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4899_, v___x_4906_, v___x_4907_, v___x_4904_, v___y_4869_);
lean_dec(v_a_4899_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_dec_ref(v___x_4908_);
lean_dec_ref(v_pkg_4863_);
goto v___jp_4879_;
}
else
{
v___y_4877_ = v___x_4908_;
goto v___jp_4876_;
}
}
}
else
{
size_t v___x_4909_; size_t v___x_4910_; lean_object* v___x_4911_; 
v___x_4909_ = ((size_t)0ULL);
v___x_4910_ = lean_usize_of_nat(v___x_4900_);
v___x_4911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4899_, v___x_4909_, v___x_4910_, v___x_4904_, v___y_4869_);
lean_dec(v_a_4899_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_dec_ref(v___x_4911_);
lean_dec_ref(v_pkg_4863_);
goto v___jp_4879_;
}
else
{
v___y_4877_ = v___x_4911_;
goto v___jp_4876_;
}
}
}
}
}
else
{
lean_object* v___x_4912_; 
lean_dec_ref(v_pkg_4863_);
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v_b_4867_);
return v___x_4912_;
}
v___jp_4871_:
{
size_t v___x_4873_; size_t v___x_4874_; 
v___x_4873_ = ((size_t)1ULL);
v___x_4874_ = lean_usize_add(v_i_4865_, v___x_4873_);
v_i_4865_ = v___x_4874_;
v_b_4867_ = v_a_4872_;
goto _start;
}
v___jp_4876_:
{
if (lean_obj_tag(v___y_4877_) == 0)
{
lean_object* v_a_4878_; 
v_a_4878_ = lean_ctor_get(v___y_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref(v___y_4877_);
v_a_4872_ = v_a_4878_;
goto v___jp_4871_;
}
else
{
lean_dec_ref(v_pkg_4863_);
return v___y_4877_;
}
}
v___jp_4879_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4880_ = lean_box(0);
v___x_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
return v___x_4881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_4913_, lean_object* v_as_4914_, lean_object* v_i_4915_, lean_object* v_stop_4916_, lean_object* v_b_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_){
_start:
{
size_t v_i_boxed_4921_; size_t v_stop_boxed_4922_; lean_object* v_res_4923_; 
v_i_boxed_4921_ = lean_unbox_usize(v_i_4915_);
lean_dec(v_i_4915_);
v_stop_boxed_4922_ = lean_unbox_usize(v_stop_4916_);
lean_dec(v_stop_4916_);
v_res_4923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4913_, v_as_4914_, v_i_boxed_4921_, v_stop_boxed_4922_, v_b_4917_, v___y_4918_, v___y_4919_);
lean_dec_ref(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v_as_4914_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v_baseName_4929_; lean_object* v_postUpdateHooks_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; uint8_t v___x_4933_; 
v_baseName_4929_ = lean_ctor_get(v_pkg_4925_, 1);
v_postUpdateHooks_4930_ = lean_ctor_get(v_pkg_4925_, 18);
lean_inc_ref(v_postUpdateHooks_4930_);
v___x_4931_ = lean_array_get_size(v_postUpdateHooks_4930_);
v___x_4932_ = lean_unsigned_to_nat(0u);
v___x_4933_ = lean_nat_dec_eq(v___x_4931_, v___x_4932_);
if (v___x_4933_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; uint8_t v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; uint8_t v___x_4941_; 
lean_inc(v_baseName_4929_);
v___x_4934_ = l_Lean_Name_toString(v_baseName_4929_, v___x_4933_);
v___x_4935_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_4936_ = lean_string_append(v___x_4934_, v___x_4935_);
v___x_4937_ = 1;
v___x_4938_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set_uint8(v___x_4938_, sizeof(void*)*1, v___x_4937_);
lean_inc_ref(v_a_4927_);
v___x_4939_ = lean_apply_2(v_a_4927_, v___x_4938_, lean_box(0));
v___x_4940_ = lean_box(0);
v___x_4941_ = lean_nat_dec_lt(v___x_4932_, v___x_4931_);
if (v___x_4941_ == 0)
{
lean_object* v___x_4942_; 
lean_dec_ref(v_postUpdateHooks_4930_);
lean_dec_ref(v_pkg_4925_);
v___x_4942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4940_);
return v___x_4942_;
}
else
{
uint8_t v___x_4943_; 
v___x_4943_ = lean_nat_dec_le(v___x_4931_, v___x_4931_);
if (v___x_4943_ == 0)
{
if (v___x_4941_ == 0)
{
lean_object* v___x_4944_; 
lean_dec_ref(v_postUpdateHooks_4930_);
lean_dec_ref(v_pkg_4925_);
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4940_);
return v___x_4944_;
}
else
{
size_t v___x_4945_; size_t v___x_4946_; lean_object* v___x_4947_; 
v___x_4945_ = ((size_t)0ULL);
v___x_4946_ = lean_usize_of_nat(v___x_4931_);
v___x_4947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4925_, v_postUpdateHooks_4930_, v___x_4945_, v___x_4946_, v___x_4940_, v_a_4926_, v_a_4927_);
lean_dec_ref(v_postUpdateHooks_4930_);
return v___x_4947_;
}
}
else
{
size_t v___x_4948_; size_t v___x_4949_; lean_object* v___x_4950_; 
v___x_4948_ = ((size_t)0ULL);
v___x_4949_ = lean_usize_of_nat(v___x_4931_);
v___x_4950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_4925_, v_postUpdateHooks_4930_, v___x_4948_, v___x_4949_, v___x_4940_, v_a_4926_, v_a_4927_);
lean_dec_ref(v_postUpdateHooks_4930_);
return v___x_4950_;
}
}
}
else
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
lean_dec_ref(v_postUpdateHooks_4930_);
lean_dec_ref(v_pkg_4925_);
v___x_4951_ = lean_box(0);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
return v___x_4952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_4953_, v_a_4954_, v_a_4955_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_4958_, lean_object* v_ws_4959_, lean_object* v_toUpdate_4960_, lean_object* v_leanOpts_4961_, uint8_t v_updateToolchain_4962_){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4964_ = lean_box(1);
lean_inc_ref(v_ws_4959_);
v___x_4965_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__3(v_a_4958_, v_ws_4959_, v_toUpdate_4960_, v___x_4964_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref(v___x_4965_);
if (v_updateToolchain_4962_ == 0)
{
lean_object* v_snd_4967_; lean_object* v_root_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v_snd_4967_ = lean_ctor_get(v_a_4966_, 1);
lean_inc(v_snd_4967_);
lean_dec(v_a_4966_);
v_root_4968_ = lean_ctor_get(v_ws_4959_, 0);
lean_inc_ref(v_root_4968_);
v___x_4969_ = lean_box(0);
v___x_4970_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_leanOpts_4961_, v_ws_4959_, v_root_4968_, v___x_4969_, v_snd_4967_, v_a_4958_);
return v___x_4970_;
}
else
{
lean_object* v_snd_4971_; lean_object* v_root_4972_; lean_object* v_packages_4973_; lean_object* v___y_4975_; lean_object* v_fst_4976_; lean_object* v_packages_4977_; lean_object* v_snd_4978_; lean_object* v___y_4990_; lean_object* v_depConfigs_4995_; lean_object* v___x_4996_; size_t v_sz_4997_; size_t v___x_4998_; lean_object* v___x_4999_; 
v_snd_4971_ = lean_ctor_get(v_a_4966_, 1);
lean_inc(v_snd_4971_);
lean_dec(v_a_4966_);
v_root_4972_ = lean_ctor_get(v_ws_4959_, 0);
v_packages_4973_ = lean_ctor_get(v_ws_4959_, 5);
lean_inc_ref(v_packages_4973_);
v_depConfigs_4995_ = lean_ctor_get(v_root_4972_, 12);
lean_inc_ref(v_depConfigs_4995_);
v___x_4996_ = l_Array_reverse___redArg(v_depConfigs_4995_);
v_sz_4997_ = lean_array_size(v___x_4996_);
v___x_4998_ = ((size_t)0ULL);
lean_inc_ref(v___x_4996_);
lean_inc_ref(v_ws_4959_);
lean_inc_ref(v_root_4972_);
v___x_4999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_root_4972_, v_updateToolchain_4962_, v_ws_4959_, v_sz_4997_, v___x_4998_, v___x_4996_, v_snd_4971_, v_a_4958_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; lean_object* v_fst_5001_; lean_object* v_snd_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5041_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref(v___x_4999_);
v_fst_5001_ = lean_ctor_get(v_a_5000_, 0);
v_snd_5002_ = lean_ctor_get(v_a_5000_, 1);
v_isSharedCheck_5041_ = !lean_is_exclusive(v_a_5000_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5004_ = v_a_5000_;
v_isShared_5005_ = v_isSharedCheck_5041_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_snd_5002_);
lean_inc(v_fst_5001_);
lean_dec(v_a_5000_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5041_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5006_; 
lean_inc_ref(v_ws_4959_);
v___x_5006_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_a_4958_, v_ws_4959_, v_fst_5001_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5031_; 
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5031_ == 0)
{
lean_object* v_unused_5032_; 
v_unused_5032_ = lean_ctor_get(v___x_5006_, 0);
lean_dec(v_unused_5032_);
v___x_5008_ = v___x_5006_;
v_isShared_5009_ = v_isSharedCheck_5031_;
goto v_resetjp_5007_;
}
else
{
lean_dec(v___x_5006_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5031_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; 
v___x_5010_ = l_Array_zip___redArg(v___x_4996_, v_fst_5001_);
lean_dec(v_fst_5001_);
lean_dec_ref(v___x_4996_);
v___x_5011_ = lean_unsigned_to_nat(0u);
v___x_5012_ = lean_array_get_size(v___x_5010_);
v___x_5013_ = lean_nat_dec_lt(v___x_5011_, v___x_5012_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5015_; 
lean_dec_ref(v___x_5010_);
lean_inc(v_snd_5002_);
lean_inc_ref(v_ws_4959_);
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v_ws_4959_);
v___x_5015_ = v___x_5004_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_ws_4959_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v_snd_5002_);
v___x_5015_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
lean_object* v___x_5017_; 
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5015_);
v___x_5017_ = v___x_5008_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
lean_inc_ref(v_packages_4973_);
v___y_4975_ = v___x_5017_;
v_fst_4976_ = v_ws_4959_;
v_packages_4977_ = v_packages_4973_;
v_snd_4978_ = v_snd_5002_;
goto v___jp_4974_;
}
}
}
else
{
uint8_t v___x_5020_; 
v___x_5020_ = lean_nat_dec_le(v___x_5012_, v___x_5012_);
if (v___x_5020_ == 0)
{
if (v___x_5013_ == 0)
{
lean_object* v___x_5022_; 
lean_dec_ref(v___x_5010_);
lean_inc(v_snd_5002_);
lean_inc_ref(v_ws_4959_);
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v_ws_4959_);
v___x_5022_ = v___x_5004_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_ws_4959_);
lean_ctor_set(v_reuseFailAlloc_5026_, 1, v_snd_5002_);
v___x_5022_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
lean_object* v___x_5024_; 
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5022_);
v___x_5024_ = v___x_5008_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
lean_inc_ref(v_packages_4973_);
v___y_4975_ = v___x_5024_;
v_fst_4976_ = v_ws_4959_;
v_packages_4977_ = v_packages_4973_;
v_snd_4978_ = v_snd_5002_;
goto v___jp_4974_;
}
}
}
else
{
size_t v___x_5027_; lean_object* v___x_5028_; 
lean_del_object(v___x_5008_);
lean_del_object(v___x_5004_);
v___x_5027_ = lean_usize_of_nat(v___x_5012_);
lean_inc_ref(v_leanOpts_4961_);
v___x_5028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(v_leanOpts_4961_, v___x_5010_, v___x_4998_, v___x_5027_, v_ws_4959_, v_snd_5002_, v_a_4958_);
lean_dec_ref(v___x_5010_);
v___y_4990_ = v___x_5028_;
goto v___jp_4989_;
}
}
else
{
size_t v___x_5029_; lean_object* v___x_5030_; 
lean_del_object(v___x_5008_);
lean_del_object(v___x_5004_);
v___x_5029_ = lean_usize_of_nat(v___x_5012_);
lean_inc_ref(v_leanOpts_4961_);
v___x_5030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(v_leanOpts_4961_, v___x_5010_, v___x_4998_, v___x_5029_, v_ws_4959_, v_snd_5002_, v_a_4958_);
lean_dec_ref(v___x_5010_);
v___y_4990_ = v___x_5030_;
goto v___jp_4989_;
}
}
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
lean_del_object(v___x_5004_);
lean_dec(v_snd_5002_);
lean_dec(v_fst_5001_);
lean_dec_ref(v___x_4996_);
lean_dec_ref(v_packages_4973_);
lean_dec_ref(v_leanOpts_4961_);
lean_dec_ref(v_ws_4959_);
v_a_5033_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5006_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5006_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
else
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
lean_dec_ref(v___x_4996_);
lean_dec_ref(v_packages_4973_);
lean_dec_ref(v_leanOpts_4961_);
lean_dec_ref(v_ws_4959_);
v_a_5042_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_4999_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_4999_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
v___jp_4974_:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; uint8_t v___x_4981_; 
v___x_4979_ = lean_array_get_size(v_packages_4973_);
lean_dec_ref(v_packages_4973_);
v___x_4980_ = lean_array_get_size(v_packages_4977_);
v___x_4981_ = lean_nat_dec_lt(v___x_4979_, v___x_4980_);
if (v___x_4981_ == 0)
{
lean_dec(v_snd_4978_);
lean_dec_ref(v_packages_4977_);
lean_dec_ref(v_fst_4976_);
lean_dec_ref(v_leanOpts_4961_);
return v___y_4975_;
}
else
{
uint8_t v___x_4982_; 
v___x_4982_ = lean_nat_dec_le(v___x_4980_, v___x_4980_);
if (v___x_4982_ == 0)
{
if (v___x_4981_ == 0)
{
lean_dec(v_snd_4978_);
lean_dec_ref(v_packages_4977_);
lean_dec_ref(v_fst_4976_);
lean_dec_ref(v_leanOpts_4961_);
return v___y_4975_;
}
else
{
size_t v___x_4983_; size_t v___x_4984_; lean_object* v___x_4985_; 
lean_dec_ref(v___y_4975_);
v___x_4983_ = lean_usize_of_nat(v___x_4979_);
v___x_4984_ = lean_usize_of_nat(v___x_4980_);
v___x_4985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_leanOpts_4961_, v_packages_4977_, v___x_4983_, v___x_4984_, v_fst_4976_, v_snd_4978_, v_a_4958_);
lean_dec_ref(v_packages_4977_);
return v___x_4985_;
}
}
else
{
size_t v___x_4986_; size_t v___x_4987_; lean_object* v___x_4988_; 
lean_dec_ref(v___y_4975_);
v___x_4986_ = lean_usize_of_nat(v___x_4979_);
v___x_4987_ = lean_usize_of_nat(v___x_4980_);
v___x_4988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_leanOpts_4961_, v_packages_4977_, v___x_4986_, v___x_4987_, v_fst_4976_, v_snd_4978_, v_a_4958_);
lean_dec_ref(v_packages_4977_);
return v___x_4988_;
}
}
}
v___jp_4989_:
{
if (lean_obj_tag(v___y_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v_fst_4992_; lean_object* v_snd_4993_; lean_object* v_packages_4994_; 
v_a_4991_ = lean_ctor_get(v___y_4990_, 0);
v_fst_4992_ = lean_ctor_get(v_a_4991_, 0);
lean_inc(v_fst_4992_);
v_snd_4993_ = lean_ctor_get(v_a_4991_, 1);
lean_inc(v_snd_4993_);
v_packages_4994_ = lean_ctor_get(v_fst_4992_, 5);
lean_inc_ref(v_packages_4994_);
v___y_4975_ = v___y_4990_;
v_fst_4976_ = v_fst_4992_;
v_packages_4977_ = v_packages_4994_;
v_snd_4978_ = v_snd_4993_;
goto v___jp_4974_;
}
else
{
lean_dec_ref(v_packages_4973_);
lean_dec_ref(v_leanOpts_4961_);
return v___y_4990_;
}
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_dec_ref(v_leanOpts_4961_);
lean_dec_ref(v_ws_4959_);
v_a_5050_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_4965_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_4965_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_5058_, lean_object* v_ws_5059_, lean_object* v_toUpdate_5060_, lean_object* v_leanOpts_5061_, lean_object* v_updateToolchain_5062_, lean_object* v_a_5063_){
_start:
{
uint8_t v_updateToolchain_boxed_5064_; lean_object* v_res_5065_; 
v_updateToolchain_boxed_5064_ = lean_unbox(v_updateToolchain_5062_);
v_res_5065_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_5058_, v_ws_5059_, v_toUpdate_5060_, v_leanOpts_5061_, v_updateToolchain_boxed_5064_);
lean_dec(v_toUpdate_5060_);
lean_dec_ref(v_a_5058_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_5066_, size_t v_i_5067_, size_t v_stop_5068_, lean_object* v_b_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_){
_start:
{
uint8_t v___x_5073_; 
v___x_5073_ = lean_usize_dec_eq(v_i_5067_, v_stop_5068_);
if (v___x_5073_ == 0)
{
lean_object* v___x_5074_; lean_object* v___x_5075_; 
v___x_5074_ = lean_array_uget_borrowed(v_as_5066_, v_i_5067_);
lean_inc(v___x_5074_);
v___x_5075_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_5074_, v___y_5070_, v___y_5071_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v_a_5076_; size_t v___x_5077_; size_t v___x_5078_; 
v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_a_5076_);
lean_dec_ref(v___x_5075_);
v___x_5077_ = ((size_t)1ULL);
v___x_5078_ = lean_usize_add(v_i_5067_, v___x_5077_);
v_i_5067_ = v___x_5078_;
v_b_5069_ = v_a_5076_;
goto _start;
}
else
{
return v___x_5075_;
}
}
else
{
lean_object* v___x_5080_; 
v___x_5080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5080_, 0, v_b_5069_);
return v___x_5080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_5081_, lean_object* v_i_5082_, lean_object* v_stop_5083_, lean_object* v_b_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
size_t v_i_boxed_5088_; size_t v_stop_boxed_5089_; lean_object* v_res_5090_; 
v_i_boxed_5088_ = lean_unbox_usize(v_i_5082_);
lean_dec(v_i_5082_);
v_stop_boxed_5089_ = lean_unbox_usize(v_stop_5083_);
lean_dec(v_stop_5083_);
v_res_5090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_5081_, v_i_boxed_5088_, v_stop_boxed_5089_, v_b_5084_, v___y_5085_, v___y_5086_);
lean_dec_ref(v___y_5086_);
lean_dec(v___y_5085_);
lean_dec_ref(v_as_5081_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_5091_, lean_object* v_toUpdate_5092_, lean_object* v_leanOpts_5093_, uint8_t v_updateToolchain_5094_, lean_object* v_a_5095_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_5095_, v_ws_5091_, v_toUpdate_5092_, v_leanOpts_5093_, v_updateToolchain_5094_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; lean_object* v_fst_5099_; lean_object* v_snd_5100_; lean_object* v___y_5102_; lean_object* v___x_5119_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref(v___x_5097_);
v_fst_5099_ = lean_ctor_get(v_a_5098_, 0);
lean_inc_n(v_fst_5099_, 2);
v_snd_5100_ = lean_ctor_get(v_a_5098_, 1);
lean_inc(v_snd_5100_);
lean_dec(v_a_5098_);
v___x_5119_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_5099_, v_snd_5100_);
lean_dec(v_snd_5100_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5141_; 
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5141_ == 0)
{
lean_object* v_unused_5142_; 
v_unused_5142_ = lean_ctor_get(v___x_5119_, 0);
lean_dec(v_unused_5142_);
v___x_5121_ = v___x_5119_;
v_isShared_5122_ = v_isSharedCheck_5141_;
goto v_resetjp_5120_;
}
else
{
lean_dec(v___x_5119_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5141_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v_packages_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; uint8_t v___x_5126_; 
v_packages_5123_ = lean_ctor_get(v_fst_5099_, 5);
v___x_5124_ = lean_unsigned_to_nat(0u);
v___x_5125_ = lean_array_get_size(v_packages_5123_);
v___x_5126_ = lean_nat_dec_lt(v___x_5124_, v___x_5125_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5128_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 0, v_fst_5099_);
v___x_5128_ = v___x_5121_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_fst_5099_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
else
{
lean_object* v___x_5130_; uint8_t v___x_5131_; 
v___x_5130_ = lean_box(0);
v___x_5131_ = lean_nat_dec_le(v___x_5125_, v___x_5125_);
if (v___x_5131_ == 0)
{
if (v___x_5126_ == 0)
{
lean_object* v___x_5133_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 0, v_fst_5099_);
v___x_5133_ = v___x_5121_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_fst_5099_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
else
{
size_t v___x_5135_; size_t v___x_5136_; lean_object* v___x_5137_; 
lean_del_object(v___x_5121_);
v___x_5135_ = ((size_t)0ULL);
v___x_5136_ = lean_usize_of_nat(v___x_5125_);
v___x_5137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_5123_, v___x_5135_, v___x_5136_, v___x_5130_, v_fst_5099_, v_a_5095_);
v___y_5102_ = v___x_5137_;
goto v___jp_5101_;
}
}
else
{
size_t v___x_5138_; size_t v___x_5139_; lean_object* v___x_5140_; 
lean_del_object(v___x_5121_);
v___x_5138_ = ((size_t)0ULL);
v___x_5139_ = lean_usize_of_nat(v___x_5125_);
v___x_5140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_5123_, v___x_5138_, v___x_5139_, v___x_5130_, v_fst_5099_, v_a_5095_);
v___y_5102_ = v___x_5140_;
goto v___jp_5101_;
}
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5155_; 
lean_dec(v_fst_5099_);
v_a_5143_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5145_ = v___x_5119_;
v_isShared_5146_ = v_isSharedCheck_5155_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5119_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5155_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5147_; uint8_t v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5153_; 
v___x_5147_ = lean_io_error_to_string(v_a_5143_);
v___x_5148_ = 3;
v___x_5149_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5149_, 0, v___x_5147_);
lean_ctor_set_uint8(v___x_5149_, sizeof(void*)*1, v___x_5148_);
lean_inc_ref(v_a_5095_);
v___x_5150_ = lean_apply_2(v_a_5095_, v___x_5149_, lean_box(0));
v___x_5151_ = lean_box(0);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 0, v___x_5151_);
v___x_5153_ = v___x_5145_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5151_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
v___jp_5101_:
{
if (lean_obj_tag(v___y_5102_) == 0)
{
lean_object* v___x_5104_; uint8_t v_isShared_5105_; uint8_t v_isSharedCheck_5109_; 
v_isSharedCheck_5109_ = !lean_is_exclusive(v___y_5102_);
if (v_isSharedCheck_5109_ == 0)
{
lean_object* v_unused_5110_; 
v_unused_5110_ = lean_ctor_get(v___y_5102_, 0);
lean_dec(v_unused_5110_);
v___x_5104_ = v___y_5102_;
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
else
{
lean_dec(v___y_5102_);
v___x_5104_ = lean_box(0);
v_isShared_5105_ = v_isSharedCheck_5109_;
goto v_resetjp_5103_;
}
v_resetjp_5103_:
{
lean_object* v___x_5107_; 
if (v_isShared_5105_ == 0)
{
lean_ctor_set(v___x_5104_, 0, v_fst_5099_);
v___x_5107_ = v___x_5104_;
goto v_reusejp_5106_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_fst_5099_);
v___x_5107_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5106_;
}
v_reusejp_5106_:
{
return v___x_5107_;
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec(v_fst_5099_);
v_a_5111_ = lean_ctor_get(v___y_5102_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___y_5102_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___y_5102_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___y_5102_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
v_a_5156_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5097_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5097_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_5164_, lean_object* v_toUpdate_5165_, lean_object* v_leanOpts_5166_, lean_object* v_updateToolchain_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_){
_start:
{
uint8_t v_updateToolchain_boxed_5170_; lean_object* v_res_5171_; 
v_updateToolchain_boxed_5170_ = lean_unbox(v_updateToolchain_5167_);
v_res_5171_ = l_Lake_Workspace_updateAndMaterialize(v_ws_5164_, v_toUpdate_5165_, v_leanOpts_5166_, v_updateToolchain_boxed_5170_, v_a_5168_);
lean_dec_ref(v_a_5168_);
lean_dec(v_toUpdate_5165_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_5176_, lean_object* v_what_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v_name_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; uint8_t v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; uint8_t v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v_name_5180_ = lean_ctor_get(v___x_5176_, 0);
lean_inc(v_name_5180_);
lean_dec_ref(v___x_5176_);
v___x_5181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_5182_ = lean_string_append(v___x_5181_, v_what_5177_);
v___x_5183_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_5184_ = lean_string_append(v___x_5182_, v___x_5183_);
v___x_5185_ = 1;
v___x_5186_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5180_, v___x_5185_);
v___x_5187_ = lean_string_append(v___x_5184_, v___x_5186_);
v___x_5188_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_5189_ = lean_string_append(v___x_5187_, v___x_5188_);
v___x_5190_ = lean_string_append(v___x_5189_, v___x_5186_);
lean_dec_ref(v___x_5186_);
v___x_5191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_5192_ = lean_string_append(v___x_5190_, v___x_5191_);
v___x_5193_ = 2;
v___x_5194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5194_, 0, v___x_5192_);
lean_ctor_set_uint8(v___x_5194_, sizeof(void*)*1, v___x_5193_);
lean_inc_ref(v___y_5178_);
v___x_5195_ = lean_apply_2(v___y_5178_, v___x_5194_, lean_box(0));
v___x_5196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5195_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_5197_, lean_object* v_what_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5197_, v_what_5198_, v___y_5199_);
lean_dec_ref(v___y_5199_);
lean_dec_ref(v_what_5198_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_5205_, lean_object* v_as_5206_, size_t v_i_5207_, size_t v_stop_5208_, lean_object* v_b_5209_, lean_object* v___y_5210_){
_start:
{
lean_object* v_a_5213_; lean_object* v___y_5218_; uint8_t v___x_5220_; 
v___x_5220_ = lean_usize_dec_eq(v_i_5207_, v_stop_5208_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; lean_object* v_src_x3f_5222_; 
v___x_5221_ = lean_array_uget_borrowed(v_as_5206_, v_i_5207_);
v_src_x3f_5222_ = lean_ctor_get(v___x_5221_, 3);
if (lean_obj_tag(v_src_x3f_5222_) == 1)
{
lean_object* v_name_5223_; lean_object* v_val_5224_; lean_object* v___x_5225_; 
v_name_5223_ = lean_ctor_get(v___x_5221_, 0);
v_val_5224_ = lean_ctor_get(v_src_x3f_5222_, 0);
v___x_5225_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_5205_, v_name_5223_);
if (lean_obj_tag(v___x_5225_) == 1)
{
lean_object* v_val_5226_; lean_object* v___y_5228_; lean_object* v___y_5232_; 
v_val_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_val_5226_);
lean_dec_ref(v___x_5225_);
if (lean_obj_tag(v_val_5224_) == 0)
{
lean_object* v_src_5235_; 
v_src_5235_ = lean_ctor_get(v_val_5226_, 4);
lean_inc_ref(v_src_5235_);
lean_dec(v_val_5226_);
if (lean_obj_tag(v_src_5235_) == 0)
{
lean_object* v___x_5236_; 
lean_dec_ref(v_src_5235_);
v___x_5236_ = lean_box(0);
v_a_5213_ = v___x_5236_;
goto v___jp_5212_;
}
else
{
lean_dec_ref(v_src_5235_);
v___y_5232_ = v___y_5210_;
goto v___jp_5231_;
}
}
else
{
lean_object* v_src_5237_; 
v_src_5237_ = lean_ctor_get(v_val_5226_, 4);
lean_inc_ref(v_src_5237_);
lean_dec(v_val_5226_);
if (lean_obj_tag(v_src_5237_) == 1)
{
lean_object* v_url_5238_; lean_object* v_rev_5239_; lean_object* v_url_5240_; lean_object* v_inputRev_x3f_5241_; lean_object* v___y_5243_; uint8_t v___x_5250_; 
v_url_5238_ = lean_ctor_get(v_val_5224_, 0);
v_rev_5239_ = lean_ctor_get(v_val_5224_, 1);
v_url_5240_ = lean_ctor_get(v_src_5237_, 0);
lean_inc_ref(v_url_5240_);
v_inputRev_x3f_5241_ = lean_ctor_get(v_src_5237_, 2);
lean_inc(v_inputRev_x3f_5241_);
lean_dec_ref(v_src_5237_);
v___x_5250_ = lean_string_dec_eq(v_url_5238_, v_url_5240_);
lean_dec_ref(v_url_5240_);
if (v___x_5250_ == 0)
{
goto v___jp_5247_;
}
else
{
if (v___x_5220_ == 0)
{
v___y_5243_ = v___y_5210_;
goto v___jp_5242_;
}
else
{
goto v___jp_5247_;
}
}
v___jp_5242_:
{
lean_object* v___x_5244_; uint8_t v___x_5245_; 
v___x_5244_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_5239_);
v___x_5245_ = l_Option_instDecidableEq___redArg(v___x_5244_, v_rev_5239_, v_inputRev_x3f_5241_);
if (v___x_5245_ == 0)
{
v___y_5228_ = v___y_5243_;
goto v___jp_5227_;
}
else
{
if (v___x_5220_ == 0)
{
lean_object* v___x_5246_; 
v___x_5246_ = lean_box(0);
v_a_5213_ = v___x_5246_;
goto v___jp_5212_;
}
else
{
v___y_5228_ = v___y_5243_;
goto v___jp_5227_;
}
}
}
v___jp_5247_:
{
lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_5221_);
v___x_5249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5221_, v___x_5248_, v___y_5210_);
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_dec_ref(v___x_5249_);
v___y_5243_ = v___y_5210_;
goto v___jp_5242_;
}
else
{
lean_dec(v_inputRev_x3f_5241_);
return v___x_5249_;
}
}
}
else
{
lean_dec_ref(v_src_5237_);
v___y_5232_ = v___y_5210_;
goto v___jp_5231_;
}
}
v___jp_5227_:
{
lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_5221_);
v___x_5230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5221_, v___x_5229_, v___y_5228_);
v___y_5218_ = v___x_5230_;
goto v___jp_5217_;
}
v___jp_5231_:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; 
v___x_5233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_5221_);
v___x_5234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5221_, v___x_5233_, v___y_5232_);
v___y_5218_ = v___x_5234_;
goto v___jp_5217_;
}
}
else
{
lean_object* v___x_5251_; 
lean_dec(v___x_5225_);
v___x_5251_ = lean_box(0);
v_a_5213_ = v___x_5251_;
goto v___jp_5212_;
}
}
else
{
lean_object* v___x_5252_; 
v___x_5252_ = lean_box(0);
v_a_5213_ = v___x_5252_;
goto v___jp_5212_;
}
}
else
{
lean_object* v___x_5253_; 
v___x_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5253_, 0, v_b_5209_);
return v___x_5253_;
}
v___jp_5212_:
{
size_t v___x_5214_; size_t v___x_5215_; 
v___x_5214_ = ((size_t)1ULL);
v___x_5215_ = lean_usize_add(v_i_5207_, v___x_5214_);
v_i_5207_ = v___x_5215_;
v_b_5209_ = v_a_5213_;
goto _start;
}
v___jp_5217_:
{
if (lean_obj_tag(v___y_5218_) == 0)
{
lean_object* v_a_5219_; 
v_a_5219_ = lean_ctor_get(v___y_5218_, 0);
lean_inc(v_a_5219_);
lean_dec_ref(v___y_5218_);
v_a_5213_ = v_a_5219_;
goto v___jp_5212_;
}
else
{
return v___y_5218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_5254_, lean_object* v_as_5255_, lean_object* v_i_5256_, lean_object* v_stop_5257_, lean_object* v_b_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
size_t v_i_boxed_5261_; size_t v_stop_boxed_5262_; lean_object* v_res_5263_; 
v_i_boxed_5261_ = lean_unbox_usize(v_i_5256_);
lean_dec(v_i_5256_);
v_stop_boxed_5262_ = lean_unbox_usize(v_stop_5257_);
lean_dec(v_stop_5257_);
v_res_5263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5254_, v_as_5255_, v_i_boxed_5261_, v_stop_boxed_5262_, v_b_5258_, v___y_5259_);
lean_dec_ref(v___y_5259_);
lean_dec_ref(v_as_5255_);
lean_dec(v_pkgEntries_5254_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_5264_, lean_object* v_deps_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; uint8_t v___x_5271_; 
v___x_5268_ = lean_unsigned_to_nat(0u);
v___x_5269_ = lean_array_get_size(v_deps_5265_);
v___x_5270_ = lean_box(0);
v___x_5271_ = lean_nat_dec_lt(v___x_5268_, v___x_5269_);
if (v___x_5271_ == 0)
{
lean_object* v___x_5272_; 
v___x_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5270_);
return v___x_5272_;
}
else
{
uint8_t v___x_5273_; 
v___x_5273_ = lean_nat_dec_le(v___x_5269_, v___x_5269_);
if (v___x_5273_ == 0)
{
if (v___x_5271_ == 0)
{
lean_object* v___x_5274_; 
v___x_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5270_);
return v___x_5274_;
}
else
{
size_t v___x_5275_; size_t v___x_5276_; lean_object* v___x_5277_; 
v___x_5275_ = ((size_t)0ULL);
v___x_5276_ = lean_usize_of_nat(v___x_5269_);
v___x_5277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5264_, v_deps_5265_, v___x_5275_, v___x_5276_, v___x_5270_, v_a_5266_);
return v___x_5277_;
}
}
else
{
size_t v___x_5278_; size_t v___x_5279_; lean_object* v___x_5280_; 
v___x_5278_ = ((size_t)0ULL);
v___x_5279_ = lean_usize_of_nat(v___x_5269_);
v___x_5280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5264_, v_deps_5265_, v___x_5278_, v___x_5279_, v___x_5270_, v_a_5266_);
return v___x_5280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5281_, lean_object* v_deps_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5281_, v_deps_5282_, v_a_5283_);
lean_dec_ref(v_a_5283_);
lean_dec_ref(v_deps_5282_);
lean_dec(v_pkgEntries_5281_);
return v_res_5285_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3(lean_object* v_x_5286_, lean_object* v_x_5287_){
_start:
{
if (lean_obj_tag(v_x_5286_) == 0)
{
if (lean_obj_tag(v_x_5287_) == 0)
{
uint8_t v___x_5288_; 
v___x_5288_ = 1;
return v___x_5288_;
}
else
{
uint8_t v___x_5289_; 
v___x_5289_ = 0;
return v___x_5289_;
}
}
else
{
if (lean_obj_tag(v_x_5287_) == 0)
{
uint8_t v___x_5290_; 
v___x_5290_ = 0;
return v___x_5290_;
}
else
{
lean_object* v_val_5291_; lean_object* v_val_5292_; uint8_t v___x_5293_; 
v_val_5291_ = lean_ctor_get(v_x_5286_, 0);
v_val_5292_ = lean_ctor_get(v_x_5287_, 0);
v___x_5293_ = lean_string_dec_eq(v_val_5291_, v_val_5292_);
return v___x_5293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3___boxed(lean_object* v_x_5294_, lean_object* v_x_5295_){
_start:
{
uint8_t v_res_5296_; lean_object* v_r_5297_; 
v_res_5296_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3(v_x_5294_, v_x_5295_);
lean_dec(v_x_5295_);
lean_dec(v_x_5294_);
v_r_5297_ = lean_box(v_res_5296_);
return v_r_5297_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(lean_object* v_cycle_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; uint8_t v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v___x_5301_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1));
v___x_5302_ = l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__13_spec__19(v_cycle_5298_);
v___x_5303_ = lean_string_append(v___x_5301_, v___x_5302_);
lean_dec_ref(v___x_5302_);
v___x_5304_ = 3;
v___x_5305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5305_, 0, v___x_5303_);
lean_ctor_set_uint8(v___x_5305_, sizeof(void*)*1, v___x_5304_);
lean_inc_ref(v___y_5299_);
v___x_5306_ = lean_apply_2(v___y_5299_, v___x_5305_, lean_box(0));
v___x_5307_ = lean_box(0);
v___x_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_cycle_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(v_cycle_5309_, v___y_5310_);
lean_dec_ref(v___y_5310_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(lean_object* v_pkg_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v_leanOpts_5321_, uint8_t v_reconfigure_5322_, lean_object* v_as_5323_, size_t v_i_5324_, size_t v_stop_5325_, lean_object* v_b_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_){
_start:
{
uint8_t v___x_5330_; 
v___x_5330_ = lean_usize_dec_eq(v_i_5324_, v_stop_5325_);
if (v___x_5330_ == 0)
{
lean_object* v_root_5331_; lean_object* v_lakeEnv_5332_; lean_object* v_packages_5333_; size_t v___x_5334_; size_t v___x_5335_; lean_object* v___y_5337_; lean_object* v_fst_5338_; lean_object* v___x_5341_; uint8_t v___y_5343_; lean_object* v___x_5483_; lean_object* v___x_5484_; uint8_t v___x_5485_; 
v_root_5331_ = lean_ctor_get(v___y_5327_, 0);
v_lakeEnv_5332_ = lean_ctor_get(v___y_5327_, 1);
v_packages_5333_ = lean_ctor_get(v___y_5327_, 5);
v___x_5334_ = ((size_t)1ULL);
v___x_5335_ = lean_usize_sub(v_i_5324_, v___x_5334_);
v___x_5341_ = lean_array_uget_borrowed(v_as_5323_, v___x_5335_);
v___x_5483_ = lean_unsigned_to_nat(0u);
v___x_5484_ = lean_array_get_size(v_packages_5333_);
v___x_5485_ = lean_nat_dec_lt(v___x_5483_, v___x_5484_);
if (v___x_5485_ == 0)
{
v___y_5343_ = v___x_5330_;
goto v___jp_5342_;
}
else
{
if (v___x_5485_ == 0)
{
v___y_5343_ = v___x_5330_;
goto v___jp_5342_;
}
else
{
size_t v___x_5486_; size_t v___x_5487_; uint8_t v___x_5488_; 
v___x_5486_ = ((size_t)0ULL);
v___x_5487_ = lean_usize_of_nat(v___x_5484_);
v___x_5488_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4_spec__4(v___x_5341_, v_packages_5333_, v___x_5486_, v___x_5487_);
if (v___x_5488_ == 0)
{
v___y_5343_ = v___x_5488_;
goto v___jp_5342_;
}
else
{
lean_object* v___x_5489_; 
v___x_5489_ = lean_box(0);
v_i_5324_ = v___x_5335_;
v_b_5326_ = v___x_5489_;
goto _start;
}
}
}
v___jp_5336_:
{
lean_object* v_snd_5339_; 
v_snd_5339_ = lean_ctor_get(v_fst_5338_, 1);
lean_inc(v_snd_5339_);
lean_dec_ref(v_fst_5338_);
v_i_5324_ = v___x_5335_;
v_b_5326_ = v___y_5337_;
v___y_5327_ = v_snd_5339_;
goto _start;
}
v___jp_5342_:
{
lean_object* v_wsIdx_5344_; lean_object* v_baseName_5345_; lean_object* v_name_5346_; lean_object* v_opts_5347_; uint8_t v___x_5348_; 
v_wsIdx_5344_ = lean_ctor_get(v_pkg_5318_, 0);
v_baseName_5345_ = lean_ctor_get(v_pkg_5318_, 1);
v_name_5346_ = lean_ctor_get(v___x_5341_, 0);
v_opts_5347_ = lean_ctor_get(v___x_5341_, 4);
v___x_5348_ = lean_name_eq(v_baseName_5345_, v_name_5346_);
if (v___x_5348_ == 0)
{
lean_object* v___x_5349_; 
v___x_5349_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5319_, v_name_5346_);
if (lean_obj_tag(v___x_5349_) == 1)
{
lean_object* v_val_5350_; lean_object* v_dir_5351_; lean_object* v___x_5352_; 
v_val_5350_ = lean_ctor_get(v___x_5349_, 0);
lean_inc(v_val_5350_);
lean_dec_ref(v___x_5349_);
v_dir_5351_ = lean_ctor_get(v_root_5331_, 4);
lean_inc_ref(v___y_5320_);
lean_inc_ref(v_dir_5351_);
v___x_5352_ = l_Lake_PackageEntry_materialize(v_val_5350_, v_lakeEnv_5332_, v_dir_5351_, v___y_5320_, v___y_5328_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5436_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5355_ = v___x_5352_;
v_isShared_5356_ = v_isSharedCheck_5436_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5352_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5436_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; 
v___x_5357_ = lean_unsigned_to_nat(0u);
v___x_5358_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5321_);
lean_inc(v_opts_5347_);
v___x_5359_ = l___private_Lake_Load_Resolve_0__Lake_addDepPackage(v_a_5353_, v_opts_5347_, v_leanOpts_5321_, v_reconfigure_5322_, v___y_5327_, v___x_5358_);
v___x_5360_ = lean_box(0);
if (lean_obj_tag(v___x_5359_) == 0)
{
lean_object* v_a_5361_; lean_object* v_a_5362_; lean_object* v___x_5363_; uint8_t v___x_5364_; 
lean_del_object(v___x_5355_);
v_a_5361_ = lean_ctor_get(v___x_5359_, 0);
lean_inc(v_a_5361_);
v_a_5362_ = lean_ctor_get(v___x_5359_, 1);
lean_inc(v_a_5362_);
lean_dec_ref(v___x_5359_);
v___x_5363_ = lean_array_get_size(v_a_5362_);
v___x_5364_ = lean_nat_dec_lt(v___x_5357_, v___x_5363_);
if (v___x_5364_ == 0)
{
lean_dec(v_a_5362_);
v___y_5337_ = v___x_5360_;
v_fst_5338_ = v_a_5361_;
goto v___jp_5336_;
}
else
{
uint8_t v___x_5365_; 
v___x_5365_ = lean_nat_dec_le(v___x_5363_, v___x_5363_);
if (v___x_5365_ == 0)
{
if (v___x_5364_ == 0)
{
lean_dec(v_a_5362_);
v___y_5337_ = v___x_5360_;
v_fst_5338_ = v_a_5361_;
goto v___jp_5336_;
}
else
{
size_t v___x_5366_; size_t v___x_5367_; lean_object* v___x_5368_; 
v___x_5366_ = ((size_t)0ULL);
v___x_5367_ = lean_usize_of_nat(v___x_5363_);
v___x_5368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5362_, v___x_5366_, v___x_5367_, v___x_5360_, v___y_5328_);
lean_dec(v_a_5362_);
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_dec_ref(v___x_5368_);
v___y_5337_ = v___x_5360_;
v_fst_5338_ = v_a_5361_;
goto v___jp_5336_;
}
else
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
lean_dec(v_a_5361_);
lean_dec_ref(v_leanOpts_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_pkg_5318_);
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v___x_5368_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5368_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
}
else
{
size_t v___x_5377_; size_t v___x_5378_; lean_object* v___x_5379_; 
v___x_5377_ = ((size_t)0ULL);
v___x_5378_ = lean_usize_of_nat(v___x_5363_);
v___x_5379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5362_, v___x_5377_, v___x_5378_, v___x_5360_, v___y_5328_);
lean_dec(v_a_5362_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_dec_ref(v___x_5379_);
v___y_5337_ = v___x_5360_;
v_fst_5338_ = v_a_5361_;
goto v___jp_5336_;
}
else
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5387_; 
lean_dec(v_a_5361_);
lean_dec_ref(v_leanOpts_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_pkg_5318_);
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5382_ = v___x_5379_;
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5379_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5387_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5385_; 
if (v_isShared_5383_ == 0)
{
v___x_5385_ = v___x_5382_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
v___x_5385_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
return v___x_5385_;
}
}
}
}
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5389_; uint8_t v___x_5390_; 
lean_dec_ref(v_leanOpts_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_pkg_5318_);
v_a_5388_ = lean_ctor_get(v___x_5359_, 1);
lean_inc(v_a_5388_);
lean_dec_ref(v___x_5359_);
v___x_5389_ = lean_array_get_size(v_a_5388_);
v___x_5390_ = lean_nat_dec_lt(v___x_5357_, v___x_5389_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5392_; 
lean_dec(v_a_5388_);
if (v_isShared_5356_ == 0)
{
lean_ctor_set_tag(v___x_5355_, 1);
lean_ctor_set(v___x_5355_, 0, v___x_5360_);
v___x_5392_ = v___x_5355_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5360_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
else
{
uint8_t v___x_5394_; 
v___x_5394_ = lean_nat_dec_le(v___x_5389_, v___x_5389_);
if (v___x_5394_ == 0)
{
if (v___x_5390_ == 0)
{
lean_object* v___x_5396_; 
lean_dec(v_a_5388_);
if (v_isShared_5356_ == 0)
{
lean_ctor_set_tag(v___x_5355_, 1);
lean_ctor_set(v___x_5355_, 0, v___x_5360_);
v___x_5396_ = v___x_5355_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v___x_5360_);
v___x_5396_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
return v___x_5396_;
}
}
else
{
size_t v___x_5398_; size_t v___x_5399_; lean_object* v___x_5400_; 
lean_del_object(v___x_5355_);
v___x_5398_ = ((size_t)0ULL);
v___x_5399_ = lean_usize_of_nat(v___x_5389_);
v___x_5400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5388_, v___x_5398_, v___x_5399_, v___x_5360_, v___y_5328_);
lean_dec(v_a_5388_);
if (lean_obj_tag(v___x_5400_) == 0)
{
lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5407_ == 0)
{
lean_object* v_unused_5408_; 
v_unused_5408_ = lean_ctor_get(v___x_5400_, 0);
lean_dec(v_unused_5408_);
v___x_5402_ = v___x_5400_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_dec(v___x_5400_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set_tag(v___x_5402_, 1);
lean_ctor_set(v___x_5402_, 0, v___x_5360_);
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5360_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
else
{
lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5416_; 
v_a_5409_ = lean_ctor_get(v___x_5400_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5400_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5411_ = v___x_5400_;
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_dec(v___x_5400_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5414_; 
if (v_isShared_5412_ == 0)
{
v___x_5414_ = v___x_5411_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5409_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
}
else
{
size_t v___x_5417_; size_t v___x_5418_; lean_object* v___x_5419_; 
lean_del_object(v___x_5355_);
v___x_5417_ = ((size_t)0ULL);
v___x_5418_ = lean_usize_of_nat(v___x_5389_);
v___x_5419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5388_, v___x_5417_, v___x_5418_, v___x_5360_, v___y_5328_);
lean_dec(v_a_5388_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5426_ == 0)
{
lean_object* v_unused_5427_; 
v_unused_5427_ = lean_ctor_get(v___x_5419_, 0);
lean_dec(v_unused_5427_);
v___x_5421_ = v___x_5419_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_dec(v___x_5419_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5424_; 
if (v_isShared_5422_ == 0)
{
lean_ctor_set_tag(v___x_5421_, 1);
lean_ctor_set(v___x_5421_, 0, v___x_5360_);
v___x_5424_ = v___x_5421_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5360_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
else
{
lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
v_a_5428_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5419_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_dec(v___x_5419_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
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
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
lean_dec_ref(v___y_5327_);
lean_dec_ref(v_leanOpts_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_pkg_5318_);
v_a_5437_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5352_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5352_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
else
{
lean_object* v___x_5445_; uint8_t v___x_5446_; 
lean_inc(v_baseName_5345_);
lean_inc(v_wsIdx_5344_);
lean_dec(v___x_5349_);
lean_dec_ref(v___y_5327_);
lean_dec_ref(v_leanOpts_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_pkg_5318_);
v___x_5445_ = lean_unsigned_to_nat(0u);
v___x_5446_ = lean_nat_dec_eq(v_wsIdx_5344_, v___x_5445_);
lean_dec(v_wsIdx_5344_);
if (v___x_5446_ == 0)
{
lean_object* v___x_5447_; uint8_t v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__0));
v___x_5448_ = 1;
lean_inc(v_name_5346_);
v___x_5449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5346_, v___x_5448_);
v___x_5450_ = lean_string_append(v___x_5447_, v___x_5449_);
lean_dec_ref(v___x_5449_);
v___x_5451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__1));
v___x_5452_ = lean_string_append(v___x_5450_, v___x_5451_);
v___x_5453_ = l_Lean_Name_toString(v_baseName_5345_, v___x_5446_);
v___x_5454_ = lean_string_append(v___x_5452_, v___x_5453_);
lean_dec_ref(v___x_5453_);
v___x_5455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__2));
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
lean_dec(v_baseName_5345_);
v___x_5462_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__0));
lean_inc(v_name_5346_);
v___x_5463_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5346_, v___x_5446_);
v___x_5464_ = lean_string_append(v___x_5462_, v___x_5463_);
v___x_5465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__3));
v___x_5466_ = lean_string_append(v___x_5464_, v___x_5465_);
v___x_5467_ = lean_string_append(v___x_5466_, v___x_5463_);
lean_dec_ref(v___x_5463_);
v___x_5468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__4));
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
lean_inc(v_baseName_5345_);
lean_dec_ref(v___y_5327_);
lean_dec_ref(v_leanOpts_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_pkg_5318_);
v___x_5475_ = l_Lean_Name_toString(v_baseName_5345_, v___y_5343_);
v___x_5476_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__14___closed__0));
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
else
{
lean_object* v___x_5491_; lean_object* v___x_5492_; 
lean_dec_ref(v_leanOpts_5321_);
lean_dec_ref(v___y_5320_);
lean_dec_ref(v_pkg_5318_);
v___x_5491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5491_, 0, v_b_5326_);
lean_ctor_set(v___x_5491_, 1, v___y_5327_);
v___x_5492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5491_);
return v___x_5492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___boxed(lean_object* v_pkg_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v_leanOpts_5496_, lean_object* v_reconfigure_5497_, lean_object* v_as_5498_, lean_object* v_i_5499_, lean_object* v_stop_5500_, lean_object* v_b_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_){
_start:
{
uint8_t v_reconfigure_boxed_5505_; size_t v_i_boxed_5506_; size_t v_stop_boxed_5507_; lean_object* v_res_5508_; 
v_reconfigure_boxed_5505_ = lean_unbox(v_reconfigure_5497_);
v_i_boxed_5506_ = lean_unbox_usize(v_i_5499_);
lean_dec(v_i_5499_);
v_stop_boxed_5507_ = lean_unbox_usize(v_stop_5500_);
lean_dec(v_stop_5500_);
v_res_5508_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5493_, v___y_5494_, v___y_5495_, v_leanOpts_5496_, v_reconfigure_boxed_5505_, v_as_5498_, v_i_boxed_5506_, v_stop_boxed_5507_, v_b_5501_, v___y_5502_, v___y_5503_);
lean_dec_ref(v___y_5503_);
lean_dec_ref(v_as_5498_);
lean_dec(v___y_5494_);
return v_res_5508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v_leanOpts_5511_, uint8_t v_reconfigure_5512_, lean_object* v___x_5513_, lean_object* v_as_5514_, size_t v_i_5515_, size_t v_stop_5516_, lean_object* v_b_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_){
_start:
{
uint8_t v___x_5521_; 
v___x_5521_ = lean_usize_dec_eq(v_i_5515_, v_stop_5516_);
if (v___x_5521_ == 0)
{
lean_object* v___x_5522_; lean_object* v___x_5523_; 
v___x_5522_ = lean_array_uget_borrowed(v_as_5514_, v_i_5515_);
lean_inc(v___x_5522_);
lean_inc_ref(v_leanOpts_5511_);
lean_inc_ref(v___y_5510_);
v___x_5523_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_5509_, v___y_5510_, v_leanOpts_5511_, v_reconfigure_5512_, v___x_5522_, v___x_5513_, v___y_5518_, v___y_5519_);
if (lean_obj_tag(v___x_5523_) == 0)
{
lean_object* v_a_5524_; lean_object* v_fst_5525_; lean_object* v_snd_5526_; size_t v___x_5527_; size_t v___x_5528_; 
v_a_5524_ = lean_ctor_get(v___x_5523_, 0);
lean_inc(v_a_5524_);
lean_dec_ref(v___x_5523_);
v_fst_5525_ = lean_ctor_get(v_a_5524_, 0);
lean_inc(v_fst_5525_);
v_snd_5526_ = lean_ctor_get(v_a_5524_, 1);
lean_inc(v_snd_5526_);
lean_dec(v_a_5524_);
v___x_5527_ = ((size_t)1ULL);
v___x_5528_ = lean_usize_add(v_i_5515_, v___x_5527_);
v_i_5515_ = v___x_5528_;
v_b_5517_ = v_fst_5525_;
v___y_5518_ = v_snd_5526_;
goto _start;
}
else
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5537_; 
lean_dec_ref(v_leanOpts_5511_);
lean_dec_ref(v___y_5510_);
v_a_5530_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5523_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5523_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5535_; 
if (v_isShared_5533_ == 0)
{
v___x_5535_ = v___x_5532_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
else
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
lean_dec_ref(v_leanOpts_5511_);
lean_dec_ref(v___y_5510_);
v___x_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5538_, 0, v_b_5517_);
lean_ctor_set(v___x_5538_, 1, v___y_5518_);
v___x_5539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5538_);
return v___x_5539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12(lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v_leanOpts_5542_, uint8_t v_reconfigure_5543_, lean_object* v___x_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v_leanOpts_5547_, uint8_t v_reconfigure_5548_, lean_object* v_pkg_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v___y_5552_){
_start:
{
lean_object* v_packages_5554_; lean_object* v_depConfigs_5555_; lean_object* v___x_5556_; lean_object* v_snd_5558_; lean_object* v_packages_5559_; lean_object* v___y_5560_; lean_object* v_____x_5576_; lean_object* v___y_5577_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; uint8_t v___x_5583_; 
v_packages_5554_ = lean_ctor_get(v_a_5551_, 5);
v_depConfigs_5555_ = lean_ctor_get(v_pkg_5549_, 12);
lean_inc_ref(v_depConfigs_5555_);
v___x_5556_ = lean_array_get_size(v_packages_5554_);
v___x_5580_ = lean_array_get_size(v_depConfigs_5555_);
v___x_5581_ = lean_unsigned_to_nat(0u);
v___x_5582_ = lean_box(0);
v___x_5583_ = lean_nat_dec_le(v___x_5580_, v___x_5580_);
if (v___x_5583_ == 0)
{
uint8_t v___x_5584_; 
v___x_5584_ = lean_nat_dec_lt(v___x_5581_, v___x_5580_);
if (v___x_5584_ == 0)
{
uint8_t v___x_5585_; 
lean_dec_ref(v_depConfigs_5555_);
lean_dec_ref(v_pkg_5549_);
lean_dec_ref(v_leanOpts_5547_);
lean_dec_ref(v___y_5546_);
v___x_5585_ = lean_nat_dec_lt(v___x_5556_, v___x_5556_);
if (v___x_5585_ == 0)
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
lean_dec_ref(v_leanOpts_5542_);
lean_dec_ref(v___y_5541_);
v___x_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5582_);
lean_ctor_set(v___x_5586_, 1, v_a_5551_);
v___x_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
return v___x_5587_;
}
else
{
uint8_t v___x_5588_; 
v___x_5588_ = lean_nat_dec_le(v___x_5556_, v___x_5556_);
if (v___x_5588_ == 0)
{
if (v___x_5585_ == 0)
{
lean_object* v___x_5589_; lean_object* v___x_5590_; 
lean_dec_ref(v_leanOpts_5542_);
lean_dec_ref(v___y_5541_);
v___x_5589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5582_);
lean_ctor_set(v___x_5589_, 1, v_a_5551_);
v___x_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5590_, 0, v___x_5589_);
return v___x_5590_;
}
else
{
size_t v___x_5591_; lean_object* v___x_5592_; 
lean_inc_ref(v_packages_5554_);
v___x_5591_ = lean_usize_of_nat(v___x_5556_);
v___x_5592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5540_, v___y_5541_, v_leanOpts_5542_, v_reconfigure_5543_, v___x_5544_, v_packages_5554_, v___x_5591_, v___x_5591_, v___x_5582_, v_a_5551_, v___y_5552_);
lean_dec_ref(v_packages_5554_);
return v___x_5592_;
}
}
else
{
size_t v___x_5593_; lean_object* v___x_5594_; 
lean_inc_ref(v_packages_5554_);
v___x_5593_ = lean_usize_of_nat(v___x_5556_);
v___x_5594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5540_, v___y_5541_, v_leanOpts_5542_, v_reconfigure_5543_, v___x_5544_, v_packages_5554_, v___x_5593_, v___x_5593_, v___x_5582_, v_a_5551_, v___y_5552_);
lean_dec_ref(v_packages_5554_);
return v___x_5594_;
}
}
}
else
{
size_t v___x_5595_; size_t v___x_5596_; lean_object* v___x_5597_; 
v___x_5595_ = lean_usize_of_nat(v___x_5580_);
v___x_5596_ = ((size_t)0ULL);
v___x_5597_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5549_, v___y_5545_, v___y_5546_, v_leanOpts_5547_, v_reconfigure_5548_, v_depConfigs_5555_, v___x_5595_, v___x_5596_, v___x_5582_, v_a_5551_, v___y_5552_);
lean_dec_ref(v_depConfigs_5555_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; 
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
lean_inc(v_a_5598_);
lean_dec_ref(v___x_5597_);
v_____x_5576_ = v_a_5598_;
v___y_5577_ = v___y_5552_;
goto v___jp_5575_;
}
else
{
lean_dec_ref(v_leanOpts_5542_);
lean_dec_ref(v___y_5541_);
return v___x_5597_;
}
}
}
else
{
uint8_t v___x_5599_; 
v___x_5599_ = lean_nat_dec_lt(v___x_5581_, v___x_5580_);
if (v___x_5599_ == 0)
{
lean_inc_ref(v_packages_5554_);
lean_dec_ref(v_depConfigs_5555_);
lean_dec_ref(v_pkg_5549_);
lean_dec_ref(v_leanOpts_5547_);
lean_dec_ref(v___y_5546_);
v_snd_5558_ = v_a_5551_;
v_packages_5559_ = v_packages_5554_;
v___y_5560_ = v___y_5552_;
goto v___jp_5557_;
}
else
{
size_t v___x_5600_; size_t v___x_5601_; lean_object* v___x_5602_; 
v___x_5600_ = lean_usize_of_nat(v___x_5580_);
v___x_5601_ = ((size_t)0ULL);
v___x_5602_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5549_, v___y_5545_, v___y_5546_, v_leanOpts_5547_, v_reconfigure_5548_, v_depConfigs_5555_, v___x_5600_, v___x_5601_, v___x_5582_, v_a_5551_, v___y_5552_);
lean_dec_ref(v_depConfigs_5555_);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_object* v_a_5603_; 
v_a_5603_ = lean_ctor_get(v___x_5602_, 0);
lean_inc(v_a_5603_);
lean_dec_ref(v___x_5602_);
v_____x_5576_ = v_a_5603_;
v___y_5577_ = v___y_5552_;
goto v___jp_5575_;
}
else
{
lean_dec_ref(v_leanOpts_5542_);
lean_dec_ref(v___y_5541_);
return v___x_5602_;
}
}
}
v___jp_5557_:
{
lean_object* v___x_5561_; lean_object* v___x_5562_; uint8_t v___x_5563_; 
v___x_5561_ = lean_array_get_size(v_packages_5559_);
v___x_5562_ = lean_box(0);
v___x_5563_ = lean_nat_dec_lt(v___x_5556_, v___x_5561_);
if (v___x_5563_ == 0)
{
lean_object* v___x_5564_; lean_object* v___x_5565_; 
lean_dec_ref(v_packages_5559_);
lean_dec_ref(v_leanOpts_5542_);
lean_dec_ref(v___y_5541_);
v___x_5564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5562_);
lean_ctor_set(v___x_5564_, 1, v_snd_5558_);
v___x_5565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
return v___x_5565_;
}
else
{
uint8_t v___x_5566_; 
v___x_5566_ = lean_nat_dec_le(v___x_5561_, v___x_5561_);
if (v___x_5566_ == 0)
{
if (v___x_5563_ == 0)
{
lean_object* v___x_5567_; lean_object* v___x_5568_; 
lean_dec_ref(v_packages_5559_);
lean_dec_ref(v_leanOpts_5542_);
lean_dec_ref(v___y_5541_);
v___x_5567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5562_);
lean_ctor_set(v___x_5567_, 1, v_snd_5558_);
v___x_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5567_);
return v___x_5568_;
}
else
{
size_t v___x_5569_; size_t v___x_5570_; lean_object* v___x_5571_; 
v___x_5569_ = lean_usize_of_nat(v___x_5556_);
v___x_5570_ = lean_usize_of_nat(v___x_5561_);
v___x_5571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5540_, v___y_5541_, v_leanOpts_5542_, v_reconfigure_5543_, v___x_5544_, v_packages_5559_, v___x_5569_, v___x_5570_, v___x_5562_, v_snd_5558_, v___y_5560_);
lean_dec_ref(v_packages_5559_);
return v___x_5571_;
}
}
else
{
size_t v___x_5572_; size_t v___x_5573_; lean_object* v___x_5574_; 
v___x_5572_ = lean_usize_of_nat(v___x_5556_);
v___x_5573_ = lean_usize_of_nat(v___x_5561_);
v___x_5574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5540_, v___y_5541_, v_leanOpts_5542_, v_reconfigure_5543_, v___x_5544_, v_packages_5559_, v___x_5572_, v___x_5573_, v___x_5562_, v_snd_5558_, v___y_5560_);
lean_dec_ref(v_packages_5559_);
return v___x_5574_;
}
}
}
v___jp_5575_:
{
lean_object* v_snd_5578_; lean_object* v_packages_5579_; 
v_snd_5578_ = lean_ctor_get(v_____x_5576_, 1);
lean_inc(v_snd_5578_);
lean_dec_ref(v_____x_5576_);
v_packages_5579_ = lean_ctor_get(v_snd_5578_, 5);
lean_inc_ref(v_packages_5579_);
v_snd_5558_ = v_snd_5578_;
v_packages_5559_ = v_packages_5579_;
v___y_5560_ = v___y_5577_;
goto v___jp_5557_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v_leanOpts_5606_, uint8_t v_reconfigure_5607_, lean_object* v_a_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
lean_object* v_baseName_5613_; uint8_t v___x_5614_; 
v_baseName_5613_ = lean_ctor_get(v_a_5608_, 1);
v___x_5614_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__10(v_baseName_5613_, v___y_5609_);
if (v___x_5614_ == 0)
{
lean_object* v___x_5615_; lean_object* v___x_5616_; 
lean_inc(v___y_5609_);
lean_inc(v_baseName_5613_);
v___x_5615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5615_, 0, v_baseName_5613_);
lean_ctor_set(v___x_5615_, 1, v___y_5609_);
lean_inc_ref(v_leanOpts_5606_);
lean_inc_ref(v___y_5605_);
v___x_5616_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12(v___y_5604_, v___y_5605_, v_leanOpts_5606_, v_reconfigure_5607_, v___x_5615_, v___y_5604_, v___y_5605_, v_leanOpts_5606_, v_reconfigure_5607_, v_a_5608_, v___x_5615_, v___y_5610_, v___y_5611_);
lean_dec_ref(v___x_5615_);
return v___x_5616_;
}
else
{
lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v_fst_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5630_; 
lean_inc(v_baseName_5613_);
lean_dec_ref(v___y_5610_);
lean_dec_ref(v_a_5608_);
lean_dec_ref(v_leanOpts_5606_);
lean_dec_ref(v___y_5605_);
v___x_5617_ = lean_box(0);
v___x_5618_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__14___redArg___closed__0));
lean_inc(v___y_5609_);
v___x_5619_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__8_spec__12(v_baseName_5613_, v___x_5614_, v___y_5609_, v___x_5618_);
v_fst_5620_ = lean_ctor_get(v___x_5619_, 0);
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5619_);
if (v_isSharedCheck_5630_ == 0)
{
lean_object* v_unused_5631_; 
v_unused_5631_ = lean_ctor_get(v___x_5619_, 1);
lean_dec(v_unused_5631_);
v___x_5622_ = v___x_5619_;
v_isShared_5623_ = v_isSharedCheck_5630_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_fst_5620_);
lean_dec(v___x_5619_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5630_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5625_; 
lean_inc(v_baseName_5613_);
if (v_isShared_5623_ == 0)
{
lean_ctor_set_tag(v___x_5622_, 1);
lean_ctor_set(v___x_5622_, 1, v_fst_5620_);
lean_ctor_set(v___x_5622_, 0, v_baseName_5613_);
v___x_5625_ = v___x_5622_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_baseName_5613_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v_fst_5620_);
v___x_5625_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; 
v___x_5626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5626_, 0, v_baseName_5613_);
lean_ctor_set(v___x_5626_, 1, v___x_5617_);
v___x_5627_ = l_List_appendTR___redArg(v___x_5625_, v___x_5626_);
v___x_5628_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(v___x_5627_, v___y_5611_);
return v___x_5628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v_leanOpts_5634_, lean_object* v_reconfigure_5635_, lean_object* v_a_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_){
_start:
{
uint8_t v_reconfigure_boxed_5641_; lean_object* v_res_5642_; 
v_reconfigure_boxed_5641_ = lean_unbox(v_reconfigure_5635_);
v_res_5642_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_5632_, v___y_5633_, v_leanOpts_5634_, v_reconfigure_boxed_5641_, v_a_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
lean_dec_ref(v___y_5639_);
lean_dec(v___y_5637_);
lean_dec(v___y_5632_);
return v_res_5642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg___boxed(lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v_leanOpts_5645_, lean_object* v_reconfigure_5646_, lean_object* v___x_5647_, lean_object* v_as_5648_, lean_object* v_i_5649_, lean_object* v_stop_5650_, lean_object* v_b_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_){
_start:
{
uint8_t v_reconfigure_boxed_5655_; size_t v_i_boxed_5656_; size_t v_stop_boxed_5657_; lean_object* v_res_5658_; 
v_reconfigure_boxed_5655_ = lean_unbox(v_reconfigure_5646_);
v_i_boxed_5656_ = lean_unbox_usize(v_i_5649_);
lean_dec(v_i_5649_);
v_stop_boxed_5657_ = lean_unbox_usize(v_stop_5650_);
lean_dec(v_stop_5650_);
v_res_5658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5643_, v___y_5644_, v_leanOpts_5645_, v_reconfigure_boxed_5655_, v___x_5647_, v_as_5648_, v_i_boxed_5656_, v_stop_boxed_5657_, v_b_5651_, v___y_5652_, v___y_5653_);
lean_dec_ref(v___y_5653_);
lean_dec_ref(v_as_5648_);
lean_dec(v___x_5647_);
lean_dec(v___y_5643_);
return v_res_5658_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12___boxed(lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v_leanOpts_5661_, lean_object* v_reconfigure_5662_, lean_object* v___x_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v_leanOpts_5666_, lean_object* v_reconfigure_5667_, lean_object* v_pkg_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_){
_start:
{
uint8_t v_reconfigure_boxed_5673_; uint8_t v_reconfigure_boxed_5674_; lean_object* v_res_5675_; 
v_reconfigure_boxed_5673_ = lean_unbox(v_reconfigure_5662_);
v_reconfigure_boxed_5674_ = lean_unbox(v_reconfigure_5667_);
v_res_5675_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12(v___y_5659_, v___y_5660_, v_leanOpts_5661_, v_reconfigure_boxed_5673_, v___x_5663_, v___y_5664_, v___y_5665_, v_leanOpts_5666_, v_reconfigure_boxed_5674_, v_pkg_5668_, v_a_5669_, v_a_5670_, v___y_5671_);
lean_dec_ref(v___y_5671_);
lean_dec(v_a_5669_);
lean_dec(v___y_5664_);
lean_dec(v___x_5663_);
lean_dec(v___y_5659_);
return v_res_5675_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v_leanOpts_5678_, uint8_t v_reconfigure_5679_, lean_object* v_ws_5680_, lean_object* v_root_5681_, lean_object* v_stack_5682_, lean_object* v___y_5683_){
_start:
{
lean_object* v___x_5685_; 
v___x_5685_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_5676_, v___y_5677_, v_leanOpts_5678_, v_reconfigure_5679_, v_root_5681_, v_stack_5682_, v_ws_5680_, v___y_5683_);
if (lean_obj_tag(v___x_5685_) == 0)
{
lean_object* v_a_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5694_; 
v_a_5686_ = lean_ctor_get(v___x_5685_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5685_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5688_ = v___x_5685_;
v_isShared_5689_ = v_isSharedCheck_5694_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_a_5686_);
lean_dec(v___x_5685_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5694_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v_snd_5690_; lean_object* v___x_5692_; 
v_snd_5690_ = lean_ctor_get(v_a_5686_, 1);
lean_inc(v_snd_5690_);
lean_dec(v_a_5686_);
if (v_isShared_5689_ == 0)
{
lean_ctor_set(v___x_5688_, 0, v_snd_5690_);
v___x_5692_ = v___x_5688_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_snd_5690_);
v___x_5692_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
return v___x_5692_;
}
}
}
else
{
lean_object* v_a_5695_; lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5702_; 
v_a_5695_ = lean_ctor_get(v___x_5685_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5685_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5697_ = v___x_5685_;
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
else
{
lean_inc(v_a_5695_);
lean_dec(v___x_5685_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5702_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5700_; 
if (v_isShared_5698_ == 0)
{
v___x_5700_ = v___x_5697_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_a_5695_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v_leanOpts_5705_, lean_object* v_reconfigure_5706_, lean_object* v_ws_5707_, lean_object* v_root_5708_, lean_object* v_stack_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_){
_start:
{
uint8_t v_reconfigure_boxed_5712_; lean_object* v_res_5713_; 
v_reconfigure_boxed_5712_ = lean_unbox(v_reconfigure_5706_);
v_res_5713_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1(v___y_5703_, v___y_5704_, v_leanOpts_5705_, v_reconfigure_boxed_5712_, v_ws_5707_, v_root_5708_, v_stack_5709_, v___y_5710_);
lean_dec_ref(v___y_5710_);
lean_dec(v_stack_5709_);
lean_dec(v___y_5703_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5(lean_object* v_as_5714_, size_t v_i_5715_, size_t v_stop_5716_, lean_object* v_b_5717_){
_start:
{
uint8_t v___x_5718_; 
v___x_5718_ = lean_usize_dec_eq(v_i_5715_, v_stop_5716_);
if (v___x_5718_ == 0)
{
lean_object* v___x_5719_; lean_object* v_name_5720_; lean_object* v___x_5721_; size_t v___x_5722_; size_t v___x_5723_; 
v___x_5719_ = lean_array_uget_borrowed(v_as_5714_, v_i_5715_);
v_name_5720_ = lean_ctor_get(v___x_5719_, 0);
lean_inc(v___x_5719_);
lean_inc(v_name_5720_);
v___x_5721_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5720_, v___x_5719_, v_b_5717_);
v___x_5722_ = ((size_t)1ULL);
v___x_5723_ = lean_usize_add(v_i_5715_, v___x_5722_);
v_i_5715_ = v___x_5723_;
v_b_5717_ = v___x_5721_;
goto _start;
}
else
{
return v_b_5717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5___boxed(lean_object* v_as_5725_, lean_object* v_i_5726_, lean_object* v_stop_5727_, lean_object* v_b_5728_){
_start:
{
size_t v_i_boxed_5729_; size_t v_stop_boxed_5730_; lean_object* v_res_5731_; 
v_i_boxed_5729_ = lean_unbox_usize(v_i_5726_);
lean_dec(v_i_5726_);
v_stop_boxed_5730_ = lean_unbox_usize(v_stop_5727_);
lean_dec(v_stop_5727_);
v_res_5731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5(v_as_5725_, v_i_boxed_5729_, v_stop_boxed_5730_, v_b_5728_);
lean_dec_ref(v_as_5725_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_as_5732_, size_t v_i_5733_, size_t v_stop_5734_, lean_object* v_b_5735_){
_start:
{
uint8_t v___x_5736_; 
v___x_5736_ = lean_usize_dec_eq(v_i_5733_, v_stop_5734_);
if (v___x_5736_ == 0)
{
lean_object* v___x_5737_; lean_object* v_name_5738_; lean_object* v___x_5739_; size_t v___x_5740_; size_t v___x_5741_; lean_object* v___x_5742_; 
v___x_5737_ = lean_array_uget_borrowed(v_as_5732_, v_i_5733_);
v_name_5738_ = lean_ctor_get(v___x_5737_, 0);
lean_inc(v___x_5737_);
lean_inc(v_name_5738_);
v___x_5739_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5738_, v___x_5737_, v_b_5735_);
v___x_5740_ = ((size_t)1ULL);
v___x_5741_ = lean_usize_add(v_i_5733_, v___x_5740_);
v___x_5742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5(v_as_5732_, v___x_5741_, v_stop_5734_, v___x_5739_);
return v___x_5742_;
}
else
{
return v_b_5735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_as_5743_, lean_object* v_i_5744_, lean_object* v_stop_5745_, lean_object* v_b_5746_){
_start:
{
size_t v_i_boxed_5747_; size_t v_stop_boxed_5748_; lean_object* v_res_5749_; 
v_i_boxed_5747_ = lean_unbox_usize(v_i_5744_);
lean_dec(v_i_5744_);
v_stop_boxed_5748_ = lean_unbox_usize(v_stop_5745_);
lean_dec(v_stop_5745_);
v_res_5749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_as_5743_, v_i_boxed_5747_, v_stop_boxed_5748_, v_b_5746_);
lean_dec_ref(v_as_5743_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_5759_, lean_object* v_manifest_5760_, lean_object* v_leanOpts_5761_, uint8_t v_reconfigure_5762_, lean_object* v_overrides_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v___y_5767_; lean_object* v___y_5768_; lean_object* v___y_5769_; lean_object* v___y_5770_; lean_object* v___y_5774_; lean_object* v___y_5775_; lean_object* v___y_5776_; lean_object* v___y_5777_; lean_object* v___y_5778_; lean_object* v___y_5779_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v___y_5790_; lean_object* v___y_5791_; lean_object* v___y_5792_; lean_object* v___y_5803_; lean_object* v___y_5804_; lean_object* v___y_5805_; lean_object* v___y_5806_; lean_object* v_packagesDir_x3f_5847_; lean_object* v_packages_5848_; lean_object* v___y_5850_; lean_object* v___y_5851_; lean_object* v___y_5864_; lean_object* v___x_5870_; lean_object* v___x_5871_; uint8_t v___x_5872_; 
v_packagesDir_x3f_5847_ = lean_ctor_get(v_manifest_5760_, 2);
lean_inc(v_packagesDir_x3f_5847_);
v_packages_5848_ = lean_ctor_get(v_manifest_5760_, 3);
lean_inc_ref(v_packages_5848_);
lean_dec_ref(v_manifest_5760_);
v___x_5870_ = lean_array_get_size(v_packages_5848_);
v___x_5871_ = lean_unsigned_to_nat(0u);
v___x_5872_ = lean_nat_dec_eq(v___x_5870_, v___x_5871_);
if (v___x_5872_ == 0)
{
lean_object* v_root_5873_; lean_object* v_config_5874_; lean_object* v_toWorkspaceConfig_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; uint8_t v___x_5879_; 
v_root_5873_ = lean_ctor_get(v_ws_5759_, 0);
v_config_5874_ = lean_ctor_get(v_root_5873_, 6);
v_toWorkspaceConfig_5875_ = lean_ctor_get(v_config_5874_, 0);
lean_inc_ref(v_toWorkspaceConfig_5875_);
v___x_5876_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5875_);
v___x_5877_ = l_Lake_mkRelPathString(v___x_5876_);
v___x_5878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5877_);
v___x_5879_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3(v_packagesDir_x3f_5847_, v___x_5878_);
lean_dec_ref(v___x_5878_);
if (v___x_5879_ == 0)
{
lean_object* v___x_5880_; lean_object* v___x_5881_; 
v___x_5880_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_5764_);
v___x_5881_ = lean_apply_2(v_a_5764_, v___x_5880_, lean_box(0));
v___y_5864_ = v_a_5764_;
goto v___jp_5863_;
}
else
{
v___y_5864_ = v_a_5764_;
goto v___jp_5863_;
}
}
else
{
v___y_5864_ = v_a_5764_;
goto v___jp_5863_;
}
v___jp_5766_:
{
lean_object* v___x_5771_; lean_object* v___x_5772_; 
v___x_5771_ = lean_box(0);
v___x_5772_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1(v___y_5767_, v___y_5769_, v_leanOpts_5761_, v_reconfigure_5762_, v_ws_5759_, v___y_5768_, v___x_5771_, v___y_5770_);
lean_dec(v___y_5767_);
return v___x_5772_;
}
v___jp_5773_:
{
if (lean_obj_tag(v___y_5779_) == 0)
{
lean_dec_ref(v___y_5774_);
v___y_5767_ = v___y_5779_;
v___y_5768_ = v___y_5775_;
v___y_5769_ = v___y_5776_;
v___y_5770_ = v___y_5777_;
goto v___jp_5766_;
}
else
{
lean_object* v___x_5780_; uint8_t v___x_5781_; 
v___x_5780_ = lean_array_get_size(v___y_5774_);
lean_dec_ref(v___y_5774_);
v___x_5781_ = lean_nat_dec_eq(v___x_5780_, v___y_5778_);
if (v___x_5781_ == 0)
{
lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; 
lean_dec_ref(v___y_5776_);
lean_dec_ref(v___y_5775_);
lean_dec_ref(v_leanOpts_5761_);
lean_dec_ref(v_ws_5759_);
v___x_5782_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_5777_);
v___x_5783_ = lean_apply_2(v___y_5777_, v___x_5782_, lean_box(0));
v___x_5784_ = lean_box(0);
v___x_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5785_, 0, v___x_5784_);
return v___x_5785_;
}
else
{
v___y_5767_ = v___y_5779_;
v___y_5768_ = v___y_5775_;
v___y_5769_ = v___y_5776_;
v___y_5770_ = v___y_5777_;
goto v___jp_5766_;
}
}
}
v___jp_5786_:
{
lean_object* v___x_5793_; uint8_t v___x_5794_; 
v___x_5793_ = lean_array_get_size(v_overrides_5763_);
v___x_5794_ = lean_nat_dec_lt(v___y_5791_, v___x_5793_);
if (v___x_5794_ == 0)
{
v___y_5774_ = v___y_5787_;
v___y_5775_ = v___y_5788_;
v___y_5776_ = v___y_5789_;
v___y_5777_ = v___y_5790_;
v___y_5778_ = v___y_5791_;
v___y_5779_ = v___y_5792_;
goto v___jp_5773_;
}
else
{
uint8_t v___x_5795_; 
v___x_5795_ = lean_nat_dec_le(v___x_5793_, v___x_5793_);
if (v___x_5795_ == 0)
{
if (v___x_5794_ == 0)
{
v___y_5774_ = v___y_5787_;
v___y_5775_ = v___y_5788_;
v___y_5776_ = v___y_5789_;
v___y_5777_ = v___y_5790_;
v___y_5778_ = v___y_5791_;
v___y_5779_ = v___y_5792_;
goto v___jp_5773_;
}
else
{
size_t v___x_5796_; size_t v___x_5797_; lean_object* v___x_5798_; 
v___x_5796_ = ((size_t)0ULL);
v___x_5797_ = lean_usize_of_nat(v___x_5793_);
v___x_5798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_overrides_5763_, v___x_5796_, v___x_5797_, v___y_5792_);
v___y_5774_ = v___y_5787_;
v___y_5775_ = v___y_5788_;
v___y_5776_ = v___y_5789_;
v___y_5777_ = v___y_5790_;
v___y_5778_ = v___y_5791_;
v___y_5779_ = v___x_5798_;
goto v___jp_5773_;
}
}
else
{
size_t v___x_5799_; size_t v___x_5800_; lean_object* v___x_5801_; 
v___x_5799_ = ((size_t)0ULL);
v___x_5800_ = lean_usize_of_nat(v___x_5793_);
v___x_5801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_overrides_5763_, v___x_5799_, v___x_5800_, v___y_5792_);
v___y_5774_ = v___y_5787_;
v___y_5775_ = v___y_5788_;
v___y_5776_ = v___y_5789_;
v___y_5777_ = v___y_5790_;
v___y_5778_ = v___y_5791_;
v___y_5779_ = v___x_5801_;
goto v___jp_5773_;
}
}
}
v___jp_5802_:
{
lean_object* v_root_5807_; lean_object* v_dir_5808_; lean_object* v_depConfigs_5809_; lean_object* v___x_5810_; 
v_root_5807_ = lean_ctor_get(v_ws_5759_, 0);
v_dir_5808_ = lean_ctor_get(v_root_5807_, 4);
v_depConfigs_5809_ = lean_ctor_get(v_root_5807_, 12);
v___x_5810_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_5806_, v_depConfigs_5809_, v___y_5804_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; 
lean_dec_ref(v___x_5810_);
v___x_5811_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_5808_);
v___x_5812_ = l_Lake_joinRelative(v_dir_5808_, v___x_5811_);
v___x_5813_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_5814_ = l_Lake_joinRelative(v___x_5812_, v___x_5813_);
v___x_5815_ = l_Lake_Manifest_tryLoadEntries(v___x_5814_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_object* v_a_5816_; lean_object* v___x_5817_; uint8_t v___x_5818_; 
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
lean_inc(v_a_5816_);
lean_dec_ref(v___x_5815_);
v___x_5817_ = lean_array_get_size(v_a_5816_);
v___x_5818_ = lean_nat_dec_lt(v___y_5805_, v___x_5817_);
if (v___x_5818_ == 0)
{
lean_dec(v_a_5816_);
lean_inc_ref(v_root_5807_);
lean_inc_ref(v_depConfigs_5809_);
v___y_5787_ = v_depConfigs_5809_;
v___y_5788_ = v_root_5807_;
v___y_5789_ = v___y_5803_;
v___y_5790_ = v___y_5804_;
v___y_5791_ = v___y_5805_;
v___y_5792_ = v___y_5806_;
goto v___jp_5786_;
}
else
{
uint8_t v___x_5819_; 
v___x_5819_ = lean_nat_dec_le(v___x_5817_, v___x_5817_);
if (v___x_5819_ == 0)
{
if (v___x_5818_ == 0)
{
lean_dec(v_a_5816_);
lean_inc_ref(v_root_5807_);
lean_inc_ref(v_depConfigs_5809_);
v___y_5787_ = v_depConfigs_5809_;
v___y_5788_ = v_root_5807_;
v___y_5789_ = v___y_5803_;
v___y_5790_ = v___y_5804_;
v___y_5791_ = v___y_5805_;
v___y_5792_ = v___y_5806_;
goto v___jp_5786_;
}
else
{
size_t v___x_5820_; size_t v___x_5821_; lean_object* v___x_5822_; 
v___x_5820_ = ((size_t)0ULL);
v___x_5821_ = lean_usize_of_nat(v___x_5817_);
v___x_5822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_a_5816_, v___x_5820_, v___x_5821_, v___y_5806_);
lean_dec(v_a_5816_);
lean_inc_ref(v_root_5807_);
lean_inc_ref(v_depConfigs_5809_);
v___y_5787_ = v_depConfigs_5809_;
v___y_5788_ = v_root_5807_;
v___y_5789_ = v___y_5803_;
v___y_5790_ = v___y_5804_;
v___y_5791_ = v___y_5805_;
v___y_5792_ = v___x_5822_;
goto v___jp_5786_;
}
}
else
{
size_t v___x_5823_; size_t v___x_5824_; lean_object* v___x_5825_; 
v___x_5823_ = ((size_t)0ULL);
v___x_5824_ = lean_usize_of_nat(v___x_5817_);
v___x_5825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_a_5816_, v___x_5823_, v___x_5824_, v___y_5806_);
lean_dec(v_a_5816_);
lean_inc_ref(v_root_5807_);
lean_inc_ref(v_depConfigs_5809_);
v___y_5787_ = v_depConfigs_5809_;
v___y_5788_ = v_root_5807_;
v___y_5789_ = v___y_5803_;
v___y_5790_ = v___y_5804_;
v___y_5791_ = v___y_5805_;
v___y_5792_ = v___x_5825_;
goto v___jp_5786_;
}
}
}
else
{
lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5838_; 
lean_dec(v___y_5806_);
lean_dec_ref(v___y_5803_);
lean_dec_ref(v_leanOpts_5761_);
lean_dec_ref(v_ws_5759_);
v_a_5826_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5838_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5838_ == 0)
{
v___x_5828_ = v___x_5815_;
v_isShared_5829_ = v_isSharedCheck_5838_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v___x_5815_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5838_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5830_; uint8_t v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5836_; 
v___x_5830_ = lean_io_error_to_string(v_a_5826_);
v___x_5831_ = 3;
v___x_5832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5832_, 0, v___x_5830_);
lean_ctor_set_uint8(v___x_5832_, sizeof(void*)*1, v___x_5831_);
lean_inc_ref(v___y_5804_);
v___x_5833_ = lean_apply_2(v___y_5804_, v___x_5832_, lean_box(0));
v___x_5834_ = lean_box(0);
if (v_isShared_5829_ == 0)
{
lean_ctor_set(v___x_5828_, 0, v___x_5834_);
v___x_5836_ = v___x_5828_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5834_);
v___x_5836_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
return v___x_5836_;
}
}
}
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5846_; 
lean_dec(v___y_5806_);
lean_dec_ref(v___y_5803_);
lean_dec_ref(v_leanOpts_5761_);
lean_dec_ref(v_ws_5759_);
v_a_5839_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5841_ = v___x_5810_;
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_a_5839_);
lean_dec(v___x_5810_);
v___x_5841_ = lean_box(0);
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
v_resetjp_5840_:
{
lean_object* v___x_5844_; 
if (v_isShared_5842_ == 0)
{
v___x_5844_ = v___x_5841_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5839_);
v___x_5844_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
return v___x_5844_;
}
}
}
}
v___jp_5849_:
{
lean_object* v_pkgEntries_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; uint8_t v___x_5855_; 
v_pkgEntries_5852_ = lean_box(1);
v___x_5853_ = lean_unsigned_to_nat(0u);
v___x_5854_ = lean_array_get_size(v_packages_5848_);
v___x_5855_ = lean_nat_dec_lt(v___x_5853_, v___x_5854_);
if (v___x_5855_ == 0)
{
lean_dec_ref(v_packages_5848_);
v___y_5803_ = v___y_5851_;
v___y_5804_ = v___y_5850_;
v___y_5805_ = v___x_5853_;
v___y_5806_ = v_pkgEntries_5852_;
goto v___jp_5802_;
}
else
{
uint8_t v___x_5856_; 
v___x_5856_ = lean_nat_dec_le(v___x_5854_, v___x_5854_);
if (v___x_5856_ == 0)
{
if (v___x_5855_ == 0)
{
lean_dec_ref(v_packages_5848_);
v___y_5803_ = v___y_5851_;
v___y_5804_ = v___y_5850_;
v___y_5805_ = v___x_5853_;
v___y_5806_ = v_pkgEntries_5852_;
goto v___jp_5802_;
}
else
{
size_t v___x_5857_; size_t v___x_5858_; lean_object* v___x_5859_; 
v___x_5857_ = ((size_t)0ULL);
v___x_5858_ = lean_usize_of_nat(v___x_5854_);
v___x_5859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_packages_5848_, v___x_5857_, v___x_5858_, v_pkgEntries_5852_);
lean_dec_ref(v_packages_5848_);
v___y_5803_ = v___y_5851_;
v___y_5804_ = v___y_5850_;
v___y_5805_ = v___x_5853_;
v___y_5806_ = v___x_5859_;
goto v___jp_5802_;
}
}
else
{
size_t v___x_5860_; size_t v___x_5861_; lean_object* v___x_5862_; 
v___x_5860_ = ((size_t)0ULL);
v___x_5861_ = lean_usize_of_nat(v___x_5854_);
v___x_5862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_packages_5848_, v___x_5860_, v___x_5861_, v_pkgEntries_5852_);
lean_dec_ref(v_packages_5848_);
v___y_5803_ = v___y_5851_;
v___y_5804_ = v___y_5850_;
v___y_5805_ = v___x_5853_;
v___y_5806_ = v___x_5862_;
goto v___jp_5802_;
}
}
}
v___jp_5863_:
{
if (lean_obj_tag(v_packagesDir_x3f_5847_) == 0)
{
lean_object* v_root_5865_; lean_object* v_config_5866_; lean_object* v_toWorkspaceConfig_5867_; lean_object* v___x_5868_; 
v_root_5865_ = lean_ctor_get(v_ws_5759_, 0);
v_config_5866_ = lean_ctor_get(v_root_5865_, 6);
v_toWorkspaceConfig_5867_ = lean_ctor_get(v_config_5866_, 0);
lean_inc_ref(v_toWorkspaceConfig_5867_);
v___x_5868_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5867_);
v___y_5850_ = v___y_5864_;
v___y_5851_ = v___x_5868_;
goto v___jp_5849_;
}
else
{
lean_object* v_val_5869_; 
v_val_5869_ = lean_ctor_get(v_packagesDir_x3f_5847_, 0);
lean_inc(v_val_5869_);
lean_dec_ref(v_packagesDir_x3f_5847_);
v___y_5850_ = v___y_5864_;
v___y_5851_ = v_val_5869_;
goto v___jp_5849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_5882_, lean_object* v_manifest_5883_, lean_object* v_leanOpts_5884_, lean_object* v_reconfigure_5885_, lean_object* v_overrides_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_){
_start:
{
uint8_t v_reconfigure_boxed_5889_; lean_object* v_res_5890_; 
v_reconfigure_boxed_5889_ = lean_unbox(v_reconfigure_5885_);
v_res_5890_ = l_Lake_Workspace_materializeDeps(v_ws_5882_, v_manifest_5883_, v_leanOpts_5884_, v_reconfigure_boxed_5889_, v_overrides_5886_, v_a_5887_);
lean_dec_ref(v_a_5887_);
lean_dec_ref(v_overrides_5886_);
return v_res_5890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v___y_5891_, lean_object* v_as_5892_, size_t v_i_5893_, size_t v_stop_5894_, lean_object* v_b_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_){
_start:
{
uint8_t v___x_5900_; 
v___x_5900_ = lean_usize_dec_eq(v_i_5893_, v_stop_5894_);
if (v___x_5900_ == 0)
{
lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5901_ = lean_array_uget_borrowed(v_as_5892_, v_i_5893_);
lean_inc_ref(v___y_5891_);
lean_inc_ref(v___y_5898_);
lean_inc(v___y_5896_);
lean_inc(v___x_5901_);
v___x_5902_ = lean_apply_5(v___y_5891_, v___x_5901_, v___y_5896_, v___y_5897_, v___y_5898_, lean_box(0));
if (lean_obj_tag(v___x_5902_) == 0)
{
lean_object* v_a_5903_; lean_object* v_fst_5904_; lean_object* v_snd_5905_; size_t v___x_5906_; size_t v___x_5907_; 
v_a_5903_ = lean_ctor_get(v___x_5902_, 0);
lean_inc(v_a_5903_);
lean_dec_ref(v___x_5902_);
v_fst_5904_ = lean_ctor_get(v_a_5903_, 0);
lean_inc(v_fst_5904_);
v_snd_5905_ = lean_ctor_get(v_a_5903_, 1);
lean_inc(v_snd_5905_);
lean_dec(v_a_5903_);
v___x_5906_ = ((size_t)1ULL);
v___x_5907_ = lean_usize_add(v_i_5893_, v___x_5906_);
v_i_5893_ = v___x_5907_;
v_b_5895_ = v_fst_5904_;
v___y_5897_ = v_snd_5905_;
goto _start;
}
else
{
lean_dec_ref(v___y_5891_);
return v___x_5902_;
}
}
else
{
lean_object* v___x_5909_; lean_object* v___x_5910_; 
lean_dec_ref(v___y_5891_);
v___x_5909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5909_, 0, v_b_5895_);
lean_ctor_set(v___x_5909_, 1, v___y_5897_);
v___x_5910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5909_);
return v___x_5910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v___y_5911_, lean_object* v_as_5912_, lean_object* v_i_5913_, lean_object* v_stop_5914_, lean_object* v_b_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_){
_start:
{
size_t v_i_boxed_5920_; size_t v_stop_boxed_5921_; lean_object* v_res_5922_; 
v_i_boxed_5920_ = lean_unbox_usize(v_i_5913_);
lean_dec(v_i_5913_);
v_stop_boxed_5921_ = lean_unbox_usize(v_stop_5914_);
lean_dec(v_stop_5914_);
v_res_5922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_5911_, v_as_5912_, v_i_boxed_5920_, v_stop_boxed_5921_, v_b_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5916_);
lean_dec_ref(v_as_5912_);
return v_res_5922_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_, lean_object* v_leanOpts_5926_, uint8_t v_reconfigure_5927_, lean_object* v_pkg_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v___y_5931_){
_start:
{
lean_object* v_packages_5933_; lean_object* v_depConfigs_5934_; lean_object* v___x_5935_; lean_object* v_snd_5937_; lean_object* v_packages_5938_; lean_object* v___y_5939_; lean_object* v_____x_5955_; lean_object* v___y_5956_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; uint8_t v___x_5962_; 
v_packages_5933_ = lean_ctor_get(v_a_5930_, 5);
v_depConfigs_5934_ = lean_ctor_get(v_pkg_5928_, 12);
lean_inc_ref(v_depConfigs_5934_);
v___x_5935_ = lean_array_get_size(v_packages_5933_);
v___x_5959_ = lean_array_get_size(v_depConfigs_5934_);
v___x_5960_ = lean_unsigned_to_nat(0u);
v___x_5961_ = lean_box(0);
v___x_5962_ = lean_nat_dec_le(v___x_5959_, v___x_5959_);
if (v___x_5962_ == 0)
{
uint8_t v___x_5963_; 
v___x_5963_ = lean_nat_dec_lt(v___x_5960_, v___x_5959_);
if (v___x_5963_ == 0)
{
uint8_t v___x_5964_; 
lean_dec_ref(v_depConfigs_5934_);
lean_dec_ref(v_pkg_5928_);
lean_dec_ref(v_leanOpts_5926_);
lean_dec_ref(v___y_5924_);
v___x_5964_ = lean_nat_dec_lt(v___x_5935_, v___x_5935_);
if (v___x_5964_ == 0)
{
lean_object* v___x_5965_; lean_object* v___x_5966_; 
lean_dec_ref(v___y_5925_);
v___x_5965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5961_);
lean_ctor_set(v___x_5965_, 1, v_a_5930_);
v___x_5966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5965_);
return v___x_5966_;
}
else
{
uint8_t v___x_5967_; 
v___x_5967_ = lean_nat_dec_le(v___x_5935_, v___x_5935_);
if (v___x_5967_ == 0)
{
if (v___x_5964_ == 0)
{
lean_object* v___x_5968_; lean_object* v___x_5969_; 
lean_dec_ref(v___y_5925_);
v___x_5968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5961_);
lean_ctor_set(v___x_5968_, 1, v_a_5930_);
v___x_5969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
return v___x_5969_;
}
else
{
size_t v___x_5970_; lean_object* v___x_5971_; 
lean_inc_ref(v_packages_5933_);
v___x_5970_ = lean_usize_of_nat(v___x_5935_);
v___x_5971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_5925_, v_packages_5933_, v___x_5970_, v___x_5970_, v___x_5961_, v_a_5929_, v_a_5930_, v___y_5931_);
lean_dec_ref(v_packages_5933_);
return v___x_5971_;
}
}
else
{
size_t v___x_5972_; lean_object* v___x_5973_; 
lean_inc_ref(v_packages_5933_);
v___x_5972_ = lean_usize_of_nat(v___x_5935_);
v___x_5973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_5925_, v_packages_5933_, v___x_5972_, v___x_5972_, v___x_5961_, v_a_5929_, v_a_5930_, v___y_5931_);
lean_dec_ref(v_packages_5933_);
return v___x_5973_;
}
}
}
else
{
size_t v___x_5974_; size_t v___x_5975_; lean_object* v___x_5976_; 
v___x_5974_ = lean_usize_of_nat(v___x_5959_);
v___x_5975_ = ((size_t)0ULL);
v___x_5976_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5928_, v___y_5923_, v___y_5924_, v_leanOpts_5926_, v_reconfigure_5927_, v_depConfigs_5934_, v___x_5974_, v___x_5975_, v___x_5961_, v_a_5930_, v___y_5931_);
lean_dec_ref(v_depConfigs_5934_);
if (lean_obj_tag(v___x_5976_) == 0)
{
lean_object* v_a_5977_; 
v_a_5977_ = lean_ctor_get(v___x_5976_, 0);
lean_inc(v_a_5977_);
lean_dec_ref(v___x_5976_);
v_____x_5955_ = v_a_5977_;
v___y_5956_ = v___y_5931_;
goto v___jp_5954_;
}
else
{
lean_dec_ref(v___y_5925_);
return v___x_5976_;
}
}
}
else
{
uint8_t v___x_5978_; 
v___x_5978_ = lean_nat_dec_lt(v___x_5960_, v___x_5959_);
if (v___x_5978_ == 0)
{
lean_inc_ref(v_packages_5933_);
lean_dec_ref(v_depConfigs_5934_);
lean_dec_ref(v_pkg_5928_);
lean_dec_ref(v_leanOpts_5926_);
lean_dec_ref(v___y_5924_);
v_snd_5937_ = v_a_5930_;
v_packages_5938_ = v_packages_5933_;
v___y_5939_ = v___y_5931_;
goto v___jp_5936_;
}
else
{
size_t v___x_5979_; size_t v___x_5980_; lean_object* v___x_5981_; 
v___x_5979_ = lean_usize_of_nat(v___x_5959_);
v___x_5980_ = ((size_t)0ULL);
v___x_5981_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5928_, v___y_5923_, v___y_5924_, v_leanOpts_5926_, v_reconfigure_5927_, v_depConfigs_5934_, v___x_5979_, v___x_5980_, v___x_5961_, v_a_5930_, v___y_5931_);
lean_dec_ref(v_depConfigs_5934_);
if (lean_obj_tag(v___x_5981_) == 0)
{
lean_object* v_a_5982_; 
v_a_5982_ = lean_ctor_get(v___x_5981_, 0);
lean_inc(v_a_5982_);
lean_dec_ref(v___x_5981_);
v_____x_5955_ = v_a_5982_;
v___y_5956_ = v___y_5931_;
goto v___jp_5954_;
}
else
{
lean_dec_ref(v___y_5925_);
return v___x_5981_;
}
}
}
v___jp_5936_:
{
lean_object* v___x_5940_; lean_object* v___x_5941_; uint8_t v___x_5942_; 
v___x_5940_ = lean_array_get_size(v_packages_5938_);
v___x_5941_ = lean_box(0);
v___x_5942_ = lean_nat_dec_lt(v___x_5935_, v___x_5940_);
if (v___x_5942_ == 0)
{
lean_object* v___x_5943_; lean_object* v___x_5944_; 
lean_dec_ref(v_packages_5938_);
lean_dec_ref(v___y_5925_);
v___x_5943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5943_, 0, v___x_5941_);
lean_ctor_set(v___x_5943_, 1, v_snd_5937_);
v___x_5944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5943_);
return v___x_5944_;
}
else
{
uint8_t v___x_5945_; 
v___x_5945_ = lean_nat_dec_le(v___x_5940_, v___x_5940_);
if (v___x_5945_ == 0)
{
if (v___x_5942_ == 0)
{
lean_object* v___x_5946_; lean_object* v___x_5947_; 
lean_dec_ref(v_packages_5938_);
lean_dec_ref(v___y_5925_);
v___x_5946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5941_);
lean_ctor_set(v___x_5946_, 1, v_snd_5937_);
v___x_5947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5947_, 0, v___x_5946_);
return v___x_5947_;
}
else
{
size_t v___x_5948_; size_t v___x_5949_; lean_object* v___x_5950_; 
v___x_5948_ = lean_usize_of_nat(v___x_5935_);
v___x_5949_ = lean_usize_of_nat(v___x_5940_);
v___x_5950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_5925_, v_packages_5938_, v___x_5948_, v___x_5949_, v___x_5941_, v_a_5929_, v_snd_5937_, v___y_5939_);
lean_dec_ref(v_packages_5938_);
return v___x_5950_;
}
}
else
{
size_t v___x_5951_; size_t v___x_5952_; lean_object* v___x_5953_; 
v___x_5951_ = lean_usize_of_nat(v___x_5935_);
v___x_5952_ = lean_usize_of_nat(v___x_5940_);
v___x_5953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_5925_, v_packages_5938_, v___x_5951_, v___x_5952_, v___x_5941_, v_a_5929_, v_snd_5937_, v___y_5939_);
lean_dec_ref(v_packages_5938_);
return v___x_5953_;
}
}
}
v___jp_5954_:
{
lean_object* v_snd_5957_; lean_object* v_packages_5958_; 
v_snd_5957_ = lean_ctor_get(v_____x_5955_, 1);
lean_inc(v_snd_5957_);
lean_dec_ref(v_____x_5955_);
v_packages_5958_ = lean_ctor_get(v_snd_5957_, 5);
lean_inc_ref(v_packages_5958_);
v_snd_5937_ = v_snd_5957_;
v_packages_5938_ = v_packages_5958_;
v___y_5939_ = v___y_5956_;
goto v___jp_5936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v_leanOpts_5986_, lean_object* v_reconfigure_5987_, lean_object* v_pkg_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_){
_start:
{
uint8_t v_reconfigure_boxed_5993_; lean_object* v_res_5994_; 
v_reconfigure_boxed_5993_ = lean_unbox(v_reconfigure_5987_);
v_res_5994_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_5983_, v___y_5984_, v___y_5985_, v_leanOpts_5986_, v_reconfigure_boxed_5993_, v_pkg_5988_, v_a_5989_, v_a_5990_, v___y_5991_);
lean_dec_ref(v___y_5991_);
lean_dec(v_a_5989_);
lean_dec(v___y_5983_);
return v_res_5994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(lean_object* v_pkg_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v_leanOpts_5998_, uint8_t v_reconfigure_5999_, lean_object* v_as_6000_, size_t v_i_6001_, size_t v_stop_6002_, lean_object* v_b_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_){
_start:
{
lean_object* v___x_6008_; 
v___x_6008_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5995_, v___y_5996_, v___y_5997_, v_leanOpts_5998_, v_reconfigure_5999_, v_as_6000_, v_i_6001_, v_stop_6002_, v_b_6003_, v___y_6005_, v___y_6006_);
return v___x_6008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___boxed(lean_object* v_pkg_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v_leanOpts_6012_, lean_object* v_reconfigure_6013_, lean_object* v_as_6014_, lean_object* v_i_6015_, lean_object* v_stop_6016_, lean_object* v_b_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
uint8_t v_reconfigure_boxed_6022_; size_t v_i_boxed_6023_; size_t v_stop_boxed_6024_; lean_object* v_res_6025_; 
v_reconfigure_boxed_6022_ = lean_unbox(v_reconfigure_6013_);
v_i_boxed_6023_ = lean_unbox_usize(v_i_6015_);
lean_dec(v_i_6015_);
v_stop_boxed_6024_ = lean_unbox_usize(v_stop_6016_);
lean_dec(v_stop_6016_);
v_res_6025_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_pkg_6009_, v___y_6010_, v___y_6011_, v_leanOpts_6012_, v_reconfigure_boxed_6022_, v_as_6014_, v_i_boxed_6023_, v_stop_boxed_6024_, v_b_6017_, v___y_6018_, v___y_6019_, v___y_6020_);
lean_dec_ref(v___y_6020_);
lean_dec(v___y_6018_);
lean_dec_ref(v_as_6014_);
lean_dec(v___y_6010_);
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v_leanOpts_6028_, uint8_t v_reconfigure_6029_, lean_object* v_a_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_){
_start:
{
lean_object* v___x_6035_; 
v___x_6035_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_6026_, v___y_6027_, v_leanOpts_6028_, v_reconfigure_6029_, v_a_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
return v___x_6035_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3___boxed(lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v_leanOpts_6038_, lean_object* v_reconfigure_6039_, lean_object* v_a_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_){
_start:
{
uint8_t v_reconfigure_boxed_6045_; lean_object* v_res_6046_; 
v_reconfigure_boxed_6045_ = lean_unbox(v_reconfigure_6039_);
v_res_6046_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(v___y_6036_, v___y_6037_, v_leanOpts_6038_, v_reconfigure_boxed_6045_, v_a_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
lean_dec_ref(v___y_6043_);
lean_dec(v___y_6041_);
lean_dec(v___y_6036_);
return v_res_6046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v___y_6047_, lean_object* v___x_6048_, lean_object* v_as_6049_, size_t v_i_6050_, size_t v_stop_6051_, lean_object* v_b_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_){
_start:
{
uint8_t v___x_6056_; 
v___x_6056_ = lean_usize_dec_eq(v_i_6050_, v_stop_6051_);
if (v___x_6056_ == 0)
{
lean_object* v___x_6057_; lean_object* v___x_6058_; 
v___x_6057_ = lean_array_uget_borrowed(v_as_6049_, v_i_6050_);
lean_inc_ref(v___y_6047_);
lean_inc_ref(v___y_6054_);
lean_inc(v___x_6048_);
lean_inc(v___x_6057_);
v___x_6058_ = lean_apply_5(v___y_6047_, v___x_6057_, v___x_6048_, v___y_6053_, v___y_6054_, lean_box(0));
if (lean_obj_tag(v___x_6058_) == 0)
{
lean_object* v_a_6059_; lean_object* v_fst_6060_; lean_object* v_snd_6061_; size_t v___x_6062_; size_t v___x_6063_; 
v_a_6059_ = lean_ctor_get(v___x_6058_, 0);
lean_inc(v_a_6059_);
lean_dec_ref(v___x_6058_);
v_fst_6060_ = lean_ctor_get(v_a_6059_, 0);
lean_inc(v_fst_6060_);
v_snd_6061_ = lean_ctor_get(v_a_6059_, 1);
lean_inc(v_snd_6061_);
lean_dec(v_a_6059_);
v___x_6062_ = ((size_t)1ULL);
v___x_6063_ = lean_usize_add(v_i_6050_, v___x_6062_);
v_i_6050_ = v___x_6063_;
v_b_6052_ = v_fst_6060_;
v___y_6053_ = v_snd_6061_;
goto _start;
}
else
{
lean_dec(v___x_6048_);
lean_dec_ref(v___y_6047_);
return v___x_6058_;
}
}
else
{
lean_object* v___x_6065_; lean_object* v___x_6066_; 
lean_dec(v___x_6048_);
lean_dec_ref(v___y_6047_);
v___x_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6065_, 0, v_b_6052_);
lean_ctor_set(v___x_6065_, 1, v___y_6053_);
v___x_6066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6065_);
return v___x_6066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v___y_6067_, lean_object* v___x_6068_, lean_object* v_as_6069_, lean_object* v_i_6070_, lean_object* v_stop_6071_, lean_object* v_b_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_){
_start:
{
size_t v_i_boxed_6076_; size_t v_stop_boxed_6077_; lean_object* v_res_6078_; 
v_i_boxed_6076_ = lean_unbox_usize(v_i_6070_);
lean_dec(v_i_6070_);
v_stop_boxed_6077_ = lean_unbox_usize(v_stop_6071_);
lean_dec(v_stop_6071_);
v_res_6078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6067_, v___x_6068_, v_as_6069_, v_i_boxed_6076_, v_stop_boxed_6077_, v_b_6072_, v___y_6073_, v___y_6074_);
lean_dec_ref(v___y_6074_);
lean_dec_ref(v_as_6069_);
return v_res_6078_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5(lean_object* v___y_6079_, lean_object* v___x_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v_leanOpts_6083_, uint8_t v_reconfigure_6084_, lean_object* v_pkg_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v___y_6088_){
_start:
{
lean_object* v_packages_6090_; lean_object* v_depConfigs_6091_; lean_object* v___x_6092_; lean_object* v_snd_6094_; lean_object* v_packages_6095_; lean_object* v___y_6096_; lean_object* v_____x_6112_; lean_object* v___y_6113_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; uint8_t v___x_6119_; 
v_packages_6090_ = lean_ctor_get(v_a_6087_, 5);
v_depConfigs_6091_ = lean_ctor_get(v_pkg_6085_, 12);
lean_inc_ref(v_depConfigs_6091_);
v___x_6092_ = lean_array_get_size(v_packages_6090_);
v___x_6116_ = lean_array_get_size(v_depConfigs_6091_);
v___x_6117_ = lean_unsigned_to_nat(0u);
v___x_6118_ = lean_box(0);
v___x_6119_ = lean_nat_dec_le(v___x_6116_, v___x_6116_);
if (v___x_6119_ == 0)
{
uint8_t v___x_6120_; 
v___x_6120_ = lean_nat_dec_lt(v___x_6117_, v___x_6116_);
if (v___x_6120_ == 0)
{
uint8_t v___x_6121_; 
lean_dec_ref(v_depConfigs_6091_);
lean_dec_ref(v_pkg_6085_);
lean_dec_ref(v_leanOpts_6083_);
lean_dec_ref(v___y_6082_);
v___x_6121_ = lean_nat_dec_lt(v___x_6092_, v___x_6092_);
if (v___x_6121_ == 0)
{
lean_object* v___x_6122_; lean_object* v___x_6123_; 
lean_dec(v___x_6080_);
lean_dec_ref(v___y_6079_);
v___x_6122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6118_);
lean_ctor_set(v___x_6122_, 1, v_a_6087_);
v___x_6123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
return v___x_6123_;
}
else
{
uint8_t v___x_6124_; 
v___x_6124_ = lean_nat_dec_le(v___x_6092_, v___x_6092_);
if (v___x_6124_ == 0)
{
if (v___x_6121_ == 0)
{
lean_object* v___x_6125_; lean_object* v___x_6126_; 
lean_dec(v___x_6080_);
lean_dec_ref(v___y_6079_);
v___x_6125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6118_);
lean_ctor_set(v___x_6125_, 1, v_a_6087_);
v___x_6126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6126_, 0, v___x_6125_);
return v___x_6126_;
}
else
{
size_t v___x_6127_; lean_object* v___x_6128_; 
lean_inc_ref(v_packages_6090_);
v___x_6127_ = lean_usize_of_nat(v___x_6092_);
v___x_6128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6079_, v___x_6080_, v_packages_6090_, v___x_6127_, v___x_6127_, v___x_6118_, v_a_6087_, v___y_6088_);
lean_dec_ref(v_packages_6090_);
return v___x_6128_;
}
}
else
{
size_t v___x_6129_; lean_object* v___x_6130_; 
lean_inc_ref(v_packages_6090_);
v___x_6129_ = lean_usize_of_nat(v___x_6092_);
v___x_6130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6079_, v___x_6080_, v_packages_6090_, v___x_6129_, v___x_6129_, v___x_6118_, v_a_6087_, v___y_6088_);
lean_dec_ref(v_packages_6090_);
return v___x_6130_;
}
}
}
else
{
size_t v___x_6131_; size_t v___x_6132_; lean_object* v___x_6133_; 
v___x_6131_ = lean_usize_of_nat(v___x_6116_);
v___x_6132_ = ((size_t)0ULL);
v___x_6133_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_6085_, v___y_6081_, v___y_6082_, v_leanOpts_6083_, v_reconfigure_6084_, v_depConfigs_6091_, v___x_6131_, v___x_6132_, v___x_6118_, v_a_6087_, v___y_6088_);
lean_dec_ref(v_depConfigs_6091_);
if (lean_obj_tag(v___x_6133_) == 0)
{
lean_object* v_a_6134_; 
v_a_6134_ = lean_ctor_get(v___x_6133_, 0);
lean_inc(v_a_6134_);
lean_dec_ref(v___x_6133_);
v_____x_6112_ = v_a_6134_;
v___y_6113_ = v___y_6088_;
goto v___jp_6111_;
}
else
{
lean_dec(v___x_6080_);
lean_dec_ref(v___y_6079_);
return v___x_6133_;
}
}
}
else
{
uint8_t v___x_6135_; 
v___x_6135_ = lean_nat_dec_lt(v___x_6117_, v___x_6116_);
if (v___x_6135_ == 0)
{
lean_inc_ref(v_packages_6090_);
lean_dec_ref(v_depConfigs_6091_);
lean_dec_ref(v_pkg_6085_);
lean_dec_ref(v_leanOpts_6083_);
lean_dec_ref(v___y_6082_);
v_snd_6094_ = v_a_6087_;
v_packages_6095_ = v_packages_6090_;
v___y_6096_ = v___y_6088_;
goto v___jp_6093_;
}
else
{
size_t v___x_6136_; size_t v___x_6137_; lean_object* v___x_6138_; 
v___x_6136_ = lean_usize_of_nat(v___x_6116_);
v___x_6137_ = ((size_t)0ULL);
v___x_6138_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_6085_, v___y_6081_, v___y_6082_, v_leanOpts_6083_, v_reconfigure_6084_, v_depConfigs_6091_, v___x_6136_, v___x_6137_, v___x_6118_, v_a_6087_, v___y_6088_);
lean_dec_ref(v_depConfigs_6091_);
if (lean_obj_tag(v___x_6138_) == 0)
{
lean_object* v_a_6139_; 
v_a_6139_ = lean_ctor_get(v___x_6138_, 0);
lean_inc(v_a_6139_);
lean_dec_ref(v___x_6138_);
v_____x_6112_ = v_a_6139_;
v___y_6113_ = v___y_6088_;
goto v___jp_6111_;
}
else
{
lean_dec(v___x_6080_);
lean_dec_ref(v___y_6079_);
return v___x_6138_;
}
}
}
v___jp_6093_:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; uint8_t v___x_6099_; 
v___x_6097_ = lean_array_get_size(v_packages_6095_);
v___x_6098_ = lean_box(0);
v___x_6099_ = lean_nat_dec_lt(v___x_6092_, v___x_6097_);
if (v___x_6099_ == 0)
{
lean_object* v___x_6100_; lean_object* v___x_6101_; 
lean_dec_ref(v_packages_6095_);
lean_dec(v___x_6080_);
lean_dec_ref(v___y_6079_);
v___x_6100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6098_);
lean_ctor_set(v___x_6100_, 1, v_snd_6094_);
v___x_6101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
return v___x_6101_;
}
else
{
uint8_t v___x_6102_; 
v___x_6102_ = lean_nat_dec_le(v___x_6097_, v___x_6097_);
if (v___x_6102_ == 0)
{
if (v___x_6099_ == 0)
{
lean_object* v___x_6103_; lean_object* v___x_6104_; 
lean_dec_ref(v_packages_6095_);
lean_dec(v___x_6080_);
lean_dec_ref(v___y_6079_);
v___x_6103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6098_);
lean_ctor_set(v___x_6103_, 1, v_snd_6094_);
v___x_6104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
return v___x_6104_;
}
else
{
size_t v___x_6105_; size_t v___x_6106_; lean_object* v___x_6107_; 
v___x_6105_ = lean_usize_of_nat(v___x_6092_);
v___x_6106_ = lean_usize_of_nat(v___x_6097_);
v___x_6107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6079_, v___x_6080_, v_packages_6095_, v___x_6105_, v___x_6106_, v___x_6098_, v_snd_6094_, v___y_6096_);
lean_dec_ref(v_packages_6095_);
return v___x_6107_;
}
}
else
{
size_t v___x_6108_; size_t v___x_6109_; lean_object* v___x_6110_; 
v___x_6108_ = lean_usize_of_nat(v___x_6092_);
v___x_6109_ = lean_usize_of_nat(v___x_6097_);
v___x_6110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6079_, v___x_6080_, v_packages_6095_, v___x_6108_, v___x_6109_, v___x_6098_, v_snd_6094_, v___y_6096_);
lean_dec_ref(v_packages_6095_);
return v___x_6110_;
}
}
}
v___jp_6111_:
{
lean_object* v_snd_6114_; lean_object* v_packages_6115_; 
v_snd_6114_ = lean_ctor_get(v_____x_6112_, 1);
lean_inc(v_snd_6114_);
lean_dec_ref(v_____x_6112_);
v_packages_6115_ = lean_ctor_get(v_snd_6114_, 5);
lean_inc_ref(v_packages_6115_);
v_snd_6094_ = v_snd_6114_;
v_packages_6095_ = v_packages_6115_;
v___y_6096_ = v___y_6113_;
goto v___jp_6093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___boxed(lean_object* v___y_6140_, lean_object* v___x_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v_leanOpts_6144_, lean_object* v_reconfigure_6145_, lean_object* v_pkg_6146_, lean_object* v_a_6147_, lean_object* v_a_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_){
_start:
{
uint8_t v_reconfigure_boxed_6151_; lean_object* v_res_6152_; 
v_reconfigure_boxed_6151_ = lean_unbox(v_reconfigure_6145_);
v_res_6152_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5(v___y_6140_, v___x_6141_, v___y_6142_, v___y_6143_, v_leanOpts_6144_, v_reconfigure_boxed_6151_, v_pkg_6146_, v_a_6147_, v_a_6148_, v___y_6149_);
lean_dec_ref(v___y_6149_);
lean_dec(v_a_6147_);
lean_dec(v___y_6142_);
return v_res_6152_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6(lean_object* v_00_u03b1_6153_, lean_object* v_cycle_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
lean_object* v___x_6159_; 
v___x_6159_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(v_cycle_6154_, v___y_6157_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b1_6160_, lean_object* v_cycle_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_){
_start:
{
lean_object* v_res_6166_; 
v_res_6166_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6(v_00_u03b1_6160_, v_cycle_6161_, v___y_6162_, v___y_6163_, v___y_6164_);
lean_dec_ref(v___y_6164_);
lean_dec_ref(v___y_6163_);
lean_dec(v___y_6162_);
return v_res_6166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7(lean_object* v___y_6167_, lean_object* v___x_6168_, lean_object* v_as_6169_, size_t v_i_6170_, size_t v_stop_6171_, lean_object* v_b_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_){
_start:
{
lean_object* v___x_6177_; 
v___x_6177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6167_, v___x_6168_, v_as_6169_, v_i_6170_, v_stop_6171_, v_b_6172_, v___y_6174_, v___y_6175_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v___y_6178_, lean_object* v___x_6179_, lean_object* v_as_6180_, lean_object* v_i_6181_, lean_object* v_stop_6182_, lean_object* v_b_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_){
_start:
{
size_t v_i_boxed_6188_; size_t v_stop_boxed_6189_; lean_object* v_res_6190_; 
v_i_boxed_6188_ = lean_unbox_usize(v_i_6181_);
lean_dec(v_i_6181_);
v_stop_boxed_6189_ = lean_unbox_usize(v_stop_6182_);
lean_dec(v_stop_6182_);
v_res_6190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7(v___y_6178_, v___x_6179_, v_as_6180_, v_i_boxed_6188_, v_stop_boxed_6189_, v_b_6183_, v___y_6184_, v___y_6185_, v___y_6186_);
lean_dec_ref(v___y_6186_);
lean_dec(v___y_6184_);
lean_dec_ref(v_as_6180_);
return v_res_6190_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7(lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v_leanOpts_6193_, uint8_t v_reconfigure_6194_, lean_object* v_inst_6195_, lean_object* v_a_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_){
_start:
{
lean_object* v___x_6201_; 
v___x_6201_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_6191_, v___y_6192_, v_leanOpts_6193_, v_reconfigure_6194_, v_a_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
return v___x_6201_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___boxed(lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v_leanOpts_6204_, lean_object* v_reconfigure_6205_, lean_object* v_inst_6206_, lean_object* v_a_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
uint8_t v_reconfigure_boxed_6212_; lean_object* v_res_6213_; 
v_reconfigure_boxed_6212_ = lean_unbox(v_reconfigure_6205_);
v_res_6213_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7(v___y_6202_, v___y_6203_, v_leanOpts_6204_, v_reconfigure_boxed_6212_, v_inst_6206_, v_a_6207_, v___y_6208_, v___y_6209_, v___y_6210_);
lean_dec_ref(v___y_6210_);
lean_dec(v___y_6208_);
lean_dec(v___y_6202_);
return v_res_6213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12(lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v_leanOpts_6216_, uint8_t v_reconfigure_6217_, lean_object* v___x_6218_, lean_object* v_as_6219_, size_t v_i_6220_, size_t v_stop_6221_, lean_object* v_b_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_){
_start:
{
lean_object* v___x_6227_; 
v___x_6227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_6214_, v___y_6215_, v_leanOpts_6216_, v_reconfigure_6217_, v___x_6218_, v_as_6219_, v_i_6220_, v_stop_6221_, v_b_6222_, v___y_6224_, v___y_6225_);
return v___x_6227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___boxed(lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v_leanOpts_6230_, lean_object* v_reconfigure_6231_, lean_object* v___x_6232_, lean_object* v_as_6233_, lean_object* v_i_6234_, lean_object* v_stop_6235_, lean_object* v_b_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_){
_start:
{
uint8_t v_reconfigure_boxed_6241_; size_t v_i_boxed_6242_; size_t v_stop_boxed_6243_; lean_object* v_res_6244_; 
v_reconfigure_boxed_6241_ = lean_unbox(v_reconfigure_6231_);
v_i_boxed_6242_ = lean_unbox_usize(v_i_6234_);
lean_dec(v_i_6234_);
v_stop_boxed_6243_ = lean_unbox_usize(v_stop_6235_);
lean_dec(v_stop_6235_);
v_res_6244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12(v___y_6228_, v___y_6229_, v_leanOpts_6230_, v_reconfigure_boxed_6241_, v___x_6232_, v_as_6233_, v_i_boxed_6242_, v_stop_boxed_6243_, v_b_6236_, v___y_6237_, v___y_6238_, v___y_6239_);
lean_dec_ref(v___y_6239_);
lean_dec(v___y_6237_);
lean_dec_ref(v_as_6233_);
lean_dec(v___x_6232_);
lean_dec(v___y_6228_);
return v_res_6244_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_StoreInsts(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Topological(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Materialize(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Package(uint8_t builtin);
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
res = runtime_initialize_Lake_Build_Topological(builtin);
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
lean_object* initialize_Lake_Build_Topological(uint8_t builtin);
lean_object* initialize_Lake_Load_Materialize(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Eval(uint8_t builtin);
lean_object* initialize_Lake_Load_Package(uint8_t builtin);
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
res = initialize_Lake_Build_Topological(builtin);
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

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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_Dependency_materialize(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_PackageEntry_materialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
lean_object* l_Lake_formatCycle___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lake_loadPackageCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_addFacetsFromEnv(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_Manifest_tryLoadEntries(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*);
lean_object* lean_io_rename(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_load(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
lean_object* l_StateT_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instMonadCycleOfMonadCycleOf___redArg(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lake_recFetchAcyclic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Manifest_save(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ": package directory not found: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = ": package requires itself (or a package with the same name)"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__0_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__1_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__2_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__3 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__3_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__4 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__4_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__5 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__5_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__6 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__6_value;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__7 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__7_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__1_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__2_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__8 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__8_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__8_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__3_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__4_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__5_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__6_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__9 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__9_value;
static const lean_ctor_object l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__9_value),((lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__7_value)}};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__10 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = ": ignoring missing manifest '"};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0_value;
static const lean_string_object l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = ": ignoring manifest because it failed to load: "};
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0;
static lean_once_cell_t l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1;
static const lean_closure_object l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__2 = (const lean_object*)&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22_spec__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22_spec__28___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22_spec__28___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22_spec__28(lean_object*, lean_object*);
static const lean_string_object l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22___closed__0 = (const lean_object*)&l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___closed__0 = (const lean_object*)&l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18___redArg(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.Data.DTreeMap.Internal.Balancing"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceR!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceR! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__3;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__4;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.balanceL!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "balanceL! input was not balanced"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__6_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__7;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__12_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ": updating '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "' with "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___redArg(lean_object* v_e_1_){
_start:
{
if (lean_obj_tag(v_e_1_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_a_3_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_e_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_a_3_);
lean_dec(v_e_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_mk_io_user_error(v_a_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set_tag(v___x_5_, 1);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v_a_12_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v_e_1_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_e_1_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set_tag(v___x_14_, 0);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___redArg___boxed(lean_object* v_e_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___redArg(v_e_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0(lean_object* v_00_u03b1_23_, lean_object* v_e_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___redArg(v_e_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___boxed(lean_object* v_00_u03b1_27_, lean_object* v_e_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0(v_00_u03b1_27_, v_e_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(lean_object* v_wsIdx_34_, lean_object* v_dep_35_, lean_object* v_lakeOpts_36_, lean_object* v_leanOpts_37_, uint8_t v_reconfigure_38_, lean_object* v_ws_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_root_42_; lean_object* v_lakeEnv_43_; lean_object* v_dir_44_; lean_object* v_relPkgDir_45_; lean_object* v_remoteUrl_46_; lean_object* v_manifestEntry_47_; lean_object* v_pkgDir_48_; lean_object* v___x_49_; lean_object* v_name_50_; lean_object* v_scope_51_; lean_object* v_configFile_52_; uint8_t v___x_53_; lean_object* v_name_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_root_42_ = lean_ctor_get(v_ws_39_, 0);
v_lakeEnv_43_ = lean_ctor_get(v_ws_39_, 1);
v_dir_44_ = lean_ctor_get(v_root_42_, 4);
v_relPkgDir_45_ = lean_ctor_get(v_dep_35_, 0);
lean_inc_ref(v_relPkgDir_45_);
v_remoteUrl_46_ = lean_ctor_get(v_dep_35_, 1);
lean_inc_ref(v_remoteUrl_46_);
v_manifestEntry_47_ = lean_ctor_get(v_dep_35_, 3);
lean_inc_ref(v_manifestEntry_47_);
lean_dec_ref(v_dep_35_);
lean_inc_ref(v_relPkgDir_45_);
lean_inc_ref(v_dir_44_);
v_pkgDir_48_ = l_Lake_joinRelative(v_dir_44_, v_relPkgDir_45_);
lean_inc_ref(v_pkgDir_48_);
v___x_49_ = l_Lake_resolvePath(v_pkgDir_48_);
v_name_50_ = lean_ctor_get(v_manifestEntry_47_, 0);
lean_inc(v_name_50_);
v_scope_51_ = lean_ctor_get(v_manifestEntry_47_, 1);
lean_inc_ref(v_scope_51_);
v_configFile_52_ = lean_ctor_get(v_manifestEntry_47_, 2);
lean_inc_ref(v_configFile_52_);
lean_dec_ref(v_manifestEntry_47_);
v___x_53_ = 0;
lean_inc(v_name_50_);
v_name_54_ = l_Lean_Name_toString(v_name_50_, v___x_53_);
v___x_55_ = lean_string_utf8_byte_size(v___x_49_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_nat_dec_eq(v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec_ref(v_pkgDir_48_);
v___x_58_ = lean_box(0);
lean_inc_ref(v_configFile_52_);
lean_inc_ref(v___x_49_);
v___x_59_ = l_Lake_joinRelative(v___x_49_, v_configFile_52_);
v___x_60_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__0));
v___x_61_ = 1;
lean_inc_ref(v_leanOpts_37_);
lean_inc_ref(v_dir_44_);
lean_inc_ref(v_lakeEnv_43_);
v___x_62_ = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(v___x_62_, 0, v_lakeEnv_43_);
lean_ctor_set(v___x_62_, 1, v___x_58_);
lean_ctor_set(v___x_62_, 2, v_dir_44_);
lean_ctor_set(v___x_62_, 3, v_wsIdx_34_);
lean_ctor_set(v___x_62_, 4, v_name_50_);
lean_ctor_set(v___x_62_, 5, v_relPkgDir_45_);
lean_ctor_set(v___x_62_, 6, v___x_49_);
lean_ctor_set(v___x_62_, 7, v_configFile_52_);
lean_ctor_set(v___x_62_, 8, v___x_59_);
lean_ctor_set(v___x_62_, 9, v___x_60_);
lean_ctor_set(v___x_62_, 10, v_lakeOpts_36_);
lean_ctor_set(v___x_62_, 11, v_leanOpts_37_);
lean_ctor_set(v___x_62_, 12, v_scope_51_);
lean_ctor_set(v___x_62_, 13, v_remoteUrl_46_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*14, v_reconfigure_38_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*14 + 1, v___x_53_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*14 + 2, v___x_61_);
v___x_63_ = l_Lake_loadPackageCore(v_name_54_, v___x_62_, v_a_40_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v_snd_65_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
v_snd_65_ = lean_ctor_get(v_a_64_, 1);
if (lean_obj_tag(v_snd_65_) == 1)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_95_; 
lean_inc_ref(v_snd_65_);
v_a_66_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v___x_63_, 0);
lean_dec(v_unused_96_);
v___x_68_ = v___x_63_;
v_isShared_69_ = v_isSharedCheck_95_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_63_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_95_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_fst_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_93_; 
v_fst_70_ = lean_ctor_get(v_a_64_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v_a_64_, 1);
lean_dec(v_unused_94_);
v___x_72_ = v_a_64_;
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_fst_70_);
lean_dec(v_a_64_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_val_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_val_74_ = lean_ctor_get(v_snd_65_, 0);
lean_inc(v_val_74_);
lean_dec_ref(v_snd_65_);
v___x_75_ = l_Lake_Workspace_addFacetsFromEnv(v_val_74_, v_leanOpts_37_, v_ws_39_);
lean_dec_ref(v_leanOpts_37_);
v___x_76_ = l_IO_ofExcept___at___00__private_Lake_Load_Resolve_0__Lake_loadDepPackage_spec__0___redArg(v___x_75_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref(v___x_76_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v_a_77_);
v___x_79_ = v___x_72_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_fst_70_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_a_77_);
v___x_79_ = v_reuseFailAlloc_83_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_81_; 
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_79_);
v___x_81_ = v___x_68_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_a_66_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
else
{
lean_object* v_a_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
lean_del_object(v___x_72_);
lean_dec(v_fst_70_);
v_a_84_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_84_);
lean_dec_ref(v___x_76_);
v___x_85_ = lean_io_error_to_string(v_a_84_);
v___x_86_ = 3;
v___x_87_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = lean_array_get_size(v_a_66_);
v___x_89_ = lean_array_push(v_a_66_, v___x_87_);
if (v_isShared_69_ == 0)
{
lean_ctor_set_tag(v___x_68_, 1);
lean_ctor_set(v___x_68_, 1, v___x_89_);
lean_ctor_set(v___x_68_, 0, v___x_88_);
v___x_91_ = v___x_68_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_113_; 
lean_dec_ref(v_leanOpts_37_);
v_a_97_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v___x_63_, 0);
lean_dec(v_unused_114_);
v___x_99_ = v___x_63_;
v_isShared_100_ = v_isSharedCheck_113_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_63_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_113_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_fst_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_111_; 
v_fst_101_ = lean_ctor_get(v_a_64_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v_a_64_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v_a_64_, 1);
lean_dec(v_unused_112_);
v___x_103_ = v_a_64_;
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_fst_101_);
lean_dec(v_a_64_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v_ws_39_);
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_fst_101_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_ws_39_);
v___x_106_ = v_reuseFailAlloc_110_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_108_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_106_);
v___x_108_ = v___x_99_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_a_97_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
}
else
{
lean_object* v_a_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec_ref(v_ws_39_);
lean_dec_ref(v_leanOpts_37_);
v_a_115_ = lean_ctor_get(v___x_63_, 0);
v_a_116_ = lean_ctor_get(v___x_63_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_63_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_inc(v_a_115_);
lean_dec(v___x_63_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_115_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec_ref(v_configFile_52_);
lean_dec_ref(v_scope_51_);
lean_dec(v_name_50_);
lean_dec_ref(v___x_49_);
lean_dec_ref(v_remoteUrl_46_);
lean_dec_ref(v_relPkgDir_45_);
lean_dec_ref(v_ws_39_);
lean_dec_ref(v_leanOpts_37_);
lean_dec(v_lakeOpts_36_);
lean_dec(v_wsIdx_34_);
v___x_124_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__1));
v___x_125_ = lean_string_append(v_name_54_, v___x_124_);
v___x_126_ = lean_string_append(v___x_125_, v_pkgDir_48_);
lean_dec_ref(v_pkgDir_48_);
v___x_127_ = 3;
v___x_128_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_127_);
v___x_129_ = lean_array_get_size(v_a_40_);
v___x_130_ = lean_array_push(v_a_40_, v___x_128_);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___boxed(lean_object* v_wsIdx_132_, lean_object* v_dep_133_, lean_object* v_lakeOpts_134_, lean_object* v_leanOpts_135_, lean_object* v_reconfigure_136_, lean_object* v_ws_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_reconfigure_boxed_140_; lean_object* v_res_141_; 
v_reconfigure_boxed_140_ = lean_unbox(v_reconfigure_136_);
v_res_141_ = l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(v_wsIdx_132_, v_dep_133_, v_lakeOpts_134_, v_leanOpts_135_, v_reconfigure_boxed_140_, v_ws_137_, v_a_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_DepStackT_run___redArg(lean_object* v_x_142_, lean_object* v_stack_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_apply_1(v_x_142_, v_stack_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_DepStackT_run(lean_object* v_m_145_, lean_object* v_00_u03b1_146_, lean_object* v_x_147_, lean_object* v_stack_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_apply_1(v_x_147_, v_stack_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg(lean_object* v_inst_152_, lean_object* v_cycle_153_){
_start:
{
lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___f_154_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__0));
v___x_155_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1));
v___x_156_ = l_Lake_formatCycle___redArg(v___f_154_, v_cycle_153_);
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = lean_apply_2(v_inst_152_, lean_box(0), v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError(lean_object* v_m_159_, lean_object* v_00_u03b1_160_, lean_object* v_inst_161_, lean_object* v_cycle_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg(v_inst_161_, v_cycle_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0(lean_object* v___f_164_, lean_object* v_00_u03b1_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_23__overap_168_; lean_object* v___x_169_; 
v___x_23__overap_168_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg(v___f_164_, v___y_166_);
lean_inc(v___y_167_);
v___x_169_ = lean_apply_1(v___x_23__overap_168_, v___y_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0___boxed(lean_object* v___f_170_, lean_object* v_00_u03b1_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0(v___f_170_, v_00_u03b1_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(lean_object* v_inst_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___x_182_; 
v___x_178_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v_inst_176_);
v___f_179_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___closed__0));
v___f_180_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_180_, 0, v_inst_177_);
lean_closure_set(v___f_180_, 1, v___f_179_);
v___f_181_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_181_, 0, v___f_180_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_178_);
lean_ctor_set(v___x_182_, 1, v___f_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError(lean_object* v_m_183_, lean_object* v_inst_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(v_inst_184_, v_inst_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveT_run___redArg(lean_object* v_ws_187_, lean_object* v_x_188_, lean_object* v_stack_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_apply_2(v_x_188_, v_stack_189_, v_ws_187_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ResolveT_run(lean_object* v_m_191_, lean_object* v_00_u03b1_192_, lean_object* v_ws_193_, lean_object* v_x_194_, lean_object* v_stack_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_apply_2(v_x_194_, v_stack_195_, v_ws_193_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(lean_object* v_x_197_){
_start:
{
lean_object* v_baseName_198_; 
v_baseName_198_ = lean_ctor_get(v_x_197_, 1);
lean_inc(v_baseName_198_);
return v_baseName_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0___boxed(lean_object* v_x_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__0(v_x_199_);
lean_dec_ref(v_x_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1(lean_object* v_toPure_201_, lean_object* v_____x_202_){
_start:
{
lean_object* v_snd_203_; lean_object* v___x_204_; 
v_snd_203_ = lean_ctor_get(v_____x_202_, 1);
lean_inc(v_snd_203_);
lean_dec_ref(v_____x_202_);
v___x_204_ = lean_apply_2(v_toPure_201_, lean_box(0), v_snd_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_ws_209_, lean_object* v_go_210_, lean_object* v_root_211_, lean_object* v_stack_212_){
_start:
{
lean_object* v_toApplicative_213_; lean_object* v_toBind_214_; lean_object* v___f_215_; lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_toPure_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___f_233_; lean_object* v___x_32__overap_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_toApplicative_213_ = lean_ctor_get(v_inst_207_, 0);
lean_inc_ref(v_toApplicative_213_);
v_toBind_214_ = lean_ctor_get(v_inst_207_, 1);
lean_inc(v_toBind_214_);
lean_inc_ref(v_inst_207_);
v___f_215_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_215_, 0, v_inst_207_);
lean_inc_ref(v_inst_207_);
v___f_216_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_216_, 0, v_inst_207_);
lean_inc_ref(v_inst_207_);
v___f_217_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_217_, 0, v_inst_207_);
lean_inc_ref(v_inst_207_);
v___f_218_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_218_, 0, v_inst_207_);
lean_inc_ref(v_inst_207_);
v___x_219_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_219_, 0, lean_box(0));
lean_closure_set(v___x_219_, 1, lean_box(0));
lean_closure_set(v___x_219_, 2, v_inst_207_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___f_215_);
lean_inc_ref(v_inst_207_);
v___x_221_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_221_, 0, lean_box(0));
lean_closure_set(v___x_221_, 1, lean_box(0));
lean_closure_set(v___x_221_, 2, v_inst_207_);
v___x_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
lean_ctor_set(v___x_222_, 2, v___f_216_);
lean_ctor_set(v___x_222_, 3, v___f_217_);
lean_ctor_set(v___x_222_, 4, v___f_218_);
lean_inc_ref(v_inst_207_);
v___x_223_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_223_, 0, lean_box(0));
lean_closure_set(v___x_223_, 1, lean_box(0));
lean_closure_set(v___x_223_, 2, v_inst_207_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
lean_inc_ref(v___x_224_);
v___x_225_ = l_ReaderT_instMonad___redArg(v___x_224_);
v___x_226_ = lean_alloc_closure((void*)(l_StateT_lift), 6, 3);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, lean_box(0));
lean_closure_set(v___x_226_, 2, v_inst_207_);
v___f_227_ = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_227_, 0, v_inst_208_);
lean_closure_set(v___f_227_, 1, v___x_226_);
v___x_228_ = l___private_Lake_Load_Resolve_0__Lake_instMonadCycleOfNameDepStackTOfMonadOfMonadError___redArg(v___x_224_, v___f_227_);
v___x_229_ = l_Lake_instMonadCycleOfMonadCycleOf___redArg(v___x_228_);
v_toPure_230_ = lean_ctor_get(v_toApplicative_213_, 1);
lean_inc(v_toPure_230_);
lean_dec_ref(v_toApplicative_213_);
v___f_231_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__0));
v___x_232_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___closed__1));
v___f_233_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg___lam__1), 2, 1);
lean_closure_set(v___f_233_, 0, v_toPure_230_);
v___x_32__overap_234_ = l_Lake_recFetchAcyclic___redArg(v___x_232_, v___x_225_, v___x_229_, v___f_231_, v_go_210_, v_root_211_);
v___x_235_ = lean_apply_2(v___x_32__overap_234_, v_stack_212_, v_ws_209_);
v___x_236_ = lean_apply_4(v_toBind_214_, lean_box(0), lean_box(0), v___x_235_, v___f_233_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT(lean_object* v_m_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_ws_240_, lean_object* v_go_241_, lean_object* v_root_242_, lean_object* v_stack_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(v_inst_238_, v_inst_239_, v_ws_240_, v_go_241_, v_root_242_, v_stack_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0(lean_object* v_toPure_245_, lean_object* v_____x_246_){
_start:
{
lean_object* v_fst_247_; lean_object* v_snd_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_258_; 
v_fst_247_ = lean_ctor_get(v_____x_246_, 0);
v_snd_248_ = lean_ctor_get(v_____x_246_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_____x_246_);
if (v_isSharedCheck_258_ == 0)
{
v___x_250_ = v_____x_246_;
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_snd_248_);
lean_inc(v_fst_247_);
lean_dec(v_____x_246_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_252_ = lean_box(0);
v___x_253_ = l_Lake_Workspace_addPackage(v_fst_247_, v_snd_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v___x_253_);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_253_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_apply_2(v_toPure_245_, lean_box(0), v___x_255_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_baseName_261_; lean_object* v_name_262_; uint8_t v___x_263_; 
v_baseName_261_ = lean_ctor_get(v_x_260_, 1);
v_name_262_ = lean_ctor_get(v_a_259_, 0);
v___x_263_ = lean_name_eq(v_baseName_261_, v_name_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed(lean_object* v_a_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1(v_a_264_, v_x_265_);
lean_dec_ref(v_x_265_);
lean_dec_ref(v_a_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(lean_object* v_load_268_, lean_object* v_pkg_269_, lean_object* v_a_270_, lean_object* v___x_271_, lean_object* v_toBind_272_, lean_object* v___f_273_, lean_object* v_____r_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_apply_4(v_load_268_, v_pkg_269_, v_a_270_, v___x_271_, v___y_276_);
v___x_278_ = lean_apply_4(v_toBind_272_, lean_box(0), lean_box(0), v___x_277_, v___f_273_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed(lean_object* v_load_279_, lean_object* v_pkg_280_, lean_object* v_a_281_, lean_object* v___x_282_, lean_object* v_toBind_283_, lean_object* v___f_284_, lean_object* v_____r_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_load_279_, v_pkg_280_, v_a_281_, v___x_282_, v_toBind_283_, v___f_284_, v_____r_285_, v___y_286_, v___y_287_);
lean_dec(v___y_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(lean_object* v___f_289_, lean_object* v___y_290_, lean_object* v_____x_291_){
_start:
{
lean_object* v_fst_292_; lean_object* v_snd_293_; lean_object* v___x_294_; 
v_fst_292_ = lean_ctor_get(v_____x_291_, 0);
lean_inc(v_fst_292_);
v_snd_293_ = lean_ctor_get(v_____x_291_, 1);
lean_inc(v_snd_293_);
lean_dec_ref(v_____x_291_);
lean_inc(v___y_290_);
v___x_294_ = lean_apply_3(v___f_289_, v_fst_292_, v___y_290_, v_snd_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed(lean_object* v___f_295_, lean_object* v___y_296_, lean_object* v_____x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3(v___f_295_, v___y_296_, v_____x_297_);
lean_dec(v___y_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4(lean_object* v_snd_299_, lean_object* v_toPure_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_302_, 0, v_a_301_);
lean_ctor_set(v___x_302_, 1, v_snd_299_);
v___x_303_ = lean_apply_2(v_toPure_300_, lean_box(0), v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(lean_object* v_load_324_, lean_object* v_pkg_325_, lean_object* v_a_326_, lean_object* v_toBind_327_, lean_object* v___f_328_, lean_object* v___y_329_, lean_object* v_inst_330_, lean_object* v_toPure_331_, lean_object* v___f_332_, lean_object* v_____x_333_){
_start:
{
lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_370_; 
v_fst_334_ = lean_ctor_get(v_____x_333_, 0);
v_snd_335_ = lean_ctor_get(v_____x_333_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_____x_333_);
if (v_isSharedCheck_370_ == 0)
{
v___x_337_ = v_____x_333_;
v_isShared_338_ = v_isSharedCheck_370_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_snd_335_);
lean_inc(v_fst_334_);
lean_dec(v_____x_333_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_370_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_packages_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___f_343_; uint8_t v___y_345_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_packages_339_ = lean_ctor_get(v_fst_334_, 5);
lean_inc_ref(v_packages_339_);
lean_dec(v_fst_334_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_array_get_size(v_packages_339_);
lean_inc(v___f_328_);
lean_inc(v_toBind_327_);
lean_inc_ref(v_a_326_);
lean_inc_ref(v_pkg_325_);
lean_inc(v_load_324_);
v___f_342_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2___boxed), 9, 6);
lean_closure_set(v___f_342_, 0, v_load_324_);
lean_closure_set(v___f_342_, 1, v_pkg_325_);
lean_closure_set(v___f_342_, 2, v_a_326_);
lean_closure_set(v___f_342_, 3, v___x_341_);
lean_closure_set(v___f_342_, 4, v_toBind_327_);
lean_closure_set(v___f_342_, 5, v___f_328_);
lean_inc(v___y_329_);
v___f_343_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_343_, 0, v___f_342_);
lean_closure_set(v___f_343_, 1, v___y_329_);
v___x_358_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__10));
v___x_359_ = lean_nat_dec_lt(v___x_340_, v___x_341_);
if (v___x_359_ == 0)
{
lean_dec_ref(v_packages_339_);
lean_del_object(v___x_337_);
lean_dec_ref(v___f_332_);
v___y_345_ = v___x_359_;
goto v___jp_344_;
}
else
{
if (v___x_359_ == 0)
{
lean_dec_ref(v_packages_339_);
lean_del_object(v___x_337_);
lean_dec_ref(v___f_332_);
v___y_345_ = v___x_359_;
goto v___jp_344_;
}
else
{
size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_360_ = ((size_t)0ULL);
v___x_361_ = lean_usize_of_nat(v___x_341_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_358_, v___f_332_, v_packages_339_, v___x_360_, v___x_361_);
v___x_363_ = lean_unbox(v___x_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
lean_del_object(v___x_337_);
v___x_364_ = lean_unbox(v___x_362_);
lean_dec(v___x_362_);
v___y_345_ = v___x_364_;
goto v___jp_344_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_dec(v___x_362_);
lean_dec_ref(v___f_343_);
lean_dec(v_inst_330_);
lean_dec(v___f_328_);
lean_dec(v_toBind_327_);
lean_dec_ref(v_a_326_);
lean_dec_ref(v_pkg_325_);
lean_dec(v_load_324_);
v___x_365_ = lean_box(0);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_365_);
v___x_367_ = v___x_337_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_snd_335_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; 
v___x_368_ = lean_apply_2(v_toPure_331_, lean_box(0), v___x_367_);
return v___x_368_;
}
}
}
}
v___jp_344_:
{
lean_object* v_baseName_346_; lean_object* v_name_347_; uint8_t v___x_348_; 
v_baseName_346_ = lean_ctor_get(v_pkg_325_, 1);
v_name_347_ = lean_ctor_get(v_a_326_, 0);
v___x_348_ = lean_name_eq(v_baseName_346_, v_name_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec_ref(v___f_343_);
lean_dec(v_toPure_331_);
lean_dec(v_inst_330_);
v___x_349_ = lean_box(0);
v___x_350_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__2(v_load_324_, v_pkg_325_, v_a_326_, v___x_341_, v_toBind_327_, v___f_328_, v___x_349_, v___y_329_, v_snd_335_);
return v___x_350_;
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
lean_inc(v_baseName_346_);
lean_dec(v___f_328_);
lean_dec_ref(v_a_326_);
lean_dec_ref(v_pkg_325_);
lean_dec(v_load_324_);
v___x_351_ = l_Lean_Name_toString(v_baseName_346_, v___y_345_);
v___x_352_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__0));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
v___x_354_ = lean_apply_2(v_inst_330_, lean_box(0), v___x_353_);
v___f_355_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__4), 3, 2);
lean_closure_set(v___f_355_, 0, v_snd_335_);
lean_closure_set(v___f_355_, 1, v_toPure_331_);
lean_inc(v_toBind_327_);
v___x_356_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v___x_354_, v___f_355_);
v___x_357_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v___x_356_, v___f_343_);
return v___x_357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed(lean_object* v_load_371_, lean_object* v_pkg_372_, lean_object* v_a_373_, lean_object* v_toBind_374_, lean_object* v___f_375_, lean_object* v___y_376_, lean_object* v_inst_377_, lean_object* v_toPure_378_, lean_object* v___f_379_, lean_object* v_____x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5(v_load_371_, v_pkg_372_, v_a_373_, v_toBind_374_, v___f_375_, v___y_376_, v_inst_377_, v_toPure_378_, v___f_379_, v_____x_380_);
lean_dec(v___y_376_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6(lean_object* v_toPure_382_, lean_object* v_____x_383_){
_start:
{
lean_object* v_fst_384_; lean_object* v_snd_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_fst_384_ = lean_ctor_get(v_____x_383_, 0);
v_snd_385_ = lean_ctor_get(v_____x_383_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v_____x_383_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v_____x_383_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snd_385_);
lean_inc(v_fst_384_);
lean_dec(v_____x_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_fst_384_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_snd_385_);
v___x_390_ = v_reuseFailAlloc_392_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; 
v___x_391_ = lean_apply_2(v_toPure_382_, lean_box(0), v___x_390_);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7(lean_object* v_toPure_394_, lean_object* v_____x_395_){
_start:
{
lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_fst_396_ = lean_ctor_get(v_____x_395_, 0);
v_snd_397_ = lean_ctor_get(v_____x_395_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_____x_395_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v_____x_395_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snd_397_);
lean_inc(v_fst_396_);
lean_dec(v_____x_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_fst_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_snd_397_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_apply_2(v_toPure_394_, lean_box(0), v___x_402_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(lean_object* v_load_406_, lean_object* v_pkg_407_, lean_object* v_toBind_408_, lean_object* v___f_409_, lean_object* v_inst_410_, lean_object* v_toPure_411_, lean_object* v_a_412_, lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_inc_ref(v_a_412_);
v___f_416_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_416_, 0, v_a_412_);
lean_inc(v_toPure_411_);
lean_inc(v___y_414_);
lean_inc(v_toBind_408_);
v___f_417_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_417_, 0, v_load_406_);
lean_closure_set(v___f_417_, 1, v_pkg_407_);
lean_closure_set(v___f_417_, 2, v_a_412_);
lean_closure_set(v___f_417_, 3, v_toBind_408_);
lean_closure_set(v___f_417_, 4, v___f_409_);
lean_closure_set(v___f_417_, 5, v___y_414_);
lean_closure_set(v___f_417_, 6, v_inst_410_);
lean_closure_set(v___f_417_, 7, v_toPure_411_);
lean_closure_set(v___f_417_, 8, v___f_416_);
lean_inc(v_toPure_411_);
v___f_418_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(v___f_418_, 0, v_toPure_411_);
lean_inc(v_toPure_411_);
v___f_419_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(v___f_419_, 0, v_toPure_411_);
lean_inc_ref(v___y_415_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___y_415_);
lean_ctor_set(v___x_420_, 1, v___y_415_);
v___x_421_ = lean_apply_2(v_toPure_411_, lean_box(0), v___x_420_);
lean_inc(v_toBind_408_);
v___x_422_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_421_, v___f_419_);
lean_inc(v_toBind_408_);
v___x_423_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_422_, v___f_418_);
v___x_424_ = lean_apply_4(v_toBind_408_, lean_box(0), lean_box(0), v___x_423_, v___f_417_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed(lean_object* v_load_425_, lean_object* v_pkg_426_, lean_object* v_toBind_427_, lean_object* v___f_428_, lean_object* v_inst_429_, lean_object* v_toPure_430_, lean_object* v_a_431_, lean_object* v_x_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8(v_load_425_, v_pkg_426_, v_toBind_427_, v___f_428_, v_inst_429_, v_toPure_430_, v_a_431_, v_x_432_, v___y_433_, v___y_434_);
lean_dec(v___y_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(lean_object* v_recurse_436_, lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_441_; 
lean_inc(v___y_439_);
v___x_441_ = lean_apply_3(v_recurse_436_, v___y_438_, v___y_439_, v___y_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed(lean_object* v_recurse_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9(v_recurse_442_, v_x_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(lean_object* v___x_448_, lean_object* v_toPure_449_, lean_object* v___x_450_, lean_object* v___f_451_, lean_object* v_a_452_, lean_object* v_____x_453_){
_start:
{
lean_object* v_fst_454_; lean_object* v_snd_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_480_; 
v_fst_454_ = lean_ctor_get(v_____x_453_, 0);
v_snd_455_ = lean_ctor_get(v_____x_453_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_____x_453_);
if (v_isSharedCheck_480_ == 0)
{
v___x_457_ = v_____x_453_;
v_isShared_458_ = v_isSharedCheck_480_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_snd_455_);
lean_inc(v_fst_454_);
lean_dec(v_____x_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_480_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_packages_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_packages_459_ = lean_ctor_get(v_fst_454_, 5);
lean_inc_ref(v_packages_459_);
lean_dec(v_fst_454_);
v___x_460_ = lean_array_get_size(v_packages_459_);
v___x_461_ = lean_box(0);
v___x_462_ = lean_nat_dec_lt(v___x_448_, v___x_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_464_; 
lean_dec_ref(v_packages_459_);
lean_dec(v___f_451_);
lean_dec_ref(v___x_450_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_461_);
v___x_464_ = v___x_457_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_snd_455_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; 
v___x_465_ = lean_apply_2(v_toPure_449_, lean_box(0), v___x_464_);
return v___x_465_;
}
}
else
{
uint8_t v___x_467_; 
v___x_467_ = lean_nat_dec_le(v___x_460_, v___x_460_);
if (v___x_467_ == 0)
{
if (v___x_462_ == 0)
{
lean_object* v___x_469_; 
lean_dec_ref(v_packages_459_);
lean_dec(v___f_451_);
lean_dec_ref(v___x_450_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_461_);
v___x_469_ = v___x_457_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_snd_455_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_apply_2(v_toPure_449_, lean_box(0), v___x_469_);
return v___x_470_;
}
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_5190__overap_474_; lean_object* v___x_475_; 
lean_del_object(v___x_457_);
lean_dec(v_toPure_449_);
v___x_472_ = lean_usize_of_nat(v___x_448_);
v___x_473_ = lean_usize_of_nat(v___x_460_);
v___x_5190__overap_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_450_, v___f_451_, v_packages_459_, v___x_472_, v___x_473_, v___x_461_);
lean_inc(v_a_452_);
v___x_475_ = lean_apply_2(v___x_5190__overap_474_, v_a_452_, v_snd_455_);
return v___x_475_;
}
}
else
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_5193__overap_478_; lean_object* v___x_479_; 
lean_del_object(v___x_457_);
lean_dec(v_toPure_449_);
v___x_476_ = lean_usize_of_nat(v___x_448_);
v___x_477_ = lean_usize_of_nat(v___x_460_);
v___x_5193__overap_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_450_, v___f_451_, v_packages_459_, v___x_476_, v___x_477_, v___x_461_);
lean_inc(v_a_452_);
v___x_479_ = lean_apply_2(v___x_5193__overap_478_, v_a_452_, v_snd_455_);
return v___x_479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed(lean_object* v___x_481_, lean_object* v_toPure_482_, lean_object* v___x_483_, lean_object* v___f_484_, lean_object* v_a_485_, lean_object* v_____x_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10(v___x_481_, v_toPure_482_, v___x_483_, v___f_484_, v_a_485_, v_____x_486_);
lean_dec(v_a_485_);
lean_dec(v___x_481_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13(lean_object* v_toPure_488_, lean_object* v_toBind_489_, lean_object* v___f_490_, lean_object* v_____x_491_){
_start:
{
lean_object* v_snd_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_505_; 
v_snd_492_ = lean_ctor_get(v_____x_491_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_____x_491_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_____x_491_, 0);
lean_dec(v_unused_506_);
v___x_494_ = v_____x_491_;
v_isShared_495_ = v_isSharedCheck_505_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snd_492_);
lean_dec(v_____x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_505_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___x_499_; 
lean_inc(v_toPure_488_);
v___f_496_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(v___f_496_, 0, v_toPure_488_);
lean_inc(v_toPure_488_);
v___f_497_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(v___f_497_, 0, v_toPure_488_);
lean_inc(v_snd_492_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_snd_492_);
v___x_499_ = v___x_494_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_snd_492_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_snd_492_);
v___x_499_ = v_reuseFailAlloc_504_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = lean_apply_2(v_toPure_488_, lean_box(0), v___x_499_);
lean_inc(v_toBind_489_);
v___x_501_ = lean_apply_4(v_toBind_489_, lean_box(0), lean_box(0), v___x_500_, v___f_497_);
lean_inc(v_toBind_489_);
v___x_502_ = lean_apply_4(v_toBind_489_, lean_box(0), lean_box(0), v___x_501_, v___f_496_);
v___x_503_ = lean_apply_4(v_toBind_489_, lean_box(0), lean_box(0), v___x_502_, v___f_490_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(lean_object* v_pkg_507_, lean_object* v_toPure_508_, lean_object* v___x_509_, lean_object* v___f_510_, lean_object* v_a_511_, lean_object* v_toBind_512_, lean_object* v___f_513_, lean_object* v_____x_514_){
_start:
{
lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_539_; 
v_fst_515_ = lean_ctor_get(v_____x_514_, 0);
v_snd_516_ = lean_ctor_get(v_____x_514_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_____x_514_);
if (v_isSharedCheck_539_ == 0)
{
v___x_518_ = v_____x_514_;
v_isShared_519_ = v_isSharedCheck_539_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_snd_516_);
lean_inc(v_fst_515_);
lean_dec(v_____x_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_539_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v_packages_520_; lean_object* v_depConfigs_521_; lean_object* v___x_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_packages_520_ = lean_ctor_get(v_fst_515_, 5);
lean_inc_ref(v_packages_520_);
lean_dec(v_fst_515_);
v_depConfigs_521_ = lean_ctor_get(v_pkg_507_, 12);
lean_inc_ref(v_depConfigs_521_);
lean_dec_ref(v_pkg_507_);
v___x_522_ = lean_array_get_size(v_packages_520_);
lean_dec_ref(v_packages_520_);
lean_inc(v_a_511_);
lean_inc_ref(v___x_509_);
lean_inc(v_toPure_508_);
v___f_523_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__10___boxed), 6, 5);
lean_closure_set(v___f_523_, 0, v___x_522_);
lean_closure_set(v___f_523_, 1, v_toPure_508_);
lean_closure_set(v___f_523_, 2, v___x_509_);
lean_closure_set(v___f_523_, 3, v___f_510_);
lean_closure_set(v___f_523_, 4, v_a_511_);
lean_inc(v_toBind_512_);
lean_inc(v_toPure_508_);
v___f_524_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__13), 4, 3);
lean_closure_set(v___f_524_, 0, v_toPure_508_);
lean_closure_set(v___f_524_, 1, v_toBind_512_);
lean_closure_set(v___f_524_, 2, v___f_523_);
v___x_525_ = lean_array_get_size(v_depConfigs_521_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_box(0);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_525_);
if (v___x_528_ == 0)
{
lean_object* v___x_530_; 
lean_dec_ref(v_depConfigs_521_);
lean_dec(v___f_513_);
lean_dec_ref(v___x_509_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_527_);
v___x_530_ = v___x_518_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_snd_516_);
v___x_530_ = v_reuseFailAlloc_533_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_apply_2(v_toPure_508_, lean_box(0), v___x_530_);
v___x_532_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_531_, v___f_524_);
return v___x_532_;
}
}
else
{
size_t v___x_534_; size_t v___x_535_; lean_object* v___x_5233__overap_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_del_object(v___x_518_);
lean_dec(v_toPure_508_);
v___x_534_ = lean_usize_of_nat(v___x_525_);
v___x_535_ = ((size_t)0ULL);
v___x_5233__overap_536_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_509_, v___f_513_, v_depConfigs_521_, v___x_534_, v___x_535_, v___x_527_);
lean_inc(v_a_511_);
v___x_537_ = lean_apply_2(v___x_5233__overap_536_, v_a_511_, v_snd_516_);
v___x_538_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_537_, v___f_524_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11___boxed(lean_object* v_pkg_540_, lean_object* v_toPure_541_, lean_object* v___x_542_, lean_object* v___f_543_, lean_object* v_a_544_, lean_object* v_toBind_545_, lean_object* v___f_546_, lean_object* v_____x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11(v_pkg_540_, v_toPure_541_, v___x_542_, v___f_543_, v_a_544_, v_toBind_545_, v___f_546_, v_____x_547_);
lean_dec(v_a_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_load_551_, lean_object* v_pkg_552_, lean_object* v_recurse_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___f_556_; lean_object* v___f_557_; lean_object* v___f_558_; lean_object* v___f_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_toApplicative_567_; lean_object* v_toBind_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_586_; 
lean_inc_ref(v_inst_549_);
v___f_556_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_556_, 0, v_inst_549_);
lean_inc_ref(v_inst_549_);
v___f_557_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_557_, 0, v_inst_549_);
lean_inc_ref(v_inst_549_);
v___f_558_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_558_, 0, v_inst_549_);
lean_inc_ref(v_inst_549_);
v___f_559_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_559_, 0, v_inst_549_);
lean_inc_ref(v_inst_549_);
v___x_560_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_560_, 0, lean_box(0));
lean_closure_set(v___x_560_, 1, lean_box(0));
lean_closure_set(v___x_560_, 2, v_inst_549_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___f_556_);
lean_inc_ref(v_inst_549_);
v___x_562_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_562_, 0, lean_box(0));
lean_closure_set(v___x_562_, 1, lean_box(0));
lean_closure_set(v___x_562_, 2, v_inst_549_);
v___x_563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
lean_ctor_set(v___x_563_, 2, v___f_557_);
lean_ctor_set(v___x_563_, 3, v___f_558_);
lean_ctor_set(v___x_563_, 4, v___f_559_);
lean_inc_ref(v_inst_549_);
v___x_564_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_564_, 0, lean_box(0));
lean_closure_set(v___x_564_, 1, lean_box(0));
lean_closure_set(v___x_564_, 2, v_inst_549_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = l_ReaderT_instMonad___redArg(v___x_565_);
v_toApplicative_567_ = lean_ctor_get(v_inst_549_, 0);
v_toBind_568_ = lean_ctor_get(v_inst_549_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_inst_549_);
if (v_isSharedCheck_586_ == 0)
{
v___x_570_ = v_inst_549_;
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_toBind_568_);
lean_inc(v_toApplicative_567_);
lean_dec(v_inst_549_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_toPure_572_; lean_object* v___f_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___f_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___x_580_; 
v_toPure_572_ = lean_ctor_get(v_toApplicative_567_, 1);
lean_inc(v_toPure_572_);
lean_dec_ref(v_toApplicative_567_);
lean_inc(v_toPure_572_);
v___f_573_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__0), 2, 1);
lean_closure_set(v___f_573_, 0, v_toPure_572_);
lean_inc(v_toPure_572_);
lean_inc(v_toBind_568_);
lean_inc_ref(v_pkg_552_);
v___f_574_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__8___boxed), 10, 6);
lean_closure_set(v___f_574_, 0, v_load_551_);
lean_closure_set(v___f_574_, 1, v_pkg_552_);
lean_closure_set(v___f_574_, 2, v_toBind_568_);
lean_closure_set(v___f_574_, 3, v___f_573_);
lean_closure_set(v___f_574_, 4, v_inst_550_);
lean_closure_set(v___f_574_, 5, v_toPure_572_);
v___f_575_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__9___boxed), 5, 1);
lean_closure_set(v___f_575_, 0, v_recurse_553_);
lean_inc(v_toBind_568_);
lean_inc(v_a_554_);
lean_inc(v_toPure_572_);
v___f_576_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__11___boxed), 8, 7);
lean_closure_set(v___f_576_, 0, v_pkg_552_);
lean_closure_set(v___f_576_, 1, v_toPure_572_);
lean_closure_set(v___f_576_, 2, v___x_566_);
lean_closure_set(v___f_576_, 3, v___f_575_);
lean_closure_set(v___f_576_, 4, v_a_554_);
lean_closure_set(v___f_576_, 5, v_toBind_568_);
lean_closure_set(v___f_576_, 6, v___f_574_);
lean_inc(v_toPure_572_);
v___f_577_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__6), 2, 1);
lean_closure_set(v___f_577_, 0, v_toPure_572_);
lean_inc(v_toPure_572_);
v___f_578_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__7), 2, 1);
lean_closure_set(v___f_578_, 0, v_toPure_572_);
lean_inc_ref(v_a_555_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v_a_555_);
lean_ctor_set(v___x_570_, 0, v_a_555_);
v___x_580_ = v___x_570_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_555_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_a_555_);
v___x_580_ = v_reuseFailAlloc_585_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_apply_2(v_toPure_572_, lean_box(0), v___x_580_);
lean_inc(v_toBind_568_);
v___x_582_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_581_, v___f_578_);
lean_inc(v_toBind_568_);
v___x_583_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_582_, v___f_577_);
v___x_584_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_583_, v___f_576_);
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___boxed(lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_load_589_, lean_object* v_pkg_590_, lean_object* v_recurse_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_587_, v_inst_588_, v_load_589_, v_pkg_590_, v_recurse_591_, v_a_592_, v_a_593_);
lean_dec(v_a_592_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(lean_object* v_m_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_load_598_, lean_object* v_pkg_599_, lean_object* v_recurse_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg(v_inst_596_, v_inst_597_, v_load_598_, v_pkg_599_, v_recurse_600_, v_a_601_, v_a_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed(lean_object* v_m_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_load_607_, lean_object* v_pkg_608_, lean_object* v_recurse_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go(v_m_604_, v_inst_605_, v_inst_606_, v_load_607_, v_pkg_608_, v_recurse_609_, v_a_610_, v_a_611_);
lean_dec(v_a_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore___redArg(lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_ws_615_, lean_object* v_load_616_, lean_object* v_root_617_, lean_object* v_stack_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_inc(v_inst_614_);
lean_inc_ref(v_inst_613_);
v___x_619_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed), 8, 4);
lean_closure_set(v___x_619_, 0, lean_box(0));
lean_closure_set(v___x_619_, 1, v_inst_613_);
lean_closure_set(v___x_619_, 2, v_inst_614_);
lean_closure_set(v___x_619_, 3, v_load_616_);
v___x_620_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(v_inst_613_, v_inst_614_, v_ws_615_, v___x_619_, v_root_617_, v_stack_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore(lean_object* v_m_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_ws_624_, lean_object* v_load_625_, lean_object* v_root_626_, lean_object* v_stack_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_inc(v_inst_623_);
lean_inc_ref(v_inst_622_);
v___x_628_ = lean_alloc_closure((void*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___boxed), 8, 4);
lean_closure_set(v___x_628_, 0, lean_box(0));
lean_closure_set(v___x_628_, 1, v_inst_622_);
lean_closure_set(v___x_628_, 2, v_inst_623_);
lean_closure_set(v___x_628_, 3, v_load_625_);
v___x_629_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___redArg(v_inst_622_, v_inst_623_, v_ws_624_, v___x_628_, v_root_626_, v_stack_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run___redArg(lean_object* v_x_630_, lean_object* v_init_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_apply_1(v_x_630_, v_init_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_UpdateT_run(lean_object* v_m_633_, lean_object* v_00_u03b1_634_, lean_object* v_x_635_, lean_object* v_init_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lean_apply_1(v_x_635_, v_init_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(lean_object* v_toUpdate_638_, lean_object* v_as_639_, size_t v_i_640_, size_t v_stop_641_, lean_object* v_b_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_fst_646_; lean_object* v_snd_647_; uint8_t v___x_653_; 
v___x_653_ = lean_usize_dec_eq(v_i_640_, v_stop_641_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; uint8_t v_inherited_655_; 
v___x_654_ = lean_array_uget_borrowed(v_as_639_, v_i_640_);
v_inherited_655_ = lean_ctor_get_uint8(v___x_654_, sizeof(void*)*5);
if (v_inherited_655_ == 0)
{
lean_object* v_name_656_; uint8_t v___x_657_; 
v_name_656_ = lean_ctor_get(v___x_654_, 0);
v___x_657_ = l_Lean_NameSet_contains(v_toUpdate_638_, v_name_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(0);
lean_inc(v___x_654_);
lean_inc(v_name_656_);
v___x_659_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_656_, v___x_654_, v___y_643_);
v_fst_646_ = v___x_658_;
v_snd_647_ = v___x_659_;
goto v___jp_645_;
}
else
{
goto v___jp_651_;
}
}
else
{
goto v___jp_651_;
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_b_642_);
lean_ctor_set(v___x_660_, 1, v___y_643_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
v___jp_645_:
{
size_t v___x_648_; size_t v___x_649_; 
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_640_, v___x_648_);
v_i_640_ = v___x_649_;
v_b_642_ = v_fst_646_;
v___y_643_ = v_snd_647_;
goto _start;
}
v___jp_651_:
{
lean_object* v___x_652_; 
v___x_652_ = lean_box(0);
v_fst_646_ = v___x_652_;
v_snd_647_ = v___y_643_;
goto v___jp_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg___boxed(lean_object* v_toUpdate_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_stop_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
size_t v_i_boxed_669_; size_t v_stop_boxed_670_; lean_object* v_res_671_; 
v_i_boxed_669_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_stop_boxed_670_ = lean_unbox_usize(v_stop_665_);
lean_dec(v_stop_665_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_662_, v_as_663_, v_i_boxed_669_, v_stop_boxed_670_, v_b_666_, v___y_667_);
lean_dec_ref(v_as_663_);
lean_dec(v_toUpdate_662_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(lean_object* v_as_672_, size_t v_i_673_, size_t v_stop_674_, lean_object* v_b_675_, lean_object* v___y_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_eq(v_i_673_, v_stop_674_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; size_t v___x_681_; size_t v___x_682_; 
v___x_679_ = lean_array_uget_borrowed(v_as_672_, v_i_673_);
lean_inc_ref(v___y_676_);
lean_inc(v___x_679_);
v___x_680_ = lean_apply_2(v___y_676_, v___x_679_, lean_box(0));
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_673_, v___x_681_);
v_i_673_ = v___x_682_;
v_b_675_ = v___x_680_;
goto _start;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_b_675_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0___boxed(lean_object* v_as_685_, lean_object* v_i_686_, lean_object* v_stop_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
size_t v_i_boxed_691_; size_t v_stop_boxed_692_; lean_object* v_res_693_; 
v_i_boxed_691_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_stop_boxed_692_ = lean_unbox_usize(v_stop_687_);
lean_dec(v_stop_687_);
v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_as_685_, v_i_boxed_691_, v_stop_boxed_692_, v_b_688_, v___y_689_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v_as_685_);
return v_res_693_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_701_ = lean_array_get_size(v___x_700_);
return v___x_701_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_lt(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7(void){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_706_ = lean_nat_dec_le(v___x_705_, v___x_705_);
return v___x_706_;
}
}
static size_t _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8(void){
_start:
{
lean_object* v___x_707_; size_t v___x_708_; 
v___x_707_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__5);
v___x_708_ = lean_usize_of_nat(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest(lean_object* v_ws_711_, lean_object* v_toUpdate_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___y_717_; lean_object* v___y_722_; lean_object* v_fst_723_; lean_object* v_snd_724_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v_val_748_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v_root_797_; lean_object* v_baseName_798_; lean_object* v_dir_799_; lean_object* v_config_800_; lean_object* v_relManifestFile_801_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; uint8_t v_fst_806_; lean_object* v_snd_807_; lean_object* v_packagesDir_x3f_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_870_; lean_object* v___y_871_; uint8_t v___x_874_; lean_object* v_rootName_875_; lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_val_930_; lean_object* v___x_956_; 
v_root_797_ = lean_ctor_get(v_ws_711_, 0);
lean_inc_ref(v_root_797_);
lean_dec_ref(v_ws_711_);
v_baseName_798_ = lean_ctor_get(v_root_797_, 1);
lean_inc(v_baseName_798_);
v_dir_799_ = lean_ctor_get(v_root_797_, 4);
lean_inc_ref(v_dir_799_);
v_config_800_ = lean_ctor_get(v_root_797_, 6);
lean_inc_ref(v_config_800_);
v_relManifestFile_801_ = lean_ctor_get(v_root_797_, 9);
lean_inc_ref(v_relManifestFile_801_);
lean_dec_ref(v_root_797_);
v___x_874_ = 0;
v_rootName_875_ = l_Lean_Name_toString(v_baseName_798_, v___x_874_);
lean_inc_ref(v_dir_799_);
v___x_927_ = l_Lake_joinRelative(v_dir_799_, v_relManifestFile_801_);
v___x_928_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_956_ = l_Lake_Manifest_load(v___x_927_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 1);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v_val_930_ = v___x_962_;
goto v___jp_929_;
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_956_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_956_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 0);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v_val_930_ = v___x_970_;
goto v___jp_929_;
}
}
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___y_717_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
v___jp_721_:
{
if (lean_obj_tag(v_fst_723_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_snd_724_);
v_a_725_ = lean_ctor_get(v_fst_723_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_fst_723_);
if (v_isSharedCheck_739_ == 0)
{
v___x_727_ = v_fst_723_;
v_isShared_728_ = v_isSharedCheck_739_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v_fst_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_739_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_729_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_730_ = lean_io_error_to_string(v_a_725_);
v___x_731_ = lean_string_append(v___x_729_, v___x_730_);
lean_dec_ref(v___x_730_);
v___x_732_ = 3;
v___x_733_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*1, v___x_732_);
lean_inc_ref(v___y_722_);
v___x_734_ = lean_apply_2(v___y_722_, v___x_733_, lean_box(0));
v___x_735_ = lean_box(0);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 1);
lean_ctor_set(v___x_727_, 0, v___x_735_);
v___x_737_ = v___x_727_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec_ref(v_fst_723_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_snd_724_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
v___jp_743_:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v___y_747_);
v___x_750_ = lean_nat_dec_lt(v___y_744_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec_ref(v___y_747_);
v___y_722_ = v___y_745_;
v_fst_723_ = v_val_748_;
v_snd_724_ = v___y_746_;
goto v___jp_721_;
}
else
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_box(0);
v___x_752_ = lean_nat_dec_le(v___x_749_, v___x_749_);
if (v___x_752_ == 0)
{
if (v___x_750_ == 0)
{
lean_dec_ref(v___y_747_);
v___y_722_ = v___y_745_;
v_fst_723_ = v_val_748_;
v_snd_724_ = v___y_746_;
goto v___jp_721_;
}
else
{
size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((size_t)0ULL);
v___x_754_ = lean_usize_of_nat(v___x_749_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_747_, v___x_753_, v___x_754_, v___x_751_, v___y_745_);
lean_dec_ref(v___y_747_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_dec_ref(v___x_755_);
v___y_722_ = v___y_745_;
v_fst_723_ = v_val_748_;
v_snd_724_ = v___y_746_;
goto v___jp_721_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_val_748_);
lean_dec(v___y_746_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_749_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_747_, v___x_764_, v___x_765_, v___x_751_, v___y_745_);
lean_dec_ref(v___y_747_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_dec_ref(v___x_766_);
v___y_722_ = v___y_745_;
v_fst_723_ = v_val_748_;
v_snd_724_ = v___y_746_;
goto v___jp_721_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v_val_748_);
lean_dec(v___y_746_);
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
v___jp_775_:
{
if (lean_obj_tag(v___y_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v___y_780_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___y_780_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___y_780_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___y_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 1);
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v___y_744_ = v___y_776_;
v___y_745_ = v___y_777_;
v___y_746_ = v___y_778_;
v___y_747_ = v___y_779_;
v_val_748_ = v___x_786_;
goto v___jp_743_;
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___y_780_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___y_780_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___y_780_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___y_780_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 0);
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v___y_744_ = v___y_776_;
v___y_745_ = v___y_777_;
v___y_746_ = v___y_778_;
v___y_747_ = v___y_779_;
v_val_748_ = v___x_794_;
goto v___jp_743_;
}
}
}
}
v___jp_802_:
{
lean_object* v_toWorkspaceConfig_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_toWorkspaceConfig_808_ = lean_ctor_get(v_config_800_, 0);
lean_inc_ref(v_toWorkspaceConfig_808_);
lean_dec_ref(v_config_800_);
v___x_809_ = l_System_FilePath_normalize(v___y_803_);
v___x_810_ = l_System_FilePath_normalize(v_toWorkspaceConfig_808_);
lean_inc_ref(v___x_810_);
v___x_811_ = l_System_FilePath_normalize(v___x_810_);
v___x_812_ = lean_string_dec_eq(v___x_809_, v___x_811_);
lean_dec_ref(v___x_811_);
lean_dec_ref(v___x_809_);
if (v___x_812_ == 0)
{
if (v_fst_806_ == 0)
{
lean_dec_ref(v___x_810_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_dir_799_);
v___y_717_ = v_snd_807_;
goto v___jp_716_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_813_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_814_ = lean_string_append(v___x_813_, v___y_805_);
v___x_815_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
v___x_817_ = l_Lake_joinRelative(v_dir_799_, v___x_810_);
v___x_818_ = lean_string_append(v___x_816_, v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_820_ = lean_string_append(v___x_818_, v___x_819_);
v___x_821_ = 1;
v___x_822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*1, v___x_821_);
lean_inc_ref(v___y_804_);
v___x_823_ = lean_apply_2(v___y_804_, v___x_822_, lean_box(0));
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_817_);
v___x_826_ = l_Lake_createParentDirs(v___x_817_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_827_; 
lean_dec_ref(v___x_826_);
v___x_827_ = lean_io_rename(v___y_805_, v___x_817_);
lean_dec_ref(v___x_817_);
lean_dec_ref(v___y_805_);
v___y_776_ = v___x_824_;
v___y_777_ = v___y_804_;
v___y_778_ = v_snd_807_;
v___y_779_ = v___x_825_;
v___y_780_ = v___x_827_;
goto v___jp_775_;
}
else
{
lean_dec_ref(v___x_817_);
lean_dec_ref(v___y_805_);
v___y_776_ = v___x_824_;
v___y_777_ = v___y_804_;
v___y_778_ = v_snd_807_;
v___y_779_ = v___x_825_;
v___y_780_ = v___x_826_;
goto v___jp_775_;
}
}
}
else
{
lean_dec_ref(v___x_810_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_dir_799_);
v___y_717_ = v_snd_807_;
goto v___jp_716_;
}
}
v___jp_828_:
{
if (lean_obj_tag(v_packagesDir_x3f_829_) == 1)
{
lean_object* v_val_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_val_832_ = lean_ctor_get(v_packagesDir_x3f_829_, 0);
lean_inc(v_val_832_);
lean_dec_ref(v_packagesDir_x3f_829_);
lean_inc(v_val_832_);
lean_inc_ref(v_dir_799_);
v___x_833_ = l_Lake_joinRelative(v_dir_799_, v_val_832_);
v___x_834_ = l_System_FilePath_pathExists(v___x_833_);
v___x_835_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_836_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_836_ == 0)
{
v___y_803_ = v_val_832_;
v___y_804_ = v___y_831_;
v___y_805_ = v___x_833_;
v_fst_806_ = v___x_834_;
v_snd_807_ = v___y_830_;
goto v___jp_802_;
}
else
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_box(0);
v___x_838_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_838_ == 0)
{
if (v___x_836_ == 0)
{
v___y_803_ = v_val_832_;
v___y_804_ = v___y_831_;
v___y_805_ = v___x_833_;
v_fst_806_ = v___x_834_;
v_snd_807_ = v___y_830_;
goto v___jp_802_;
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_839_ = ((size_t)0ULL);
v___x_840_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_835_, v___x_839_, v___x_840_, v___x_837_, v___y_831_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_dec_ref(v___x_841_);
v___y_803_ = v_val_832_;
v___y_804_ = v___y_831_;
v___y_805_ = v___x_833_;
v_fst_806_ = v___x_834_;
v_snd_807_ = v___y_830_;
goto v___jp_802_;
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v___x_833_);
lean_dec(v_val_832_);
lean_dec(v___y_830_);
lean_dec_ref(v_config_800_);
lean_dec_ref(v_dir_799_);
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
else
{
size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
v___x_850_ = ((size_t)0ULL);
v___x_851_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_835_, v___x_850_, v___x_851_, v___x_837_, v___y_831_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_dec_ref(v___x_852_);
v___y_803_ = v_val_832_;
v___y_804_ = v___y_831_;
v___y_805_ = v___x_833_;
v_fst_806_ = v___x_834_;
v_snd_807_ = v___y_830_;
goto v___jp_802_;
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
lean_dec_ref(v___x_833_);
lean_dec(v_val_832_);
lean_dec(v___y_830_);
lean_dec_ref(v_config_800_);
lean_dec_ref(v_dir_799_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_packagesDir_x3f_829_);
lean_dec_ref(v_config_800_);
lean_dec_ref(v_dir_799_);
v___x_861_ = lean_box(0);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___y_830_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
v___jp_864_:
{
lean_object* v_packagesDir_x3f_868_; 
v_packagesDir_x3f_868_ = lean_ctor_get(v___y_865_, 2);
lean_inc(v_packagesDir_x3f_868_);
lean_dec_ref(v___y_865_);
v_packagesDir_x3f_829_ = v_packagesDir_x3f_868_;
v___y_830_ = v___y_866_;
v___y_831_ = v___y_867_;
goto v___jp_828_;
}
v___jp_869_:
{
if (lean_obj_tag(v___y_871_) == 0)
{
lean_object* v_a_872_; lean_object* v_snd_873_; 
v_a_872_ = lean_ctor_get(v___y_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v___y_871_);
v_snd_873_ = lean_ctor_get(v_a_872_, 1);
lean_inc(v_snd_873_);
lean_dec(v_a_872_);
v___y_865_ = v___y_870_;
v___y_866_ = v_snd_873_;
v___y_867_ = v_a_714_;
goto v___jp_864_;
}
else
{
lean_dec_ref(v___y_870_);
lean_dec_ref(v_config_800_);
lean_dec_ref(v_dir_799_);
return v___y_871_;
}
}
v___jp_876_:
{
if (lean_obj_tag(v_fst_877_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v_config_800_);
lean_dec_ref(v_dir_799_);
v_a_879_ = lean_ctor_get(v_fst_877_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v_fst_877_);
if (v_isSharedCheck_911_ == 0)
{
v___x_881_ = v_fst_877_;
v_isShared_882_ = v_isSharedCheck_911_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v_fst_877_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_911_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
if (lean_obj_tag(v_a_879_) == 11)
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
lean_dec_ref(v_a_879_);
v___x_883_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_884_ = lean_string_append(v_rootName_875_, v___x_883_);
v___x_885_ = 1;
v___x_886_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*1, v___x_885_);
lean_inc_ref(v_a_714_);
v___x_887_ = lean_apply_2(v_a_714_, v___x_886_, lean_box(0));
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v_snd_878_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_888_);
v___x_890_ = v___x_881_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_712_) == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec(v_snd_878_);
lean_dec_ref(v_rootName_875_);
v___x_892_ = lean_io_error_to_string(v_a_879_);
v___x_893_ = 3;
v___x_894_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*1, v___x_893_);
lean_inc_ref(v_a_714_);
v___x_895_ = lean_apply_2(v_a_714_, v___x_894_, lean_box(0));
v___x_896_ = lean_box(0);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 1);
lean_ctor_set(v___x_881_, 0, v___x_896_);
v___x_898_ = v___x_881_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_900_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_901_ = lean_string_append(v_rootName_875_, v___x_900_);
v___x_902_ = lean_io_error_to_string(v_a_879_);
v___x_903_ = lean_string_append(v___x_901_, v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = 2;
v___x_905_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1, v___x_904_);
lean_inc_ref(v_a_714_);
v___x_906_ = lean_apply_2(v_a_714_, v___x_905_, lean_box(0));
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v_snd_878_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_907_);
v___x_909_ = v___x_881_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
else
{
lean_dec_ref(v_rootName_875_);
if (lean_obj_tag(v_toUpdate_712_) == 0)
{
lean_object* v_a_912_; lean_object* v_packagesDir_x3f_913_; lean_object* v_packages_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_a_912_ = lean_ctor_get(v_fst_877_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v_fst_877_);
v_packagesDir_x3f_913_ = lean_ctor_get(v_a_912_, 2);
v_packages_914_ = lean_ctor_get(v_a_912_, 3);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_array_get_size(v_packages_914_);
v___x_917_ = lean_nat_dec_lt(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_inc(v_packagesDir_x3f_913_);
lean_dec(v_a_912_);
v_packagesDir_x3f_829_ = v_packagesDir_x3f_913_;
v___y_830_ = v_snd_878_;
v___y_831_ = v_a_714_;
goto v___jp_828_;
}
else
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_box(0);
v___x_919_ = lean_nat_dec_le(v___x_916_, v___x_916_);
if (v___x_919_ == 0)
{
if (v___x_917_ == 0)
{
lean_inc(v_packagesDir_x3f_913_);
lean_dec(v_a_912_);
v_packagesDir_x3f_829_ = v_packagesDir_x3f_913_;
v___y_830_ = v_snd_878_;
v___y_831_ = v_a_714_;
goto v___jp_828_;
}
else
{
size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
v___x_920_ = ((size_t)0ULL);
v___x_921_ = lean_usize_of_nat(v___x_916_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_712_, v_packages_914_, v___x_920_, v___x_921_, v___x_918_, v_snd_878_);
v___y_870_ = v_a_912_;
v___y_871_ = v___x_922_;
goto v___jp_869_;
}
}
else
{
size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
v___x_923_ = ((size_t)0ULL);
v___x_924_ = lean_usize_of_nat(v___x_916_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_712_, v_packages_914_, v___x_923_, v___x_924_, v___x_918_, v_snd_878_);
v___y_870_ = v_a_912_;
v___y_871_ = v___x_925_;
goto v___jp_869_;
}
}
}
else
{
lean_object* v_a_926_; 
v_a_926_ = lean_ctor_get(v_fst_877_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v_fst_877_);
v___y_865_ = v_a_926_;
v___y_866_ = v_snd_878_;
v___y_867_ = v_a_714_;
goto v___jp_864_;
}
}
}
v___jp_929_:
{
uint8_t v___x_931_; 
v___x_931_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_931_ == 0)
{
v_fst_877_ = v_val_930_;
v_snd_878_ = v_a_713_;
goto v___jp_876_;
}
else
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_box(0);
v___x_933_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_933_ == 0)
{
if (v___x_931_ == 0)
{
v_fst_877_ = v_val_930_;
v_snd_878_ = v_a_713_;
goto v___jp_876_;
}
else
{
size_t v___x_934_; size_t v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((size_t)0ULL);
v___x_935_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_928_, v___x_934_, v___x_935_, v___x_932_, v_a_714_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_dec_ref(v___x_936_);
v_fst_877_ = v_val_930_;
v_snd_878_ = v_a_713_;
goto v___jp_876_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_val_930_);
lean_dec_ref(v_rootName_875_);
lean_dec_ref(v_config_800_);
lean_dec_ref(v_dir_799_);
lean_dec(v_a_713_);
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
size_t v___x_945_; size_t v___x_946_; lean_object* v___x_947_; 
v___x_945_ = ((size_t)0ULL);
v___x_946_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_928_, v___x_945_, v___x_946_, v___x_932_, v_a_714_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_dec_ref(v___x_947_);
v_fst_877_ = v_val_930_;
v_snd_878_ = v_a_713_;
goto v___jp_876_;
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_val_930_);
lean_dec_ref(v_rootName_875_);
lean_dec_ref(v_config_800_);
lean_dec_ref(v_dir_799_);
lean_dec(v_a_713_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___boxed(lean_object* v_ws_973_, lean_object* v_toUpdate_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest(v_ws_973_, v_toUpdate_974_, v_a_975_, v_a_976_);
lean_dec_ref(v_a_976_);
lean_dec(v_toUpdate_974_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(lean_object* v_toUpdate_979_, lean_object* v_as_980_, size_t v_i_981_, size_t v_stop_982_, lean_object* v_b_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_979_, v_as_980_, v_i_981_, v_stop_982_, v_b_983_, v___y_984_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___boxed(lean_object* v_toUpdate_988_, lean_object* v_as_989_, lean_object* v_i_990_, lean_object* v_stop_991_, lean_object* v_b_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
size_t v_i_boxed_996_; size_t v_stop_boxed_997_; lean_object* v_res_998_; 
v_i_boxed_996_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_stop_boxed_997_ = lean_unbox_usize(v_stop_991_);
lean_dec(v_stop_991_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1(v_toUpdate_988_, v_as_989_, v_i_boxed_996_, v_stop_boxed_997_, v_b_992_, v___y_993_, v___y_994_);
lean_dec_ref(v___y_994_);
lean_dec_ref(v_as_989_);
lean_dec(v_toUpdate_988_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(lean_object* v_pkg_999_, lean_object* v_as_1000_, size_t v_i_1001_, size_t v_stop_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___y_1013_; lean_object* v_name_1014_; uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v_name_1019_; lean_object* v_scope_1020_; lean_object* v_configFile_1021_; lean_object* v_manifestFile_x3f_1022_; lean_object* v_src_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1046_; 
v___x_1018_ = lean_array_uget(v_as_1000_, v_i_1001_);
v_name_1019_ = lean_ctor_get(v___x_1018_, 0);
v_scope_1020_ = lean_ctor_get(v___x_1018_, 1);
v_configFile_1021_ = lean_ctor_get(v___x_1018_, 2);
v_manifestFile_x3f_1022_ = lean_ctor_get(v___x_1018_, 3);
v_src_1023_ = lean_ctor_get(v___x_1018_, 4);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1025_ = v___x_1018_;
v_isShared_1026_ = v_isSharedCheck_1046_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_src_1023_);
lean_inc(v_manifestFile_x3f_1022_);
lean_inc(v_configFile_1021_);
lean_inc(v_scope_1020_);
lean_inc(v_name_1019_);
lean_dec(v___x_1018_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1046_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_1019_, v___y_1004_);
if (v___x_1027_ == 0)
{
uint8_t v___x_1028_; 
v___x_1028_ = 1;
if (lean_obj_tag(v_src_1023_) == 0)
{
lean_object* v_dir_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1041_; 
v_dir_1029_ = lean_ctor_get(v_src_1023_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_src_1023_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1031_ = v_src_1023_;
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_dir_1029_);
lean_dec(v_src_1023_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_relDir_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v_relDir_1033_ = lean_ctor_get(v_pkg_999_, 5);
lean_inc_ref(v_relDir_1033_);
v___x_1034_ = l_Lake_joinRelative(v_relDir_1033_, v_dir_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1034_);
v___x_1036_ = v___x_1031_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
lean_inc(v_name_1019_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v___x_1036_);
v___x_1038_ = v___x_1025_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_name_1019_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_scope_1020_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_configFile_1021_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_manifestFile_x3f_1022_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*5, v___x_1028_);
v___y_1013_ = v___x_1038_;
v_name_1014_ = v_name_1019_;
goto v___jp_1012_;
}
}
}
}
else
{
lean_object* v___x_1043_; 
lean_inc(v_name_1019_);
if (v_isShared_1026_ == 0)
{
v___x_1043_ = v___x_1025_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_name_1019_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_scope_1020_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_configFile_1021_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v_manifestFile_x3f_1022_);
lean_ctor_set(v_reuseFailAlloc_1044_, 4, v_src_1023_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_ctor_set_uint8(v___x_1043_, sizeof(void*)*5, v___x_1028_);
v___y_1013_ = v___x_1043_;
v_name_1014_ = v_name_1019_;
goto v___jp_1012_;
}
}
}
else
{
lean_object* v___x_1045_; 
lean_del_object(v___x_1025_);
lean_dec_ref(v_src_1023_);
lean_dec(v_manifestFile_x3f_1022_);
lean_dec_ref(v_configFile_1021_);
lean_dec_ref(v_scope_1020_);
lean_dec(v_name_1019_);
v___x_1045_ = lean_box(0);
v_fst_1007_ = v___x_1045_;
v_snd_1008_ = v___y_1004_;
goto v___jp_1006_;
}
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec_ref(v_pkg_999_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_b_1003_);
lean_ctor_set(v___x_1047_, 1, v___y_1004_);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
v___jp_1006_:
{
size_t v___x_1009_; size_t v___x_1010_; 
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_add(v_i_1001_, v___x_1009_);
v_i_1001_ = v___x_1010_;
v_b_1003_ = v_fst_1007_;
v___y_1004_ = v_snd_1008_;
goto _start;
}
v___jp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1014_, v___y_1013_, v___y_1004_);
v_fst_1007_ = v___x_1015_;
v_snd_1008_ = v___x_1016_;
goto v___jp_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg___boxed(lean_object* v_pkg_1049_, lean_object* v_as_1050_, lean_object* v_i_1051_, lean_object* v_stop_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
size_t v_i_boxed_1056_; size_t v_stop_boxed_1057_; lean_object* v_res_1058_; 
v_i_boxed_1056_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_stop_boxed_1057_ = lean_unbox_usize(v_stop_1052_);
lean_dec(v_stop_1052_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_pkg_1049_, v_as_1050_, v_i_boxed_1056_, v_stop_boxed_1057_, v_b_1053_, v___y_1054_);
lean_dec_ref(v_as_1050_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(lean_object* v_pkg_1061_, lean_object* v_matDep_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_manifest_x3f_1066_; 
v_manifest_x3f_1066_ = lean_ctor_get(v_matDep_1062_, 2);
lean_inc_ref(v_manifest_x3f_1066_);
lean_dec_ref(v_matDep_1062_);
if (lean_obj_tag(v_manifest_x3f_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1103_; 
v_a_1067_ = lean_ctor_get(v_manifest_x3f_1066_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_manifest_x3f_1066_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1069_ = v_manifest_x3f_1066_;
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v_manifest_x3f_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1103_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
if (lean_obj_tag(v_a_1067_) == 11)
{
lean_object* v_baseName_1071_; lean_object* v_dir_1072_; lean_object* v_relManifestFile_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_dec_ref(v_a_1067_);
v_baseName_1071_ = lean_ctor_get(v_pkg_1061_, 1);
lean_inc(v_baseName_1071_);
v_dir_1072_ = lean_ctor_get(v_pkg_1061_, 4);
lean_inc_ref(v_dir_1072_);
v_relManifestFile_1073_ = lean_ctor_get(v_pkg_1061_, 9);
lean_inc_ref(v_relManifestFile_1073_);
lean_dec_ref(v_pkg_1061_);
v___x_1074_ = 0;
v___x_1075_ = l_Lean_Name_toString(v_baseName_1071_, v___x_1074_);
v___x_1076_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
v___x_1078_ = l_Lake_joinRelative(v_dir_1072_, v_relManifestFile_1073_);
v___x_1079_ = lean_string_append(v___x_1077_, v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
v___x_1082_ = 2;
v___x_1083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
lean_inc_ref(v_a_1064_);
v___x_1084_ = lean_apply_2(v_a_1064_, v___x_1083_, lean_box(0));
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_a_1063_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1085_);
v___x_1087_ = v___x_1069_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
lean_object* v_baseName_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v_baseName_1089_ = lean_ctor_get(v_pkg_1061_, 1);
lean_inc(v_baseName_1089_);
lean_dec_ref(v_pkg_1061_);
v___x_1090_ = 0;
v___x_1091_ = l_Lean_Name_toString(v_baseName_1089_, v___x_1090_);
v___x_1092_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_1093_ = lean_string_append(v___x_1091_, v___x_1092_);
v___x_1094_ = lean_io_error_to_string(v_a_1067_);
v___x_1095_ = lean_string_append(v___x_1093_, v___x_1094_);
lean_dec_ref(v___x_1094_);
v___x_1096_ = 2;
v___x_1097_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set_uint8(v___x_1097_, sizeof(void*)*1, v___x_1096_);
lean_inc_ref(v_a_1064_);
v___x_1098_ = lean_apply_2(v_a_1064_, v___x_1097_, lean_box(0));
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_a_1063_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1099_);
v___x_1101_ = v___x_1069_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1128_; 
v_a_1104_ = lean_ctor_get(v_manifest_x3f_1066_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_manifest_x3f_1066_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1106_ = v_manifest_x3f_1066_;
v_isShared_1107_ = v_isSharedCheck_1128_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v_manifest_x3f_1066_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1128_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_packages_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_packages_1108_ = lean_ctor_get(v_a_1104_, 3);
lean_inc_ref(v_packages_1108_);
lean_dec(v_a_1104_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_array_get_size(v_packages_1108_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_nat_dec_lt(v___x_1109_, v___x_1110_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_dec_ref(v_packages_1108_);
lean_dec_ref(v_pkg_1061_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v_a_1063_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1113_);
v___x_1115_ = v___x_1106_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_nat_dec_le(v___x_1110_, v___x_1110_);
if (v___x_1117_ == 0)
{
if (v___x_1112_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec_ref(v_packages_1108_);
lean_dec_ref(v_pkg_1061_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1111_);
lean_ctor_set(v___x_1118_, 1, v_a_1063_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1118_);
v___x_1120_ = v___x_1106_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; 
lean_del_object(v___x_1106_);
v___x_1122_ = ((size_t)0ULL);
v___x_1123_ = lean_usize_of_nat(v___x_1110_);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_pkg_1061_, v_packages_1108_, v___x_1122_, v___x_1123_, v___x_1111_, v_a_1063_);
lean_dec_ref(v_packages_1108_);
return v___x_1124_;
}
}
else
{
size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
lean_del_object(v___x_1106_);
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = lean_usize_of_nat(v___x_1110_);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_pkg_1061_, v_packages_1108_, v___x_1125_, v___x_1126_, v___x_1111_, v_a_1063_);
lean_dec_ref(v_packages_1108_);
return v___x_1127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___boxed(lean_object* v_pkg_1129_, lean_object* v_matDep_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_pkg_1129_, v_matDep_1130_, v_a_1131_, v_a_1132_);
lean_dec_ref(v_a_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(lean_object* v_pkg_1135_, lean_object* v_as_1136_, size_t v_i_1137_, size_t v_stop_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_pkg_1135_, v_as_1136_, v_i_1137_, v_stop_1138_, v_b_1139_, v___y_1140_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___boxed(lean_object* v_pkg_1144_, lean_object* v_as_1145_, lean_object* v_i_1146_, lean_object* v_stop_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
size_t v_i_boxed_1152_; size_t v_stop_boxed_1153_; lean_object* v_res_1154_; 
v_i_boxed_1152_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_stop_boxed_1153_ = lean_unbox_usize(v_stop_1147_);
lean_dec(v_stop_1147_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0(v_pkg_1144_, v_as_1145_, v_i_boxed_1152_, v_stop_boxed_1153_, v_b_1148_, v___y_1149_, v___y_1150_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v_as_1145_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(lean_object* v_ws_1156_, lean_object* v_pkg_1157_, lean_object* v_dep_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v_name_1192_; lean_object* v___x_1193_; 
v_name_1192_ = lean_ctor_get(v_dep_1158_, 0);
v___x_1193_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_1159_, v_name_1192_);
if (lean_obj_tag(v___x_1193_) == 1)
{
lean_object* v_root_1194_; lean_object* v_config_1195_; lean_object* v_val_1196_; lean_object* v_lakeEnv_1197_; lean_object* v_dir_1198_; lean_object* v_toWorkspaceConfig_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v_dep_1158_);
lean_dec_ref(v_pkg_1157_);
v_root_1194_ = lean_ctor_get(v_ws_1156_, 0);
lean_inc_ref(v_root_1194_);
v_config_1195_ = lean_ctor_get(v_root_1194_, 6);
lean_inc_ref(v_config_1195_);
v_val_1196_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_val_1196_);
lean_dec_ref(v___x_1193_);
v_lakeEnv_1197_ = lean_ctor_get(v_ws_1156_, 1);
lean_inc_ref(v_lakeEnv_1197_);
lean_dec_ref(v_ws_1156_);
v_dir_1198_ = lean_ctor_get(v_root_1194_, 4);
lean_inc_ref(v_dir_1198_);
lean_dec_ref(v_root_1194_);
v_toWorkspaceConfig_1199_ = lean_ctor_get(v_config_1195_, 0);
lean_inc_ref(v_toWorkspaceConfig_1199_);
lean_dec_ref(v_config_1195_);
v___x_1200_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1199_);
v___x_1201_ = l_Lake_PackageEntry_materialize(v_val_1196_, v_lakeEnv_1197_, v_dir_1198_, v___x_1200_, v_a_1160_);
lean_dec_ref(v_lakeEnv_1197_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1210_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_a_1202_);
lean_ctor_set(v___x_1206_, 1, v_a_1159_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_a_1159_);
v_a_1211_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1201_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1201_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_wsIdx_1219_; lean_object* v_relDir_1220_; uint8_t v___y_1222_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
lean_dec(v___x_1193_);
v_wsIdx_1219_ = lean_ctor_get(v_pkg_1157_, 0);
lean_inc(v_wsIdx_1219_);
v_relDir_1220_ = lean_ctor_get(v_pkg_1157_, 5);
lean_inc_ref(v_relDir_1220_);
lean_dec_ref(v_pkg_1157_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_nat_dec_eq(v_wsIdx_1219_, v___x_1226_);
lean_dec(v_wsIdx_1219_);
if (v___x_1227_ == 0)
{
uint8_t v___x_1228_; 
v___x_1228_ = 1;
v___y_1222_ = v___x_1228_;
goto v___jp_1221_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
v___y_1222_ = v___x_1229_;
goto v___jp_1221_;
}
v___jp_1221_:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_1224_ = lean_string_dec_eq(v_relDir_1220_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lake_joinRelative(v_relDir_1220_, v___x_1223_);
v___y_1163_ = v___y_1222_;
v___y_1164_ = v___x_1225_;
goto v___jp_1162_;
}
else
{
v___y_1163_ = v___y_1222_;
v___y_1164_ = v_relDir_1220_;
goto v___jp_1162_;
}
}
}
v___jp_1162_:
{
lean_object* v_root_1165_; lean_object* v_config_1166_; lean_object* v_lakeEnv_1167_; lean_object* v_dir_1168_; lean_object* v_toWorkspaceConfig_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_root_1165_ = lean_ctor_get(v_ws_1156_, 0);
lean_inc_ref(v_root_1165_);
v_config_1166_ = lean_ctor_get(v_root_1165_, 6);
lean_inc_ref(v_config_1166_);
v_lakeEnv_1167_ = lean_ctor_get(v_ws_1156_, 1);
lean_inc_ref(v_lakeEnv_1167_);
lean_dec_ref(v_ws_1156_);
v_dir_1168_ = lean_ctor_get(v_root_1165_, 4);
lean_inc_ref(v_dir_1168_);
lean_dec_ref(v_root_1165_);
v_toWorkspaceConfig_1169_ = lean_ctor_get(v_config_1166_, 0);
lean_inc_ref(v_toWorkspaceConfig_1169_);
lean_dec_ref(v_config_1166_);
v___x_1170_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1169_);
v___x_1171_ = l_Lake_Dependency_materialize(v_dep_1158_, v___y_1163_, v_lakeEnv_1167_, v_dir_1168_, v___x_1170_, v___y_1164_, v_a_1160_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1183_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1183_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1183_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_manifestEntry_1176_; lean_object* v_name_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v_manifestEntry_1176_ = lean_ctor_get(v_a_1172_, 3);
v_name_1177_ = lean_ctor_get(v_manifestEntry_1176_, 0);
lean_inc_ref(v_manifestEntry_1176_);
lean_inc(v_name_1177_);
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_1177_, v_manifestEntry_1176_, v_a_1159_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_a_1172_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1179_);
v___x_1181_ = v___x_1174_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_a_1159_);
v_a_1184_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1171_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1171_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___boxed(lean_object* v_ws_1230_, lean_object* v_pkg_1231_, lean_object* v_dep_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_ws_1230_, v_pkg_1231_, v_dep_1232_, v_a_1233_, v_a_1234_);
lean_dec_ref(v_a_1234_);
return v_res_1236_;
}
}
static uint32_t _init_l___private_Lake_Load_Resolve_0__Lake_restartCode(void){
_start:
{
uint32_t v___x_1237_; 
v___x_1237_ = 4;
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(lean_object* v_src_1238_, lean_object* v_tc_x3f_1239_, uint8_t v_fixed_1240_, lean_object* v_self_1241_){
_start:
{
lean_object* v_clashes_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
v_clashes_1242_ = lean_ctor_get(v_self_1241_, 2);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_self_1241_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; lean_object* v_unused_1251_; 
v_unused_1250_ = lean_ctor_get(v_self_1241_, 1);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_self_1241_, 0);
lean_dec(v_unused_1251_);
v___x_1244_ = v_self_1241_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_clashes_1242_);
lean_dec(v_self_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_tc_x3f_1239_);
lean_ctor_set(v___x_1244_, 0, v_src_1238_);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_src_1238_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_tc_x3f_1239_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_clashes_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*3, v_fixed_1240_);
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace___boxed(lean_object* v_src_1252_, lean_object* v_tc_x3f_1253_, lean_object* v_fixed_1254_, lean_object* v_self_1255_){
_start:
{
uint8_t v_fixed_boxed_1256_; lean_object* v_res_1257_; 
v_fixed_boxed_1256_ = lean_unbox(v_fixed_1254_);
v_res_1257_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_replace(v_src_1252_, v_tc_x3f_1253_, v_fixed_boxed_1256_, v_self_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(lean_object* v_src_1258_, lean_object* v_ver_1259_, uint8_t v_fixed_1260_, lean_object* v_self_1261_){
_start:
{
lean_object* v_src_1262_; lean_object* v_tc_x3f_1263_; lean_object* v_clashes_1264_; uint8_t v_fixed_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1274_; 
v_src_1262_ = lean_ctor_get(v_self_1261_, 0);
v_tc_x3f_1263_ = lean_ctor_get(v_self_1261_, 1);
v_clashes_1264_ = lean_ctor_get(v_self_1261_, 2);
v_fixed_1265_ = lean_ctor_get_uint8(v_self_1261_, sizeof(void*)*3);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_self_1261_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1267_ = v_self_1261_;
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_clashes_1264_);
lean_inc(v_tc_x3f_1263_);
lean_inc(v_src_1262_);
lean_dec(v_self_1261_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1274_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1269_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1269_, 0, v_src_1258_);
lean_ctor_set(v___x_1269_, 1, v_ver_1259_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*2, v_fixed_1260_);
v___x_1270_ = lean_array_push(v_clashes_1264_, v___x_1269_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 2, v___x_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_src_1262_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_tc_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v___x_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3, v_fixed_1265_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash___boxed(lean_object* v_src_1275_, lean_object* v_ver_1276_, lean_object* v_fixed_1277_, lean_object* v_self_1278_){
_start:
{
uint8_t v_fixed_boxed_1279_; lean_object* v_res_1280_; 
v_fixed_boxed_1279_ = lean_unbox(v_fixed_1277_);
v_res_1280_ = l___private_Lake_Load_Resolve_0__Lake_ToolchainState_addClash(v_src_1275_, v_ver_1276_, v_fixed_boxed_1279_, v_self_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(lean_object* v_as_1285_, size_t v_i_1286_, size_t v_stop_1287_, lean_object* v_b_1288_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_usize_dec_eq(v_i_1286_, v_stop_1287_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v_src_1291_; lean_object* v_ver_1292_; uint8_t v_fixed_1293_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1309_; 
v___x_1290_ = lean_array_uget_borrowed(v_as_1285_, v_i_1286_);
v_src_1291_ = lean_ctor_get(v___x_1290_, 0);
v_ver_1292_ = lean_ctor_get(v___x_1290_, 1);
v_fixed_1293_ = lean_ctor_get_uint8(v___x_1290_, sizeof(void*)*2);
if (v_fixed_1293_ == 0)
{
lean_object* v___x_1313_; 
v___x_1313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1309_ = v___x_1313_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1314_; 
v___x_1314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1309_ = v___x_1314_;
goto v___jp_1308_;
}
v___jp_1294_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; size_t v___x_1305_; size_t v___x_1306_; 
v___x_1298_ = lean_string_append(v___y_1296_, v___y_1297_);
lean_dec_ref(v___y_1297_);
v___x_1299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1300_ = lean_string_append(v___x_1298_, v___x_1299_);
v___x_1301_ = 1;
lean_inc(v_src_1291_);
v___x_1302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1291_, v___x_1301_);
v___x_1303_ = lean_string_append(v___x_1300_, v___x_1302_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = lean_string_append(v___x_1303_, v___y_1295_);
lean_dec_ref(v___y_1295_);
v___x_1305_ = ((size_t)1ULL);
v___x_1306_ = lean_usize_add(v_i_1286_, v___x_1305_);
v_i_1286_ = v___x_1306_;
v_b_1288_ = v___x_1304_;
goto _start;
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_toString_1312_; 
v___x_1310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1311_ = lean_string_append(v_b_1288_, v___x_1310_);
v_toString_1312_ = lean_ctor_get(v_ver_1292_, 0);
lean_inc_ref(v_toString_1312_);
v___y_1295_ = v___y_1309_;
v___y_1296_ = v___x_1311_;
v___y_1297_ = v_toString_1312_;
goto v___jp_1294_;
}
}
else
{
return v_b_1288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___boxed(lean_object* v_as_1315_, lean_object* v_i_1316_, lean_object* v_stop_1317_, lean_object* v_b_1318_){
_start:
{
size_t v_i_boxed_1319_; size_t v_stop_boxed_1320_; lean_object* v_res_1321_; 
v_i_boxed_1319_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_stop_boxed_1320_ = lean_unbox_usize(v_stop_1317_);
lean_dec(v_stop_1317_);
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1315_, v_i_boxed_1319_, v_stop_boxed_1320_, v_b_1318_);
lean_dec_ref(v_as_1315_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(lean_object* v_as_1322_, size_t v_i_1323_, size_t v_stop_1324_, lean_object* v_b_1325_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_eq(v_i_1323_, v_stop_1324_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v_src_1328_; lean_object* v_ver_1329_; uint8_t v_fixed_1330_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1346_; 
v___x_1327_ = lean_array_uget_borrowed(v_as_1322_, v_i_1323_);
v_src_1328_ = lean_ctor_get(v___x_1327_, 0);
v_ver_1329_ = lean_ctor_get(v___x_1327_, 1);
v_fixed_1330_ = lean_ctor_get_uint8(v___x_1327_, sizeof(void*)*2);
if (v_fixed_1330_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1346_ = v___x_1350_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1346_ = v___x_1351_;
goto v___jp_1345_;
}
v___jp_1331_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1335_ = lean_string_append(v___y_1332_, v___y_1334_);
lean_dec_ref(v___y_1334_);
v___x_1336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1337_ = lean_string_append(v___x_1335_, v___x_1336_);
v___x_1338_ = 1;
lean_inc(v_src_1328_);
v___x_1339_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_src_1328_, v___x_1338_);
v___x_1340_ = lean_string_append(v___x_1337_, v___x_1339_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_string_append(v___x_1340_, v___y_1333_);
lean_dec_ref(v___y_1333_);
v___x_1342_ = ((size_t)1ULL);
v___x_1343_ = lean_usize_add(v_i_1323_, v___x_1342_);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0(v_as_1322_, v___x_1343_, v_stop_1324_, v___x_1341_);
return v___x_1344_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_toString_1349_; 
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__1));
v___x_1348_ = lean_string_append(v_b_1325_, v___x_1347_);
v_toString_1349_ = lean_ctor_get(v_ver_1329_, 0);
lean_inc_ref(v_toString_1349_);
v___y_1332_ = v___x_1348_;
v___y_1333_ = v___y_1346_;
v___y_1334_ = v_toString_1349_;
goto v___jp_1331_;
}
}
else
{
return v_b_1325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0___boxed(lean_object* v_as_1352_, lean_object* v_i_1353_, lean_object* v_stop_1354_, lean_object* v_b_1355_){
_start:
{
size_t v_i_boxed_1356_; size_t v_stop_boxed_1357_; lean_object* v_res_1358_; 
v_i_boxed_1356_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_stop_boxed_1357_ = lean_unbox_usize(v_stop_1354_);
lean_dec(v_stop_1354_);
v_res_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v_as_1352_, v_i_boxed_1356_, v_stop_boxed_1357_, v_b_1355_);
lean_dec_ref(v_as_1352_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(lean_object* v___x_1359_, lean_object* v_as_1360_, size_t v_i_1361_, size_t v_stop_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_usize_dec_eq(v_i_1361_, v_stop_1362_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v_relPkgDir_1368_; lean_object* v_manifestEntry_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1367_ = lean_array_uget_borrowed(v_as_1360_, v_i_1361_);
v_relPkgDir_1368_ = lean_ctor_get(v___x_1367_, 0);
v_manifestEntry_1369_ = lean_ctor_get(v___x_1367_, 3);
lean_inc_ref(v_relPkgDir_1368_);
lean_inc_ref(v___x_1359_);
v___x_1370_ = l_Lake_joinRelative(v___x_1359_, v_relPkgDir_1368_);
v___x_1371_ = l_Lake_toolchainFileName;
v___x_1372_ = l_System_FilePath_join(v___x_1370_, v___x_1371_);
v___x_1373_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1372_);
lean_dec_ref(v___x_1372_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v_a_1376_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
if (lean_obj_tag(v_a_1374_) == 1)
{
lean_object* v_tc_x3f_1380_; 
v_tc_x3f_1380_ = lean_ctor_get(v_b_1363_, 1);
if (lean_obj_tag(v_tc_x3f_1380_) == 1)
{
lean_object* v_val_1381_; lean_object* v_src_1382_; lean_object* v_clashes_1383_; uint8_t v_fixed_1384_; lean_object* v_val_1385_; uint8_t v___x_1386_; 
v_val_1381_ = lean_ctor_get(v_a_1374_, 0);
v_src_1382_ = lean_ctor_get(v_b_1363_, 0);
v_clashes_1383_ = lean_ctor_get(v_b_1363_, 2);
v_fixed_1384_ = lean_ctor_get_uint8(v_b_1363_, sizeof(void*)*3);
v_val_1385_ = lean_ctor_get(v_tc_x3f_1380_, 0);
v___x_1386_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1367_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = l_Lake_ToolchainVer_ble(v_val_1381_, v_val_1385_);
if (v___x_1396_ == 0)
{
lean_inc_ref(v_clashes_1383_);
lean_inc(v_src_1382_);
lean_inc_ref(v_tc_x3f_1380_);
lean_dec_ref(v_b_1363_);
if (v_fixed_1384_ == 0)
{
goto v___jp_1392_;
}
else
{
if (v___x_1386_ == 0)
{
lean_inc(v_val_1381_);
lean_dec_ref(v_a_1374_);
goto v___jp_1387_;
}
else
{
goto v___jp_1392_;
}
}
}
else
{
lean_dec_ref(v_a_1374_);
v_a_1376_ = v_b_1363_;
goto v___jp_1375_;
}
}
else
{
if (v_fixed_1384_ == 0)
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1411_; 
lean_inc_ref(v_clashes_1383_);
lean_inc(v_src_1382_);
lean_inc_ref(v_tc_x3f_1380_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_b_1363_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; lean_object* v_unused_1413_; lean_object* v_unused_1414_; 
v_unused_1412_ = lean_ctor_get(v_b_1363_, 2);
lean_dec(v_unused_1412_);
v_unused_1413_ = lean_ctor_get(v_b_1363_, 1);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_b_1363_, 0);
lean_dec(v_unused_1414_);
v___x_1398_ = v_b_1363_;
v_isShared_1399_ = v_isSharedCheck_1411_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v_b_1363_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1411_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Lake_ToolchainVer_ble(v_val_1385_, v_val_1381_);
if (v___x_1400_ == 0)
{
lean_object* v_name_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
lean_inc(v_val_1381_);
lean_dec_ref(v_a_1374_);
v_name_1401_ = lean_ctor_get(v_manifestEntry_1369_, 0);
lean_inc(v_name_1401_);
v___x_1402_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1402_, 0, v_name_1401_);
lean_ctor_set(v___x_1402_, 1, v_val_1381_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*2, v___x_1386_);
v___x_1403_ = lean_array_push(v_clashes_1383_, v___x_1402_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 2, v___x_1403_);
v___x_1405_ = v___x_1398_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_src_1382_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_tc_x3f_1380_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v___x_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1406_, sizeof(void*)*3, v_fixed_1384_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
v_a_1376_ = v___x_1405_;
goto v___jp_1375_;
}
}
else
{
lean_object* v_name_1407_; lean_object* v___x_1409_; 
lean_dec(v_src_1382_);
lean_dec_ref(v_tc_x3f_1380_);
v_name_1407_ = lean_ctor_get(v_manifestEntry_1369_, 0);
lean_inc(v_name_1407_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v_a_1374_);
lean_ctor_set(v___x_1398_, 0, v_name_1407_);
v___x_1409_ = v___x_1398_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_name_1407_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_a_1374_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_clashes_1383_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_ctor_set_uint8(v___x_1409_, sizeof(void*)*3, v___x_1386_);
v_a_1376_ = v___x_1409_;
goto v___jp_1375_;
}
}
}
}
else
{
uint8_t v___x_1415_; 
lean_inc(v_val_1381_);
lean_dec_ref(v_a_1374_);
lean_inc(v_val_1381_);
lean_inc(v_val_1385_);
v___x_1415_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_1385_, v_val_1381_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1425_; 
lean_inc_ref(v_clashes_1383_);
lean_inc(v_src_1382_);
lean_inc_ref(v_tc_x3f_1380_);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_b_1363_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; lean_object* v_unused_1428_; 
v_unused_1426_ = lean_ctor_get(v_b_1363_, 2);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_b_1363_, 1);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_b_1363_, 0);
lean_dec(v_unused_1428_);
v___x_1417_ = v_b_1363_;
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v_b_1363_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1425_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_name_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v_name_1419_ = lean_ctor_get(v_manifestEntry_1369_, 0);
lean_inc(v_name_1419_);
v___x_1420_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1420_, 0, v_name_1419_);
lean_ctor_set(v___x_1420_, 1, v_val_1381_);
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*2, v___x_1386_);
v___x_1421_ = lean_array_push(v_clashes_1383_, v___x_1420_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 2, v___x_1421_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_src_1382_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_tc_x3f_1380_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v___x_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1424_, sizeof(void*)*3, v_fixed_1384_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
v_a_1376_ = v___x_1423_;
goto v___jp_1375_;
}
}
}
else
{
lean_dec(v_val_1381_);
v_a_1376_ = v_b_1363_;
goto v___jp_1375_;
}
}
}
v___jp_1387_:
{
lean_object* v_name_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_name_1388_ = lean_ctor_get(v_manifestEntry_1369_, 0);
lean_inc(v_name_1388_);
v___x_1389_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1389_, 0, v_name_1388_);
lean_ctor_set(v___x_1389_, 1, v_val_1381_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*2, v___x_1386_);
v___x_1390_ = lean_array_push(v_clashes_1383_, v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1391_, 0, v_src_1382_);
lean_ctor_set(v___x_1391_, 1, v_tc_x3f_1380_);
lean_ctor_set(v___x_1391_, 2, v___x_1390_);
lean_ctor_set_uint8(v___x_1391_, sizeof(void*)*3, v_fixed_1384_);
v_a_1376_ = v___x_1391_;
goto v___jp_1375_;
}
v___jp_1392_:
{
uint8_t v___x_1393_; 
v___x_1393_ = l_Lake_ToolchainVer_blt(v_val_1385_, v_val_1381_);
if (v___x_1393_ == 0)
{
lean_inc(v_val_1381_);
lean_dec_ref(v_a_1374_);
goto v___jp_1387_;
}
else
{
lean_object* v_name_1394_; lean_object* v___x_1395_; 
lean_dec(v_src_1382_);
lean_dec_ref(v_tc_x3f_1380_);
v_name_1394_ = lean_ctor_get(v_manifestEntry_1369_, 0);
lean_inc(v_name_1394_);
v___x_1395_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1395_, 0, v_name_1394_);
lean_ctor_set(v___x_1395_, 1, v_a_1374_);
lean_ctor_set(v___x_1395_, 2, v_clashes_1383_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3, v___x_1386_);
v_a_1376_ = v___x_1395_;
goto v___jp_1375_;
}
}
}
else
{
lean_object* v_clashes_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1438_; 
v_clashes_1429_ = lean_ctor_get(v_b_1363_, 2);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_b_1363_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; lean_object* v_unused_1440_; 
v_unused_1439_ = lean_ctor_get(v_b_1363_, 1);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_b_1363_, 0);
lean_dec(v_unused_1440_);
v___x_1431_ = v_b_1363_;
v_isShared_1432_ = v_isSharedCheck_1438_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_clashes_1429_);
lean_dec(v_b_1363_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1438_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_name_1433_; uint8_t v___x_1434_; lean_object* v___x_1436_; 
v_name_1433_ = lean_ctor_get(v_manifestEntry_1369_, 0);
v___x_1434_ = l_Lake_MaterializedDep_fixedToolchain(v___x_1367_);
lean_inc(v_name_1433_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v_a_1374_);
lean_ctor_set(v___x_1431_, 0, v_name_1433_);
v___x_1436_ = v___x_1431_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_name_1433_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_a_1374_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_clashes_1429_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_ctor_set_uint8(v___x_1436_, sizeof(void*)*3, v___x_1434_);
v_a_1376_ = v___x_1436_;
goto v___jp_1375_;
}
}
}
}
else
{
lean_dec(v_a_1374_);
v_a_1376_ = v_b_1363_;
goto v___jp_1375_;
}
v___jp_1375_:
{
size_t v___x_1377_; size_t v___x_1378_; 
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1361_, v___x_1377_);
v_i_1361_ = v___x_1378_;
v_b_1363_ = v_a_1376_;
goto _start;
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref(v_b_1363_);
lean_dec_ref(v___x_1359_);
v_a_1441_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1443_ = v___x_1373_;
v_isShared_1444_ = v_isSharedCheck_1453_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1373_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1453_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1445_ = lean_io_error_to_string(v_a_1441_);
v___x_1446_ = 3;
v___x_1447_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*1, v___x_1446_);
lean_inc_ref(v___y_1364_);
v___x_1448_ = lean_apply_2(v___y_1364_, v___x_1447_, lean_box(0));
v___x_1449_ = lean_box(0);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1449_);
v___x_1451_ = v___x_1443_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
else
{
lean_object* v___x_1454_; 
lean_dec_ref(v___x_1359_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1363_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1___boxed(lean_object* v___x_1455_, lean_object* v_as_1456_, lean_object* v_i_1457_, lean_object* v_stop_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
size_t v_i_boxed_1462_; size_t v_stop_boxed_1463_; lean_object* v_res_1464_; 
v_i_boxed_1462_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_stop_boxed_1463_ = lean_unbox_usize(v_stop_1458_);
lean_dec(v_stop_1458_);
v_res_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v___x_1455_, v_as_1456_, v_i_boxed_1462_, v_stop_boxed_1463_, v_b_1459_, v___y_1460_);
lean_dec_ref(v___y_1460_);
lean_dec_ref(v_as_1456_);
return v_res_1464_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__3));
v___x_1475_ = lean_unsigned_to_nat(4u);
v___x_1476_ = lean_mk_empty_array_with_capacity(v___x_1475_);
v___x_1477_ = lean_array_push(v___x_1476_, v___x_1474_);
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__4));
v___x_1479_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__6);
v___x_1480_ = lean_array_push(v___x_1479_, v___x_1478_);
return v___x_1480_;
}
}
static uint8_t _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10(void){
_start:
{
uint32_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = 4;
v___x_1486_ = lean_uint32_to_uint8(v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(lean_object* v_ws_1504_, lean_object* v_rootDeps_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___y_1509_; lean_object* v_root_1514_; lean_object* v_lakeEnv_1515_; lean_object* v_lakeArgs_x3f_1516_; lean_object* v___y_1518_; lean_object* v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; lean_object* v_baseName_1668_; lean_object* v_dir_1669_; lean_object* v_config_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_root_1514_ = lean_ctor_get(v_ws_1504_, 0);
lean_inc_ref(v_root_1514_);
v_lakeEnv_1515_ = lean_ctor_get(v_ws_1504_, 1);
lean_inc_ref(v_lakeEnv_1515_);
v_lakeArgs_x3f_1516_ = lean_ctor_get(v_ws_1504_, 4);
lean_inc(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_ws_1504_);
v_baseName_1668_ = lean_ctor_get(v_root_1514_, 1);
lean_inc(v_baseName_1668_);
v_dir_1669_ = lean_ctor_get(v_root_1514_, 4);
lean_inc_ref(v_dir_1669_);
v_config_1670_ = lean_ctor_get(v_root_1514_, 6);
lean_inc_ref(v_config_1670_);
lean_dec_ref(v_root_1514_);
v___x_1671_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_1669_);
v___x_1672_ = l_System_FilePath_join(v_dir_1669_, v___x_1671_);
v___x_1673_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_1672_);
lean_dec_ref(v___x_1672_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1768_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1768_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1768_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
uint8_t v_fixedToolchain_1678_; lean_object* v___x_1679_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1693_; lean_object* v___y_1694_; uint8_t v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v_src_1716_; lean_object* v_tc_x3f_1717_; lean_object* v_clashes_1718_; uint8_t v_fixed_1719_; lean_object* v___y_1743_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_fixedToolchain_1678_ = lean_ctor_get_uint8(v_config_1670_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_1670_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1757_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_1758_ = lean_array_get_size(v_rootDeps_1505_);
v___x_1759_ = lean_nat_dec_lt(v___x_1679_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_inc(v_a_1674_);
v_src_1716_ = v_baseName_1668_;
v_tc_x3f_1717_ = v_a_1674_;
v_clashes_1718_ = v___x_1757_;
v_fixed_1719_ = v_fixedToolchain_1678_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
lean_inc(v_a_1674_);
lean_inc(v_baseName_1668_);
v___x_1760_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1760_, 0, v_baseName_1668_);
lean_ctor_set(v___x_1760_, 1, v_a_1674_);
lean_ctor_set(v___x_1760_, 2, v___x_1757_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*3, v_fixedToolchain_1678_);
v___x_1761_ = lean_nat_dec_le(v___x_1758_, v___x_1758_);
if (v___x_1761_ == 0)
{
if (v___x_1759_ == 0)
{
lean_dec_ref(v___x_1760_);
lean_inc(v_a_1674_);
v_src_1716_ = v_baseName_1668_;
v_tc_x3f_1717_ = v_a_1674_;
v_clashes_1718_ = v___x_1757_;
v_fixed_1719_ = v_fixedToolchain_1678_;
goto v___jp_1715_;
}
else
{
size_t v___x_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v_baseName_1668_);
v___x_1762_ = ((size_t)0ULL);
v___x_1763_ = lean_usize_of_nat(v___x_1758_);
lean_inc_ref(v_dir_1669_);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_1669_, v_rootDeps_1505_, v___x_1762_, v___x_1763_, v___x_1760_, v_a_1506_);
v___y_1743_ = v___x_1764_;
goto v___jp_1742_;
}
}
else
{
size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
lean_dec(v_baseName_1668_);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = lean_usize_of_nat(v___x_1758_);
lean_inc_ref(v_dir_1669_);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_1669_, v_rootDeps_1505_, v___x_1765_, v___x_1766_, v___x_1760_, v_a_1506_);
v___y_1743_ = v___x_1767_;
goto v___jp_1742_;
}
}
v___jp_1680_:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_lt(v___x_1679_, v___y_1681_);
if (v___x_1684_ == 0)
{
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
v___y_1509_ = v___y_1683_;
goto v___jp_1508_;
}
else
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_nat_dec_le(v___y_1681_, v___y_1681_);
if (v___x_1685_ == 0)
{
if (v___x_1684_ == 0)
{
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
v___y_1509_ = v___y_1683_;
goto v___jp_1508_;
}
else
{
size_t v___x_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((size_t)0ULL);
v___x_1687_ = lean_usize_of_nat(v___y_1681_);
lean_dec(v___y_1681_);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_1682_, v___x_1686_, v___x_1687_, v___y_1683_);
lean_dec_ref(v___y_1682_);
v___y_1509_ = v___x_1688_;
goto v___jp_1508_;
}
}
else
{
size_t v___x_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = lean_usize_of_nat(v___y_1681_);
lean_dec(v___y_1681_);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_1682_, v___x_1689_, v___x_1690_, v___y_1683_);
lean_dec_ref(v___y_1682_);
v___y_1509_ = v___x_1691_;
goto v___jp_1508_;
}
}
}
v___jp_1692_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1700_ = lean_string_append(v___y_1697_, v___y_1699_);
lean_dec_ref(v___y_1699_);
v___x_1701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_1702_ = lean_string_append(v___x_1700_, v___x_1701_);
v___x_1703_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_1694_, v___y_1695_);
v___x_1704_ = lean_string_append(v___x_1702_, v___x_1703_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = lean_string_append(v___x_1704_, v___y_1693_);
lean_dec_ref(v___y_1693_);
v___y_1681_ = v___y_1696_;
v___y_1682_ = v___y_1698_;
v___y_1683_ = v___x_1705_;
goto v___jp_1680_;
}
v___jp_1706_:
{
lean_object* v___x_1713_; lean_object* v_toString_1714_; 
v___x_1713_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_1714_ = lean_ctor_get(v___y_1708_, 0);
lean_inc_ref(v_toString_1714_);
lean_dec_ref(v___y_1708_);
v___y_1693_ = v___y_1712_;
v___y_1694_ = v___y_1707_;
v___y_1695_ = v___y_1709_;
v___y_1696_ = v___y_1710_;
v___y_1697_ = v___x_1713_;
v___y_1698_ = v___y_1711_;
v___y_1699_ = v_toString_1714_;
goto v___jp_1692_;
}
v___jp_1715_:
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = lean_array_get_size(v_clashes_1718_);
v___x_1721_ = lean_nat_dec_lt(v___x_1679_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_dec_ref(v_clashes_1718_);
lean_dec(v_src_1716_);
if (lean_obj_tag(v_tc_x3f_1717_) == 1)
{
lean_object* v_val_1722_; lean_object* v_rootToolchainFile_1723_; 
v_val_1722_ = lean_ctor_get(v_tc_x3f_1717_, 0);
lean_inc(v_val_1722_);
lean_dec_ref(v_tc_x3f_1717_);
v_rootToolchainFile_1723_ = l_Lake_joinRelative(v_dir_1669_, v___x_1671_);
if (lean_obj_tag(v_a_1674_) == 0)
{
lean_del_object(v___x_1676_);
v___y_1663_ = v_val_1722_;
v___y_1664_ = v_rootToolchainFile_1723_;
v___y_1665_ = v___x_1721_;
goto v___jp_1662_;
}
else
{
lean_object* v_val_1724_; uint8_t v___x_1725_; 
v_val_1724_ = lean_ctor_get(v_a_1674_, 0);
lean_inc(v_val_1724_);
lean_dec_ref(v_a_1674_);
lean_inc(v_val_1722_);
v___x_1725_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_1724_, v_val_1722_);
if (v___x_1725_ == 0)
{
lean_del_object(v___x_1676_);
v___y_1663_ = v_val_1722_;
v___y_1664_ = v_rootToolchainFile_1723_;
v___y_1665_ = v___x_1725_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
lean_dec_ref(v_rootToolchainFile_1723_);
lean_dec(v_val_1722_);
lean_dec(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_lakeEnv_1515_);
v___x_1726_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_1506_);
v___x_1727_ = lean_apply_2(v_a_1506_, v___x_1726_, lean_box(0));
v___x_1728_ = lean_box(0);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1728_);
v___x_1730_ = v___x_1676_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
lean_dec(v_tc_x3f_1717_);
lean_dec(v_a_1674_);
lean_dec_ref(v_dir_1669_);
lean_dec(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_lakeEnv_1515_);
v___x_1732_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_1506_);
v___x_1733_ = lean_apply_2(v_a_1506_, v___x_1732_, lean_box(0));
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1733_);
v___x_1735_ = v___x_1676_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_del_object(v___x_1676_);
lean_dec(v_a_1674_);
lean_dec_ref(v_dir_1669_);
lean_dec(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_lakeEnv_1515_);
if (lean_obj_tag(v_tc_x3f_1717_) == 1)
{
if (v_fixed_1719_ == 0)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; 
v_val_1737_ = lean_ctor_get(v_tc_x3f_1717_, 0);
lean_inc(v_val_1737_);
lean_dec_ref(v_tc_x3f_1717_);
v___x_1738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_1707_ = v_src_1716_;
v___y_1708_ = v_val_1737_;
v___y_1709_ = v___x_1721_;
v___y_1710_ = v___x_1720_;
v___y_1711_ = v_clashes_1718_;
v___y_1712_ = v___x_1738_;
goto v___jp_1706_;
}
else
{
lean_object* v_val_1739_; lean_object* v___x_1740_; 
v_val_1739_ = lean_ctor_get(v_tc_x3f_1717_, 0);
lean_inc(v_val_1739_);
lean_dec_ref(v_tc_x3f_1717_);
v___x_1740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_1707_ = v_src_1716_;
v___y_1708_ = v_val_1739_;
v___y_1709_ = v___x_1721_;
v___y_1710_ = v___x_1720_;
v___y_1711_ = v_clashes_1718_;
v___y_1712_ = v___x_1740_;
goto v___jp_1706_;
}
}
else
{
lean_object* v___x_1741_; 
lean_dec(v_tc_x3f_1717_);
lean_dec(v_src_1716_);
v___x_1741_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_1681_ = v___x_1720_;
v___y_1682_ = v_clashes_1718_;
v___y_1683_ = v___x_1741_;
goto v___jp_1680_;
}
}
}
v___jp_1742_:
{
if (lean_obj_tag(v___y_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v_src_1745_; lean_object* v_tc_x3f_1746_; lean_object* v_clashes_1747_; uint8_t v_fixed_1748_; 
v_a_1744_ = lean_ctor_get(v___y_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___y_1743_);
v_src_1745_ = lean_ctor_get(v_a_1744_, 0);
lean_inc(v_src_1745_);
v_tc_x3f_1746_ = lean_ctor_get(v_a_1744_, 1);
lean_inc(v_tc_x3f_1746_);
v_clashes_1747_ = lean_ctor_get(v_a_1744_, 2);
lean_inc_ref(v_clashes_1747_);
v_fixed_1748_ = lean_ctor_get_uint8(v_a_1744_, sizeof(void*)*3);
lean_dec(v_a_1744_);
v_src_1716_ = v_src_1745_;
v_tc_x3f_1717_ = v_tc_x3f_1746_;
v_clashes_1718_ = v_clashes_1747_;
v_fixed_1719_ = v_fixed_1748_;
goto v___jp_1715_;
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_del_object(v___x_1676_);
lean_dec(v_a_1674_);
lean_dec_ref(v_dir_1669_);
lean_dec(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_lakeEnv_1515_);
v_a_1749_ = lean_ctor_get(v___y_1743_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___y_1743_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___y_1743_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___y_1743_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v_config_1670_);
lean_dec_ref(v_dir_1669_);
lean_dec(v_baseName_1668_);
lean_dec(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_lakeEnv_1515_);
v_a_1769_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1771_ = v___x_1673_;
v_isShared_1772_ = v_isSharedCheck_1781_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1673_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1781_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1773_ = lean_io_error_to_string(v_a_1769_);
v___x_1774_ = 3;
v___x_1775_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set_uint8(v___x_1775_, sizeof(void*)*1, v___x_1774_);
lean_inc_ref(v_a_1506_);
v___x_1776_ = lean_apply_2(v_a_1506_, v___x_1775_, lean_box(0));
v___x_1777_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1777_);
v___x_1779_ = v___x_1771_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
v___jp_1508_:
{
uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1510_ = 2;
v___x_1511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1511_, 0, v___y_1509_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*1, v___x_1510_);
lean_inc_ref(v_a_1506_);
v___x_1512_ = lean_apply_2(v_a_1506_, v___x_1511_, lean_box(0));
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
v___jp_1517_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1522_ = lean_string_append(v___y_1518_, v___y_1521_);
v___x_1523_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_1524_ = lean_string_append(v___x_1522_, v___x_1523_);
v___x_1525_ = 1;
v___x_1526_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*1, v___x_1525_);
lean_inc_ref(v_a_1506_);
v___x_1527_ = lean_apply_2(v_a_1506_, v___x_1526_, lean_box(0));
v___x_1528_ = l_IO_FS_writeFile(v___y_1519_, v___y_1521_);
lean_dec_ref(v___y_1519_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_dec_ref(v___x_1528_);
if (lean_obj_tag(v_lakeArgs_x3f_1516_) == 1)
{
lean_object* v_elan_x3f_1529_; 
v_elan_x3f_1529_ = lean_ctor_get(v_lakeEnv_1515_, 2);
if (lean_obj_tag(v_elan_x3f_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v_val_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_elan_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_val_1530_ = lean_ctor_get(v_lakeArgs_x3f_1516_, 0);
lean_inc(v_val_1530_);
lean_dec_ref(v_lakeArgs_x3f_1516_);
v_val_1531_ = lean_ctor_get(v_elan_x3f_1529_, 0);
v___x_1532_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_1506_);
v___x_1533_ = lean_apply_2(v_a_1506_, v___x_1532_, lean_box(0));
v___x_1534_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_1535_ = lean_ctor_get(v_val_1531_, 1);
lean_inc_ref(v_elan_1535_);
v___x_1536_ = 1;
v___x_1537_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_1538_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_1539_ = lean_array_push(v___x_1538_, v___y_1521_);
v___x_1540_ = lean_array_push(v___x_1539_, v___x_1537_);
v___x_1541_ = l_Array_append___redArg(v___x_1540_, v_val_1530_);
lean_dec(v_val_1530_);
v___x_1542_ = lean_box(0);
v___x_1543_ = l_Lake_Env_noToolchainVars(v_lakeEnv_1515_);
v___x_1544_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1544_, 0, v___x_1534_);
lean_ctor_set(v___x_1544_, 1, v_elan_1535_);
lean_ctor_set(v___x_1544_, 2, v___x_1541_);
lean_ctor_set(v___x_1544_, 3, v___x_1542_);
lean_ctor_set(v___x_1544_, 4, v___x_1543_);
lean_ctor_set_uint8(v___x_1544_, sizeof(void*)*5, v___x_1536_);
lean_ctor_set_uint8(v___x_1544_, sizeof(void*)*5 + 1, v___y_1520_);
v___x_1545_ = lean_io_process_spawn(v___x_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = lean_io_process_child_wait(v___x_1534_, v_a_1546_);
lean_dec(v_a_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; uint32_t v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = lean_unbox_uint32(v_a_1548_);
lean_dec(v_a_1548_);
v___x_1550_ = lean_uint32_to_uint8(v___x_1549_);
v___x_1551_ = lean_io_exit(v___x_1550_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1572_; 
v_a_1560_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1562_ = v___x_1551_;
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1551_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1572_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1564_ = lean_io_error_to_string(v_a_1560_);
v___x_1565_ = 3;
v___x_1566_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*1, v___x_1565_);
lean_inc_ref(v_a_1506_);
v___x_1567_ = lean_apply_2(v_a_1506_, v___x_1566_, lean_box(0));
v___x_1568_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1568_);
v___x_1570_ = v___x_1562_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
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
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1585_; 
v_a_1573_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1575_ = v___x_1547_;
v_isShared_1576_ = v_isSharedCheck_1585_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1547_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1585_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1577_ = lean_io_error_to_string(v_a_1573_);
v___x_1578_ = 3;
v___x_1579_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*1, v___x_1578_);
lean_inc_ref(v_a_1506_);
v___x_1580_ = lean_apply_2(v_a_1506_, v___x_1579_, lean_box(0));
v___x_1581_ = lean_box(0);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1581_);
v___x_1583_ = v___x_1575_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1598_; 
v_a_1586_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1588_ = v___x_1545_;
v_isShared_1589_ = v_isSharedCheck_1598_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1545_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1598_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1590_ = lean_io_error_to_string(v_a_1586_);
v___x_1591_ = 3;
v___x_1592_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set_uint8(v___x_1592_, sizeof(void*)*1, v___x_1591_);
lean_inc_ref(v_a_1506_);
v___x_1593_ = lean_apply_2(v_a_1506_, v___x_1592_, lean_box(0));
v___x_1594_ = lean_box(0);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1594_);
v___x_1596_ = v___x_1588_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; lean_object* v___x_1602_; 
lean_dec_ref(v_lakeArgs_x3f_1516_);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v_lakeEnv_1515_);
v___x_1599_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_1506_);
v___x_1600_ = lean_apply_2(v_a_1506_, v___x_1599_, lean_box(0));
v___x_1601_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_1602_ = lean_io_exit(v___x_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1623_; 
v_a_1611_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1613_ = v___x_1602_;
v_isShared_1614_ = v_isSharedCheck_1623_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1602_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1623_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1615_ = lean_io_error_to_string(v_a_1611_);
v___x_1616_ = 3;
v___x_1617_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*1, v___x_1616_);
lean_inc_ref(v_a_1506_);
v___x_1618_ = lean_apply_2(v_a_1506_, v___x_1617_, lean_box(0));
v___x_1619_ = lean_box(0);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1619_);
v___x_1621_ = v___x_1613_;
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
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; 
lean_dec_ref(v___y_1521_);
lean_dec(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_lakeEnv_1515_);
v___x_1624_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_1506_);
v___x_1625_ = lean_apply_2(v_a_1506_, v___x_1624_, lean_box(0));
v___x_1626_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_1627_ = lean_io_exit(v___x_1626_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1648_; 
v_a_1636_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1638_ = v___x_1627_;
v_isShared_1639_ = v_isSharedCheck_1648_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1627_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1648_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1640_ = lean_io_error_to_string(v_a_1636_);
v___x_1641_ = 3;
v___x_1642_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*1, v___x_1641_);
lean_inc_ref(v_a_1506_);
v___x_1643_ = lean_apply_2(v_a_1506_, v___x_1642_, lean_box(0));
v___x_1644_ = lean_box(0);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1644_);
v___x_1646_ = v___x_1638_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v___y_1521_);
lean_dec(v_lakeArgs_x3f_1516_);
lean_dec_ref(v_lakeEnv_1515_);
v_a_1649_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1651_ = v___x_1528_;
v_isShared_1652_ = v_isSharedCheck_1661_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1528_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1661_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1653_ = lean_io_error_to_string(v_a_1649_);
v___x_1654_ = 3;
v___x_1655_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set_uint8(v___x_1655_, sizeof(void*)*1, v___x_1654_);
lean_inc_ref(v_a_1506_);
v___x_1656_ = lean_apply_2(v_a_1506_, v___x_1655_, lean_box(0));
v___x_1657_ = lean_box(0);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1657_);
v___x_1659_ = v___x_1651_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
v___jp_1662_:
{
lean_object* v___x_1666_; lean_object* v_toString_1667_; 
v___x_1666_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_1667_ = lean_ctor_get(v___y_1663_, 0);
lean_inc_ref(v_toString_1667_);
lean_dec_ref(v___y_1663_);
v___y_1518_ = v___x_1666_;
v___y_1519_ = v___y_1664_;
v___y_1520_ = v___y_1665_;
v___y_1521_ = v_toString_1667_;
goto v___jp_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___boxed(lean_object* v_ws_1782_, lean_object* v_rootDeps_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain(v_ws_1782_, v_rootDeps_1783_, v_a_1784_);
lean_dec_ref(v_a_1784_);
lean_dec_ref(v_rootDeps_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0(lean_object* v_x_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_inc_ref(v___y_1789_);
v___x_1791_ = lean_apply_2(v___y_1789_, v___y_1788_, lean_box(0));
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0___boxed(lean_object* v_x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___lam__0(v_x_1793_, v___y_1794_, v___y_1795_);
lean_dec_ref(v___y_1795_);
return v_res_1797_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0(void){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_instMonadEIO(lean_box(0));
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__0);
v___x_1800_ = l_ReaderT_instMonad___redArg(v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep(lean_object* v_leanOpts_1802_, lean_object* v_wsIdx_1803_, lean_object* v_dep_1804_, lean_object* v_matDep_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_opts_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_opts_1813_ = lean_ctor_get(v_dep_1804_, 4);
lean_inc(v_opts_1813_);
lean_dec_ref(v_dep_1804_);
v___x_1814_ = 1;
v___x_1815_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_matDep_1805_);
v___x_1818_ = l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(v_wsIdx_1803_, v_matDep_1805_, v_opts_1813_, v_leanOpts_1802_, v___x_1814_, v_a_1806_, v___x_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v_a_1820_; lean_object* v_snd_1822_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
v_a_1820_ = lean_ctor_get(v___x_1818_, 1);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1818_);
v___x_1850_ = lean_array_get_size(v_a_1820_);
v___x_1851_ = lean_nat_dec_lt(v___x_1816_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_dec(v_a_1820_);
v_snd_1822_ = v_a_1807_;
goto v___jp_1821_;
}
else
{
lean_object* v___f_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___f_1852_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__2));
v___x_1853_ = lean_box(0);
v___x_1854_ = lean_nat_dec_le(v___x_1850_, v___x_1850_);
if (v___x_1854_ == 0)
{
if (v___x_1851_ == 0)
{
lean_dec(v_a_1820_);
v_snd_1822_ = v_a_1807_;
goto v___jp_1821_;
}
else
{
size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_4913__overap_1857_; lean_object* v___x_1858_; 
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1850_);
v___x_4913__overap_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1815_, v___f_1852_, v_a_1820_, v___x_1855_, v___x_1856_, v___x_1853_);
lean_inc_ref(v_a_1808_);
v___x_1858_ = lean_apply_2(v___x_4913__overap_1857_, v_a_1808_, lean_box(0));
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_dec_ref(v___x_1858_);
v_snd_1822_ = v_a_1807_;
goto v___jp_1821_;
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1819_);
lean_dec(v_a_1807_);
lean_dec_ref(v_matDep_1805_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
else
{
size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_4923__overap_1869_; lean_object* v___x_1870_; 
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = lean_usize_of_nat(v___x_1850_);
v___x_4923__overap_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1815_, v___f_1852_, v_a_1820_, v___x_1867_, v___x_1868_, v___x_1853_);
lean_inc_ref(v_a_1808_);
v___x_1870_ = lean_apply_2(v___x_4923__overap_1869_, v_a_1808_, lean_box(0));
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_dec_ref(v___x_1870_);
v_snd_1822_ = v_a_1807_;
goto v___jp_1821_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_a_1819_);
lean_dec(v_a_1807_);
lean_dec_ref(v_matDep_1805_);
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
v___jp_1821_:
{
lean_object* v_fst_1823_; lean_object* v___x_1824_; 
v_fst_1823_ = lean_ctor_get(v_a_1819_, 0);
lean_inc(v_fst_1823_);
v___x_1824_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_1823_, v_matDep_1805_, v_snd_1822_, v_a_1808_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1841_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1841_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1841_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_snd_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1839_; 
v_snd_1829_ = lean_ctor_get(v_a_1825_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v_a_1825_, 0);
lean_dec(v_unused_1840_);
v___x_1831_ = v_a_1825_;
v_isShared_1832_ = v_isSharedCheck_1839_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_snd_1829_);
lean_dec(v_a_1825_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1839_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_a_1819_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1819_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_snd_1829_);
v___x_1834_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1836_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1834_);
v___x_1836_ = v___x_1827_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_a_1819_);
v_a_1842_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1824_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1824_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
lean_dec(v_a_1807_);
lean_dec_ref(v_matDep_1805_);
v_a_1879_ = lean_ctor_get(v___x_1818_, 1);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1818_);
v___x_1880_ = lean_array_get_size(v_a_1879_);
v___x_1881_ = lean_nat_dec_lt(v___x_1816_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec(v_a_1879_);
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v___f_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___f_1884_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__2));
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_nat_dec_le(v___x_1880_, v___x_1880_);
if (v___x_1886_ == 0)
{
if (v___x_1881_ == 0)
{
lean_dec(v_a_1879_);
goto v___jp_1810_;
}
else
{
size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_4946__overap_1889_; lean_object* v___x_1890_; 
v___x_1887_ = ((size_t)0ULL);
v___x_1888_ = lean_usize_of_nat(v___x_1880_);
v___x_4946__overap_1889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1815_, v___f_1884_, v_a_1879_, v___x_1887_, v___x_1888_, v___x_1885_);
lean_inc_ref(v_a_1808_);
v___x_1890_ = lean_apply_2(v___x_4946__overap_1889_, v_a_1808_, lean_box(0));
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_dec_ref(v___x_1890_);
goto v___jp_1810_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
else
{
size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_4955__overap_1901_; lean_object* v___x_1902_; 
v___x_1899_ = ((size_t)0ULL);
v___x_1900_ = lean_usize_of_nat(v___x_1880_);
v___x_4955__overap_1901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1815_, v___f_1884_, v_a_1879_, v___x_1899_, v___x_1900_, v___x_1885_);
lean_inc_ref(v_a_1808_);
v___x_1902_ = lean_apply_2(v___x_4955__overap_1901_, v_a_1808_, lean_box(0));
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_dec_ref(v___x_1902_);
goto v___jp_1810_;
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
}
v___jp_1810_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___boxed(lean_object* v_leanOpts_1911_, lean_object* v_wsIdx_1912_, lean_object* v_dep_1913_, lean_object* v_matDep_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep(v_leanOpts_1911_, v_wsIdx_1912_, v_dep_1913_, v_matDep_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec_ref(v_a_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep(lean_object* v_leanOpts_1920_, lean_object* v_pkg_1921_, lean_object* v_dep_1922_, lean_object* v_wsIdx_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v___x_1931_; 
lean_inc_ref(v_dep_1922_);
lean_inc_ref(v_a_1924_);
v___x_1931_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v_a_1924_, v_pkg_1921_, v_dep_1922_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_2038_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_2038_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_2038_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v_opts_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_fst_1936_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_fst_1936_);
v_snd_1937_ = lean_ctor_get(v_a_1932_, 1);
lean_inc(v_snd_1937_);
lean_dec(v_a_1932_);
v_opts_1938_ = lean_ctor_get(v_dep_1922_, 4);
lean_inc(v_opts_1938_);
lean_dec_ref(v_dep_1922_);
v___x_1939_ = 1;
v___x_1940_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__1);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc(v_fst_1936_);
v___x_1943_ = l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(v_wsIdx_1923_, v_fst_1936_, v_opts_1938_, v_leanOpts_1920_, v___x_1939_, v_a_1924_, v___x_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v_a_1945_; lean_object* v_snd_1947_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
lean_del_object(v___x_1934_);
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
v_a_1945_ = lean_ctor_get(v___x_1943_, 1);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1943_);
v___x_1975_ = lean_array_get_size(v_a_1945_);
v___x_1976_ = lean_nat_dec_lt(v___x_1941_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_dec(v_a_1945_);
v_snd_1947_ = v_snd_1937_;
goto v___jp_1946_;
}
else
{
lean_object* v___f_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___f_1977_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__2));
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_nat_dec_le(v___x_1975_, v___x_1975_);
if (v___x_1979_ == 0)
{
if (v___x_1976_ == 0)
{
lean_dec(v_a_1945_);
v_snd_1947_ = v_snd_1937_;
goto v___jp_1946_;
}
else
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_5272__overap_1982_; lean_object* v___x_1983_; 
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = lean_usize_of_nat(v___x_1975_);
v___x_5272__overap_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1940_, v___f_1977_, v_a_1945_, v___x_1980_, v___x_1981_, v___x_1978_);
lean_inc_ref(v_a_1926_);
v___x_1983_ = lean_apply_2(v___x_5272__overap_1982_, v_a_1926_, lean_box(0));
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_dec_ref(v___x_1983_);
v_snd_1947_ = v_snd_1937_;
goto v___jp_1946_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_a_1944_);
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
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
}
else
{
size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_5281__overap_1994_; lean_object* v___x_1995_; 
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = lean_usize_of_nat(v___x_1975_);
v___x_5281__overap_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1940_, v___f_1977_, v_a_1945_, v___x_1992_, v___x_1993_, v___x_1978_);
lean_inc_ref(v_a_1926_);
v___x_1995_ = lean_apply_2(v___x_5281__overap_1994_, v_a_1926_, lean_box(0));
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_dec_ref(v___x_1995_);
v_snd_1947_ = v_snd_1937_;
goto v___jp_1946_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_a_1944_);
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
v___jp_1946_:
{
lean_object* v_fst_1948_; lean_object* v___x_1949_; 
v_fst_1948_ = lean_ctor_get(v_a_1944_, 0);
lean_inc(v_fst_1948_);
v___x_1949_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_1948_, v_fst_1936_, v_snd_1947_, v_a_1926_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1966_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1966_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1966_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_snd_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1964_; 
v_snd_1954_ = lean_ctor_get(v_a_1950_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_a_1950_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v_a_1950_, 0);
lean_dec(v_unused_1965_);
v___x_1956_ = v_a_1950_;
v_isShared_1957_ = v_isSharedCheck_1964_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_snd_1954_);
lean_dec(v_a_1950_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1964_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v_a_1944_);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1944_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_snd_1954_);
v___x_1959_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1959_);
v___x_1961_ = v___x_1952_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
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
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_a_1944_);
v_a_1967_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1949_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1949_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
lean_dec(v_snd_1937_);
lean_dec(v_fst_1936_);
v_a_2004_ = lean_ctor_get(v___x_1943_, 1);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_1943_);
v___x_2005_ = lean_array_get_size(v_a_2004_);
v___x_2006_ = lean_nat_dec_lt(v___x_1941_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_dec(v_a_2004_);
v___x_2007_ = lean_box(0);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 1);
lean_ctor_set(v___x_1934_, 0, v___x_2007_);
v___x_2009_ = v___x_1934_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
else
{
lean_object* v___f_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
lean_del_object(v___x_1934_);
v___f_2011_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_loadUpdatedDep___closed__2));
v___x_2012_ = lean_box(0);
v___x_2013_ = lean_nat_dec_le(v___x_2005_, v___x_2005_);
if (v___x_2013_ == 0)
{
if (v___x_2006_ == 0)
{
lean_dec(v_a_2004_);
goto v___jp_1928_;
}
else
{
size_t v___x_2014_; size_t v___x_2015_; lean_object* v___x_5303__overap_2016_; lean_object* v___x_2017_; 
v___x_2014_ = ((size_t)0ULL);
v___x_2015_ = lean_usize_of_nat(v___x_2005_);
v___x_5303__overap_2016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1940_, v___f_2011_, v_a_2004_, v___x_2014_, v___x_2015_, v___x_2012_);
lean_inc_ref(v_a_1926_);
v___x_2017_ = lean_apply_2(v___x_5303__overap_2016_, v_a_1926_, lean_box(0));
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_dec_ref(v___x_2017_);
goto v___jp_1928_;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
else
{
size_t v___x_2026_; size_t v___x_2027_; lean_object* v___x_5312__overap_2028_; lean_object* v___x_2029_; 
v___x_2026_ = ((size_t)0ULL);
v___x_2027_ = lean_usize_of_nat(v___x_2005_);
v___x_5312__overap_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1940_, v___f_2011_, v_a_2004_, v___x_2026_, v___x_2027_, v___x_2012_);
lean_inc_ref(v_a_1926_);
v___x_2029_ = lean_apply_2(v___x_5312__overap_2028_, v_a_1926_, lean_box(0));
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref(v___x_2029_);
goto v___jp_1928_;
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
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
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_a_1924_);
lean_dec(v_wsIdx_1923_);
lean_dec_ref(v_dep_1922_);
lean_dec_ref(v_leanOpts_1920_);
v_a_2039_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_1931_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_1931_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
v___jp_1928_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_box(0);
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep___boxed(lean_object* v_leanOpts_2047_, lean_object* v_pkg_2048_, lean_object* v_dep_2049_, lean_object* v_wsIdx_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_updateAndLoadDep(v_leanOpts_2047_, v_pkg_2048_, v_dep_2049_, v_wsIdx_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec_ref(v_a_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(lean_object* v___y_2056_, lean_object* v_ws_2057_, lean_object* v_pkg_2058_, lean_object* v_dep_2059_, lean_object* v_a_2060_){
_start:
{
uint8_t v___y_2063_; lean_object* v___y_2064_; lean_object* v_name_2092_; lean_object* v___x_2093_; 
v_name_2092_ = lean_ctor_get(v_dep_2059_, 0);
v___x_2093_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2060_, v_name_2092_);
if (lean_obj_tag(v___x_2093_) == 1)
{
lean_object* v_root_2094_; lean_object* v_config_2095_; lean_object* v_val_2096_; lean_object* v_lakeEnv_2097_; lean_object* v_dir_2098_; lean_object* v_toWorkspaceConfig_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec_ref(v_dep_2059_);
lean_dec_ref(v_pkg_2058_);
v_root_2094_ = lean_ctor_get(v_ws_2057_, 0);
lean_inc_ref(v_root_2094_);
v_config_2095_ = lean_ctor_get(v_root_2094_, 6);
lean_inc_ref(v_config_2095_);
v_val_2096_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_val_2096_);
lean_dec_ref(v___x_2093_);
v_lakeEnv_2097_ = lean_ctor_get(v_ws_2057_, 1);
lean_inc_ref(v_lakeEnv_2097_);
lean_dec_ref(v_ws_2057_);
v_dir_2098_ = lean_ctor_get(v_root_2094_, 4);
lean_inc_ref(v_dir_2098_);
lean_dec_ref(v_root_2094_);
v_toWorkspaceConfig_2099_ = lean_ctor_get(v_config_2095_, 0);
lean_inc_ref(v_toWorkspaceConfig_2099_);
lean_dec_ref(v_config_2095_);
v___x_2100_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2099_);
v___x_2101_ = l_Lake_PackageEntry_materialize(v_val_2096_, v_lakeEnv_2097_, v_dir_2098_, v___x_2100_, v___y_2056_);
lean_dec_ref(v_lakeEnv_2097_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_a_2102_);
lean_ctor_set(v___x_2106_, 1, v_a_2060_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_a_2060_);
v_a_2111_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2101_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2101_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_wsIdx_2119_; lean_object* v_relDir_2120_; uint8_t v___y_2122_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
lean_dec(v___x_2093_);
v_wsIdx_2119_ = lean_ctor_get(v_pkg_2058_, 0);
lean_inc(v_wsIdx_2119_);
v_relDir_2120_ = lean_ctor_get(v_pkg_2058_, 5);
lean_inc_ref(v_relDir_2120_);
lean_dec_ref(v_pkg_2058_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_nat_dec_eq(v_wsIdx_2119_, v___x_2126_);
lean_dec(v_wsIdx_2119_);
if (v___x_2127_ == 0)
{
uint8_t v___x_2128_; 
v___x_2128_ = 1;
v___y_2122_ = v___x_2128_;
goto v___jp_2121_;
}
else
{
uint8_t v___x_2129_; 
v___x_2129_ = 0;
v___y_2122_ = v___x_2129_;
goto v___jp_2121_;
}
v___jp_2121_:
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___closed__0));
v___x_2124_ = lean_string_dec_eq(v_relDir_2120_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lake_joinRelative(v_relDir_2120_, v___x_2123_);
v___y_2063_ = v___y_2122_;
v___y_2064_ = v___x_2125_;
goto v___jp_2062_;
}
else
{
v___y_2063_ = v___y_2122_;
v___y_2064_ = v_relDir_2120_;
goto v___jp_2062_;
}
}
}
v___jp_2062_:
{
lean_object* v_root_2065_; lean_object* v_config_2066_; lean_object* v_lakeEnv_2067_; lean_object* v_dir_2068_; lean_object* v_toWorkspaceConfig_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_root_2065_ = lean_ctor_get(v_ws_2057_, 0);
lean_inc_ref(v_root_2065_);
v_config_2066_ = lean_ctor_get(v_root_2065_, 6);
lean_inc_ref(v_config_2066_);
v_lakeEnv_2067_ = lean_ctor_get(v_ws_2057_, 1);
lean_inc_ref(v_lakeEnv_2067_);
lean_dec_ref(v_ws_2057_);
v_dir_2068_ = lean_ctor_get(v_root_2065_, 4);
lean_inc_ref(v_dir_2068_);
lean_dec_ref(v_root_2065_);
v_toWorkspaceConfig_2069_ = lean_ctor_get(v_config_2066_, 0);
lean_inc_ref(v_toWorkspaceConfig_2069_);
lean_dec_ref(v_config_2066_);
v___x_2070_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2069_);
v___x_2071_ = l_Lake_Dependency_materialize(v_dep_2059_, v___y_2063_, v_lakeEnv_2067_, v_dir_2068_, v___x_2070_, v___y_2064_, v___y_2056_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2083_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_manifestEntry_2076_; lean_object* v_name_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v_manifestEntry_2076_ = lean_ctor_get(v_a_2072_, 3);
v_name_2077_ = lean_ctor_get(v_manifestEntry_2076_, 0);
lean_inc_ref(v_manifestEntry_2076_);
lean_inc(v_name_2077_);
v___x_2078_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2077_, v_manifestEntry_2076_, v_a_2060_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v_a_2072_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v___x_2079_);
v___x_2081_ = v___x_2074_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_a_2060_);
v_a_2084_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2071_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2071_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0___boxed(lean_object* v___y_2130_, lean_object* v_ws_2131_, lean_object* v_pkg_2132_, lean_object* v_dep_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2130_, v_ws_2131_, v_pkg_2132_, v_dep_2133_, v_a_2134_);
lean_dec_ref(v___y_2130_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(lean_object* v___y_2137_, lean_object* v_pkg_2138_, lean_object* v_matDep_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_manifest_x3f_2142_; 
v_manifest_x3f_2142_ = lean_ctor_get(v_matDep_2139_, 2);
lean_inc_ref(v_manifest_x3f_2142_);
lean_dec_ref(v_matDep_2139_);
if (lean_obj_tag(v_manifest_x3f_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2179_; 
v_a_2143_ = lean_ctor_get(v_manifest_x3f_2142_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_manifest_x3f_2142_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2145_ = v_manifest_x3f_2142_;
v_isShared_2146_ = v_isSharedCheck_2179_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v_manifest_x3f_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2179_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
if (lean_obj_tag(v_a_2143_) == 11)
{
lean_object* v_baseName_2147_; lean_object* v_dir_2148_; lean_object* v_relManifestFile_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec_ref(v_a_2143_);
v_baseName_2147_ = lean_ctor_get(v_pkg_2138_, 1);
lean_inc(v_baseName_2147_);
v_dir_2148_ = lean_ctor_get(v_pkg_2138_, 4);
lean_inc_ref(v_dir_2148_);
v_relManifestFile_2149_ = lean_ctor_get(v_pkg_2138_, 9);
lean_inc_ref(v_relManifestFile_2149_);
lean_dec_ref(v_pkg_2138_);
v___x_2150_ = 0;
v___x_2151_ = l_Lean_Name_toString(v_baseName_2147_, v___x_2150_);
v___x_2152_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__0));
v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
v___x_2154_ = l_Lake_joinRelative(v_dir_2148_, v_relManifestFile_2149_);
v___x_2155_ = lean_string_append(v___x_2153_, v___x_2154_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2157_ = lean_string_append(v___x_2155_, v___x_2156_);
v___x_2158_ = 2;
v___x_2159_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*1, v___x_2158_);
v___x_2160_ = lean_apply_2(v___y_2137_, v___x_2159_, lean_box(0));
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_a_2140_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2161_);
v___x_2163_ = v___x_2145_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
else
{
lean_object* v_baseName_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v_baseName_2165_ = lean_ctor_get(v_pkg_2138_, 1);
lean_inc(v_baseName_2165_);
lean_dec_ref(v_pkg_2138_);
v___x_2166_ = 0;
v___x_2167_ = l_Lean_Name_toString(v_baseName_2165_, v___x_2166_);
v___x_2168_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___closed__1));
v___x_2169_ = lean_string_append(v___x_2167_, v___x_2168_);
v___x_2170_ = lean_io_error_to_string(v_a_2143_);
v___x_2171_ = lean_string_append(v___x_2169_, v___x_2170_);
lean_dec_ref(v___x_2170_);
v___x_2172_ = 2;
v___x_2173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2173_, 0, v___x_2171_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*1, v___x_2172_);
v___x_2174_ = lean_apply_2(v___y_2137_, v___x_2173_, lean_box(0));
v___x_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v_a_2140_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2175_);
v___x_2177_ = v___x_2145_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v___y_2137_);
v_a_2180_ = lean_ctor_get(v_manifest_x3f_2142_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_manifest_x3f_2142_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2182_ = v_manifest_x3f_2142_;
v_isShared_2183_ = v_isSharedCheck_2204_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v_manifest_x3f_2142_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2204_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_packages_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_packages_2184_ = lean_ctor_get(v_a_2180_, 3);
lean_inc_ref(v_packages_2184_);
lean_dec(v_a_2180_);
v___x_2185_ = lean_unsigned_to_nat(0u);
v___x_2186_ = lean_array_get_size(v_packages_2184_);
v___x_2187_ = lean_box(0);
v___x_2188_ = lean_nat_dec_lt(v___x_2185_, v___x_2186_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_dec_ref(v_packages_2184_);
lean_dec_ref(v_pkg_2138_);
v___x_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v_a_2140_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2189_);
v___x_2191_ = v___x_2182_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
else
{
uint8_t v___x_2193_; 
v___x_2193_ = lean_nat_dec_le(v___x_2186_, v___x_2186_);
if (v___x_2193_ == 0)
{
if (v___x_2188_ == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_dec_ref(v_packages_2184_);
lean_dec_ref(v_pkg_2138_);
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2187_);
lean_ctor_set(v___x_2194_, 1, v_a_2140_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2194_);
v___x_2196_ = v___x_2182_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
else
{
size_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
lean_del_object(v___x_2182_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = lean_usize_of_nat(v___x_2186_);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_pkg_2138_, v_packages_2184_, v___x_2198_, v___x_2199_, v___x_2187_, v_a_2140_);
lean_dec_ref(v_packages_2184_);
return v___x_2200_;
}
}
else
{
size_t v___x_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
lean_del_object(v___x_2182_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = lean_usize_of_nat(v___x_2186_);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_addDependencyEntries_spec__0___redArg(v_pkg_2138_, v_packages_2184_, v___x_2201_, v___x_2202_, v___x_2187_, v_a_2140_);
lean_dec_ref(v_packages_2184_);
return v___x_2203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1___boxed(lean_object* v___y_2205_, lean_object* v_pkg_2206_, lean_object* v_matDep_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2205_, v_pkg_2206_, v_matDep_2207_, v_a_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(lean_object* v_leanOpts_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2222_; 
lean_inc_ref(v___y_2213_);
lean_inc_ref(v___y_2215_);
v___x_2222_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2217_, v___y_2215_, v___y_2212_, v___y_2213_, v___y_2216_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2322_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2322_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2322_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_fst_2227_; lean_object* v_snd_2228_; lean_object* v_opts_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v_fst_2227_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_fst_2227_);
v_snd_2228_ = lean_ctor_get(v_a_2223_, 1);
lean_inc(v_snd_2228_);
lean_dec(v_a_2223_);
v_opts_2229_ = lean_ctor_get(v___y_2213_, 4);
lean_inc(v_opts_2229_);
lean_dec_ref(v___y_2213_);
v___x_2230_ = 1;
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc(v_fst_2227_);
v___x_2233_ = l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(v___y_2214_, v_fst_2227_, v_opts_2229_, v_leanOpts_2211_, v___x_2230_, v___y_2215_, v___x_2232_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v_a_2235_; lean_object* v_snd_2237_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
lean_del_object(v___x_2225_);
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
v_a_2235_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2233_);
v___x_2265_ = lean_array_get_size(v_a_2235_);
v___x_2266_ = lean_nat_dec_lt(v___x_2231_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_dec(v_a_2235_);
v_snd_2237_ = v_snd_2228_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = lean_box(0);
v___x_2268_ = lean_nat_dec_le(v___x_2265_, v___x_2265_);
if (v___x_2268_ == 0)
{
if (v___x_2266_ == 0)
{
lean_dec(v_a_2235_);
v_snd_2237_ = v_snd_2228_;
goto v___jp_2236_;
}
else
{
size_t v___x_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = ((size_t)0ULL);
v___x_2270_ = lean_usize_of_nat(v___x_2265_);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2235_, v___x_2269_, v___x_2270_, v___x_2267_, v___y_2217_);
lean_dec(v_a_2235_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_dec_ref(v___x_2271_);
v_snd_2237_ = v_snd_2228_;
goto v___jp_2236_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_a_2234_);
lean_dec(v_snd_2228_);
lean_dec(v_fst_2227_);
lean_dec_ref(v___y_2217_);
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
else
{
size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((size_t)0ULL);
v___x_2281_ = lean_usize_of_nat(v___x_2265_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2235_, v___x_2280_, v___x_2281_, v___x_2267_, v___y_2217_);
lean_dec(v_a_2235_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_dec_ref(v___x_2282_);
v_snd_2237_ = v_snd_2228_;
goto v___jp_2236_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_a_2234_);
lean_dec(v_snd_2228_);
lean_dec(v_fst_2227_);
lean_dec_ref(v___y_2217_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
v___jp_2236_:
{
lean_object* v_fst_2238_; lean_object* v___x_2239_; 
v_fst_2238_ = lean_ctor_get(v_a_2234_, 0);
lean_inc(v_fst_2238_);
v___x_2239_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2217_, v_fst_2238_, v_fst_2227_, v_snd_2237_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2256_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2256_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2256_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_snd_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2254_; 
v_snd_2244_ = lean_ctor_get(v_a_2240_, 1);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; 
v_unused_2255_ = lean_ctor_get(v_a_2240_, 0);
lean_dec(v_unused_2255_);
v___x_2246_ = v_a_2240_;
v_isShared_2247_ = v_isSharedCheck_2254_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_snd_2244_);
lean_dec(v_a_2240_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2254_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_a_2234_);
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2234_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_snd_2244_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2249_);
v___x_2251_ = v___x_2242_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_a_2234_);
v_a_2257_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2239_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2239_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; 
lean_dec(v_snd_2228_);
lean_dec(v_fst_2227_);
v_a_2291_ = lean_ctor_get(v___x_2233_, 1);
lean_inc(v_a_2291_);
lean_dec_ref(v___x_2233_);
v___x_2292_ = lean_array_get_size(v_a_2291_);
v___x_2293_ = lean_nat_dec_lt(v___x_2231_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec(v_a_2291_);
lean_dec_ref(v___y_2217_);
v___x_2294_ = lean_box(0);
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 1);
lean_ctor_set(v___x_2225_, 0, v___x_2294_);
v___x_2296_ = v___x_2225_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
else
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
lean_del_object(v___x_2225_);
v___x_2298_ = lean_box(0);
v___x_2299_ = lean_nat_dec_le(v___x_2292_, v___x_2292_);
if (v___x_2299_ == 0)
{
if (v___x_2293_ == 0)
{
lean_dec(v_a_2291_);
lean_dec_ref(v___y_2217_);
goto v___jp_2219_;
}
else
{
size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2292_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2291_, v___x_2300_, v___x_2301_, v___x_2298_, v___y_2217_);
lean_dec_ref(v___y_2217_);
lean_dec(v_a_2291_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_dec_ref(v___x_2302_);
goto v___jp_2219_;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
else
{
size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = lean_usize_of_nat(v___x_2292_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2291_, v___x_2311_, v___x_2312_, v___x_2298_, v___y_2217_);
lean_dec_ref(v___y_2217_);
lean_dec(v_a_2291_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_dec_ref(v___x_2313_);
goto v___jp_2219_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
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
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec_ref(v_leanOpts_2211_);
v_a_2323_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2222_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2222_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
v___jp_2219_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0___boxed(lean_object* v_leanOpts_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_leanOpts_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__1(lean_object* v_leanOpts_2340_, uint8_t v_updateToolchain_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2352_; 
lean_inc_ref(v___y_2343_);
lean_inc_ref(v___y_2345_);
v___x_2352_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__0(v___y_2347_, v___y_2345_, v___y_2342_, v___y_2343_, v___y_2346_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2451_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2451_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2451_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_fst_2357_; lean_object* v_snd_2358_; lean_object* v_opts_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_fst_2357_ = lean_ctor_get(v_a_2353_, 0);
lean_inc(v_fst_2357_);
v_snd_2358_ = lean_ctor_get(v_a_2353_, 1);
lean_inc(v_snd_2358_);
lean_dec(v_a_2353_);
v_opts_2359_ = lean_ctor_get(v___y_2343_, 4);
lean_inc(v_opts_2359_);
lean_dec_ref(v___y_2343_);
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc(v_fst_2357_);
v___x_2362_ = l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(v___y_2344_, v_fst_2357_, v_opts_2359_, v_leanOpts_2340_, v_updateToolchain_2341_, v___y_2345_, v___x_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_a_2364_; lean_object* v_snd_2366_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
lean_del_object(v___x_2355_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
v_a_2364_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2362_);
v___x_2394_ = lean_array_get_size(v_a_2364_);
v___x_2395_ = lean_nat_dec_lt(v___x_2360_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_dec(v_a_2364_);
v_snd_2366_ = v_snd_2358_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = lean_box(0);
v___x_2397_ = lean_nat_dec_le(v___x_2394_, v___x_2394_);
if (v___x_2397_ == 0)
{
if (v___x_2395_ == 0)
{
lean_dec(v_a_2364_);
v_snd_2366_ = v_snd_2358_;
goto v___jp_2365_;
}
else
{
size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = ((size_t)0ULL);
v___x_2399_ = lean_usize_of_nat(v___x_2394_);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2364_, v___x_2398_, v___x_2399_, v___x_2396_, v___y_2347_);
lean_dec(v_a_2364_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_dec_ref(v___x_2400_);
v_snd_2366_ = v_snd_2358_;
goto v___jp_2365_;
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec(v_a_2363_);
lean_dec(v_snd_2358_);
lean_dec(v_fst_2357_);
lean_dec_ref(v___y_2347_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
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
size_t v___x_2409_; size_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = ((size_t)0ULL);
v___x_2410_ = lean_usize_of_nat(v___x_2394_);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2364_, v___x_2409_, v___x_2410_, v___x_2396_, v___y_2347_);
lean_dec(v_a_2364_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_dec_ref(v___x_2411_);
v_snd_2366_ = v_snd_2358_;
goto v___jp_2365_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_a_2363_);
lean_dec(v_snd_2358_);
lean_dec(v_fst_2357_);
lean_dec_ref(v___y_2347_);
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
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
}
v___jp_2365_:
{
lean_object* v_fst_2367_; lean_object* v___x_2368_; 
v_fst_2367_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_fst_2367_);
v___x_2368_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0_spec__1(v___y_2347_, v_fst_2367_, v_fst_2357_, v_snd_2366_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2385_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2371_ = v___x_2368_;
v_isShared_2372_ = v_isSharedCheck_2385_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2385_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v_snd_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2383_; 
v_snd_2373_ = lean_ctor_get(v_a_2369_, 1);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_a_2369_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; 
v_unused_2384_ = lean_ctor_get(v_a_2369_, 0);
lean_dec(v_unused_2384_);
v___x_2375_ = v_a_2369_;
v_isShared_2376_ = v_isSharedCheck_2383_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_snd_2373_);
lean_dec(v_a_2369_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2383_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v_a_2363_);
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2363_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_snd_2373_);
v___x_2378_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2380_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2378_);
v___x_2380_ = v___x_2371_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_a_2363_);
v_a_2386_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2368_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2368_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
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
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
lean_dec(v_snd_2358_);
lean_dec(v_fst_2357_);
v_a_2420_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_a_2420_);
lean_dec_ref(v___x_2362_);
v___x_2421_ = lean_array_get_size(v_a_2420_);
v___x_2422_ = lean_nat_dec_lt(v___x_2360_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec(v_a_2420_);
lean_dec_ref(v___y_2347_);
v___x_2423_ = lean_box(0);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 1);
lean_ctor_set(v___x_2355_, 0, v___x_2423_);
v___x_2425_ = v___x_2355_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
else
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
lean_del_object(v___x_2355_);
v___x_2427_ = lean_box(0);
v___x_2428_ = lean_nat_dec_le(v___x_2421_, v___x_2421_);
if (v___x_2428_ == 0)
{
if (v___x_2422_ == 0)
{
lean_dec(v_a_2420_);
lean_dec_ref(v___y_2347_);
goto v___jp_2349_;
}
else
{
size_t v___x_2429_; size_t v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = ((size_t)0ULL);
v___x_2430_ = lean_usize_of_nat(v___x_2421_);
v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2420_, v___x_2429_, v___x_2430_, v___x_2427_, v___y_2347_);
lean_dec_ref(v___y_2347_);
lean_dec(v_a_2420_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_dec_ref(v___x_2431_);
goto v___jp_2349_;
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
else
{
size_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = ((size_t)0ULL);
v___x_2441_ = lean_usize_of_nat(v___x_2421_);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_2420_, v___x_2440_, v___x_2441_, v___x_2427_, v___y_2347_);
lean_dec_ref(v___y_2347_);
lean_dec(v_a_2420_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_dec_ref(v___x_2442_);
goto v___jp_2349_;
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
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
}
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v___y_2347_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec_ref(v_leanOpts_2340_);
v_a_2452_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2352_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2352_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
v___jp_2349_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__1___boxed(lean_object* v_leanOpts_2460_, lean_object* v_updateToolchain_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v_updateToolchain_boxed_2469_; lean_object* v_res_2470_; 
v_updateToolchain_boxed_2469_ = lean_unbox(v_updateToolchain_2461_);
v_res_2470_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__1(v_leanOpts_2460_, v_updateToolchain_boxed_2469_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(lean_object* v_a_2471_, lean_object* v_ws_2472_, lean_object* v_toUpdate_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v___y_2477_; lean_object* v___y_2482_; lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v_val_2508_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v_root_2557_; lean_object* v_baseName_2558_; lean_object* v_dir_2559_; lean_object* v_config_2560_; lean_object* v_relManifestFile_2561_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v_fst_2566_; lean_object* v_snd_2567_; lean_object* v_packagesDir_x3f_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2630_; lean_object* v___y_2631_; uint8_t v___x_2634_; lean_object* v_rootName_2635_; lean_object* v_fst_2637_; lean_object* v_snd_2638_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v_val_2690_; lean_object* v___x_2716_; 
v_root_2557_ = lean_ctor_get(v_ws_2472_, 0);
lean_inc_ref(v_root_2557_);
lean_dec_ref(v_ws_2472_);
v_baseName_2558_ = lean_ctor_get(v_root_2557_, 1);
lean_inc(v_baseName_2558_);
v_dir_2559_ = lean_ctor_get(v_root_2557_, 4);
lean_inc_ref(v_dir_2559_);
v_config_2560_ = lean_ctor_get(v_root_2557_, 6);
lean_inc_ref(v_config_2560_);
v_relManifestFile_2561_ = lean_ctor_get(v_root_2557_, 9);
lean_inc_ref(v_relManifestFile_2561_);
lean_dec_ref(v_root_2557_);
v___x_2634_ = 0;
v_rootName_2635_ = l_Lean_Name_toString(v_baseName_2558_, v___x_2634_);
lean_inc_ref(v_dir_2559_);
v___x_2687_ = l_Lake_joinRelative(v_dir_2559_, v_relManifestFile_2561_);
v___x_2688_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2716_ = l_Lake_Manifest_load(v___x_2687_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set_tag(v___x_2719_, 1);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
v_val_2690_ = v___x_2722_;
goto v___jp_2689_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
v_a_2725_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2716_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2716_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set_tag(v___x_2727_, 0);
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
v_val_2690_ = v___x_2730_;
goto v___jp_2689_;
}
}
}
v___jp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___y_2477_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
v___jp_2481_:
{
if (lean_obj_tag(v_fst_2483_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_snd_2484_);
v_a_2485_ = lean_ctor_get(v_fst_2483_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_fst_2483_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2487_ = v_fst_2483_;
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v_fst_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2499_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2489_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__0));
v___x_2490_ = lean_io_error_to_string(v_a_2485_);
v___x_2491_ = lean_string_append(v___x_2489_, v___x_2490_);
lean_dec_ref(v___x_2490_);
v___x_2492_ = 3;
v___x_2493_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set_uint8(v___x_2493_, sizeof(void*)*1, v___x_2492_);
lean_inc_ref(v___y_2482_);
v___x_2494_ = lean_apply_2(v___y_2482_, v___x_2493_, lean_box(0));
v___x_2495_ = lean_box(0);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 1);
lean_ctor_set(v___x_2487_, 0, v___x_2495_);
v___x_2497_ = v___x_2487_;
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
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec_ref(v_fst_2483_);
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v_snd_2484_);
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
return v___x_2502_;
}
}
v___jp_2503_:
{
lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2509_ = lean_array_get_size(v___y_2505_);
v___x_2510_ = lean_nat_dec_lt(v___y_2507_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_dec_ref(v___y_2505_);
v___y_2482_ = v___y_2504_;
v_fst_2483_ = v_val_2508_;
v_snd_2484_ = v___y_2506_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2511_ = lean_box(0);
v___x_2512_ = lean_nat_dec_le(v___x_2509_, v___x_2509_);
if (v___x_2512_ == 0)
{
if (v___x_2510_ == 0)
{
lean_dec_ref(v___y_2505_);
v___y_2482_ = v___y_2504_;
v_fst_2483_ = v_val_2508_;
v_snd_2484_ = v___y_2506_;
goto v___jp_2481_;
}
else
{
size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = ((size_t)0ULL);
v___x_2514_ = lean_usize_of_nat(v___x_2509_);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2505_, v___x_2513_, v___x_2514_, v___x_2511_, v___y_2504_);
lean_dec_ref(v___y_2505_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref(v___x_2515_);
v___y_2482_ = v___y_2504_;
v_fst_2483_ = v_val_2508_;
v_snd_2484_ = v___y_2506_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref(v_val_2508_);
lean_dec(v___y_2506_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2509_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___y_2505_, v___x_2524_, v___x_2525_, v___x_2511_, v___y_2504_);
lean_dec_ref(v___y_2505_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_dec_ref(v___x_2526_);
v___y_2482_ = v___y_2504_;
v_fst_2483_ = v_val_2508_;
v_snd_2484_ = v___y_2506_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref(v_val_2508_);
lean_dec(v___y_2506_);
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
v___jp_2535_:
{
if (lean_obj_tag(v___y_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_a_2541_ = lean_ctor_get(v___y_2540_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___y_2540_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___y_2540_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___y_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 1);
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
v___y_2504_ = v___y_2536_;
v___y_2505_ = v___y_2537_;
v___y_2506_ = v___y_2538_;
v___y_2507_ = v___y_2539_;
v_val_2508_ = v___x_2546_;
goto v___jp_2503_;
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_a_2549_ = lean_ctor_get(v___y_2540_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___y_2540_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___y_2540_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___y_2540_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set_tag(v___x_2551_, 0);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
v___y_2504_ = v___y_2536_;
v___y_2505_ = v___y_2537_;
v___y_2506_ = v___y_2538_;
v___y_2507_ = v___y_2539_;
v_val_2508_ = v___x_2554_;
goto v___jp_2503_;
}
}
}
}
v___jp_2562_:
{
lean_object* v_toWorkspaceConfig_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_toWorkspaceConfig_2568_ = lean_ctor_get(v_config_2560_, 0);
lean_inc_ref(v_toWorkspaceConfig_2568_);
lean_dec_ref(v_config_2560_);
v___x_2569_ = l_System_FilePath_normalize(v___y_2565_);
v___x_2570_ = l_System_FilePath_normalize(v_toWorkspaceConfig_2568_);
lean_inc_ref(v___x_2570_);
v___x_2571_ = l_System_FilePath_normalize(v___x_2570_);
v___x_2572_ = lean_string_dec_eq(v___x_2569_, v___x_2571_);
lean_dec_ref(v___x_2571_);
lean_dec_ref(v___x_2569_);
if (v___x_2572_ == 0)
{
if (v_fst_2566_ == 0)
{
lean_dec_ref(v___x_2570_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v_dir_2559_);
v___y_2477_ = v_snd_2567_;
goto v___jp_2476_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2573_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__1));
v___x_2574_ = lean_string_append(v___x_2573_, v___y_2564_);
v___x_2575_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__2));
v___x_2576_ = lean_string_append(v___x_2574_, v___x_2575_);
v___x_2577_ = l_Lake_joinRelative(v_dir_2559_, v___x_2570_);
v___x_2578_ = lean_string_append(v___x_2576_, v___x_2577_);
v___x_2579_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2580_ = lean_string_append(v___x_2578_, v___x_2579_);
v___x_2581_ = 1;
v___x_2582_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*1, v___x_2581_);
lean_inc_ref(v___y_2563_);
v___x_2583_ = lean_apply_2(v___y_2563_, v___x_2582_, lean_box(0));
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v___x_2577_);
v___x_2586_ = l_Lake_createParentDirs(v___x_2577_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2587_; 
lean_dec_ref(v___x_2586_);
v___x_2587_ = lean_io_rename(v___y_2564_, v___x_2577_);
lean_dec_ref(v___x_2577_);
lean_dec_ref(v___y_2564_);
v___y_2536_ = v___y_2563_;
v___y_2537_ = v___x_2585_;
v___y_2538_ = v_snd_2567_;
v___y_2539_ = v___x_2584_;
v___y_2540_ = v___x_2587_;
goto v___jp_2535_;
}
else
{
lean_dec_ref(v___x_2577_);
lean_dec_ref(v___y_2564_);
v___y_2536_ = v___y_2563_;
v___y_2537_ = v___x_2585_;
v___y_2538_ = v_snd_2567_;
v___y_2539_ = v___x_2584_;
v___y_2540_ = v___x_2586_;
goto v___jp_2535_;
}
}
}
else
{
lean_dec_ref(v___x_2570_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v_dir_2559_);
v___y_2477_ = v_snd_2567_;
goto v___jp_2476_;
}
}
v___jp_2588_:
{
if (lean_obj_tag(v_packagesDir_x3f_2589_) == 1)
{
lean_object* v_val_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v_val_2592_ = lean_ctor_get(v_packagesDir_x3f_2589_, 0);
lean_inc(v_val_2592_);
lean_dec_ref(v_packagesDir_x3f_2589_);
lean_inc(v_val_2592_);
lean_inc_ref(v_dir_2559_);
v___x_2593_ = l_Lake_joinRelative(v_dir_2559_, v_val_2592_);
v___x_2594_ = l_System_FilePath_pathExists(v___x_2593_);
v___x_2595_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_2596_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2596_ == 0)
{
v___y_2563_ = v___y_2591_;
v___y_2564_ = v___x_2593_;
v___y_2565_ = v_val_2592_;
v_fst_2566_ = v___x_2594_;
v_snd_2567_ = v___y_2590_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2598_ == 0)
{
if (v___x_2596_ == 0)
{
v___y_2563_ = v___y_2591_;
v___y_2564_ = v___x_2593_;
v___y_2565_ = v_val_2592_;
v_fst_2566_ = v___x_2594_;
v_snd_2567_ = v___y_2590_;
goto v___jp_2562_;
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2595_, v___x_2599_, v___x_2600_, v___x_2597_, v___y_2591_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec_ref(v___x_2601_);
v___y_2563_ = v___y_2591_;
v___y_2564_ = v___x_2593_;
v___y_2565_ = v_val_2592_;
v_fst_2566_ = v___x_2594_;
v_snd_2567_ = v___y_2590_;
goto v___jp_2562_;
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref(v___x_2593_);
lean_dec(v_val_2592_);
lean_dec(v___y_2590_);
lean_dec_ref(v_config_2560_);
lean_dec_ref(v_dir_2559_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
else
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2595_, v___x_2610_, v___x_2611_, v___x_2597_, v___y_2591_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_dec_ref(v___x_2612_);
v___y_2563_ = v___y_2591_;
v___y_2564_ = v___x_2593_;
v___y_2565_ = v_val_2592_;
v_fst_2566_ = v___x_2594_;
v_snd_2567_ = v___y_2590_;
goto v___jp_2562_;
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v___x_2593_);
lean_dec(v_val_2592_);
lean_dec(v___y_2590_);
lean_dec_ref(v_config_2560_);
lean_dec_ref(v_dir_2559_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_dec(v_packagesDir_x3f_2589_);
lean_dec_ref(v_config_2560_);
lean_dec_ref(v_dir_2559_);
v___x_2621_ = lean_box(0);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___y_2590_);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
return v___x_2623_;
}
}
v___jp_2624_:
{
lean_object* v_packagesDir_x3f_2628_; 
v_packagesDir_x3f_2628_ = lean_ctor_get(v___y_2625_, 2);
lean_inc(v_packagesDir_x3f_2628_);
lean_dec_ref(v___y_2625_);
v_packagesDir_x3f_2589_ = v_packagesDir_x3f_2628_;
v___y_2590_ = v___y_2626_;
v___y_2591_ = v___y_2627_;
goto v___jp_2588_;
}
v___jp_2629_:
{
if (lean_obj_tag(v___y_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v_snd_2633_; 
v_a_2632_ = lean_ctor_get(v___y_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref(v___y_2631_);
v_snd_2633_ = lean_ctor_get(v_a_2632_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_a_2632_);
v___y_2625_ = v___y_2630_;
v___y_2626_ = v_snd_2633_;
v___y_2627_ = v_a_2471_;
goto v___jp_2624_;
}
else
{
lean_dec_ref(v___y_2630_);
lean_dec_ref(v_config_2560_);
lean_dec_ref(v_dir_2559_);
return v___y_2631_;
}
}
v___jp_2636_:
{
if (lean_obj_tag(v_fst_2637_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v_config_2560_);
lean_dec_ref(v_dir_2559_);
v_a_2639_ = lean_ctor_get(v_fst_2637_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_fst_2637_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2641_ = v_fst_2637_;
v_isShared_2642_ = v_isSharedCheck_2671_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v_fst_2637_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2671_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
if (lean_obj_tag(v_a_2639_) == 11)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
lean_dec_ref(v_a_2639_);
v___x_2643_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__9));
v___x_2644_ = lean_string_append(v_rootName_2635_, v___x_2643_);
v___x_2645_ = 1;
v___x_2646_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2646_, 0, v___x_2644_);
lean_ctor_set_uint8(v___x_2646_, sizeof(void*)*1, v___x_2645_);
lean_inc_ref(v_a_2471_);
v___x_2647_ = lean_apply_2(v_a_2471_, v___x_2646_, lean_box(0));
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v_snd_2638_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2648_);
v___x_2650_ = v___x_2641_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
else
{
if (lean_obj_tag(v_toUpdate_2473_) == 0)
{
lean_object* v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_dec(v_snd_2638_);
lean_dec_ref(v_rootName_2635_);
v___x_2652_ = lean_io_error_to_string(v_a_2639_);
v___x_2653_ = 3;
v___x_2654_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set_uint8(v___x_2654_, sizeof(void*)*1, v___x_2653_);
lean_inc_ref(v_a_2471_);
v___x_2655_ = lean_apply_2(v_a_2471_, v___x_2654_, lean_box(0));
v___x_2656_ = lean_box(0);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 1);
lean_ctor_set(v___x_2641_, 0, v___x_2656_);
v___x_2658_ = v___x_2641_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2660_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__10));
v___x_2661_ = lean_string_append(v_rootName_2635_, v___x_2660_);
v___x_2662_ = lean_io_error_to_string(v_a_2639_);
v___x_2663_ = lean_string_append(v___x_2661_, v___x_2662_);
lean_dec_ref(v___x_2662_);
v___x_2664_ = 2;
v___x_2665_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set_uint8(v___x_2665_, sizeof(void*)*1, v___x_2664_);
lean_inc_ref(v_a_2471_);
v___x_2666_ = lean_apply_2(v_a_2471_, v___x_2665_, lean_box(0));
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
lean_ctor_set(v___x_2667_, 1, v_snd_2638_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2667_);
v___x_2669_ = v___x_2641_;
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
}
}
else
{
lean_dec_ref(v_rootName_2635_);
if (lean_obj_tag(v_toUpdate_2473_) == 0)
{
lean_object* v_a_2672_; lean_object* v_packagesDir_x3f_2673_; lean_object* v_packages_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
v_a_2672_ = lean_ctor_get(v_fst_2637_, 0);
lean_inc(v_a_2672_);
lean_dec_ref(v_fst_2637_);
v_packagesDir_x3f_2673_ = lean_ctor_get(v_a_2672_, 2);
v_packages_2674_ = lean_ctor_get(v_a_2672_, 3);
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = lean_array_get_size(v_packages_2674_);
v___x_2677_ = lean_nat_dec_lt(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_inc(v_packagesDir_x3f_2673_);
lean_dec(v_a_2672_);
v_packagesDir_x3f_2589_ = v_packagesDir_x3f_2673_;
v___y_2590_ = v_snd_2638_;
v___y_2591_ = v_a_2471_;
goto v___jp_2588_;
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
lean_inc(v_packagesDir_x3f_2673_);
lean_dec(v_a_2672_);
v_packagesDir_x3f_2589_ = v_packagesDir_x3f_2673_;
v___y_2590_ = v_snd_2638_;
v___y_2591_ = v_a_2471_;
goto v___jp_2588_;
}
else
{
size_t v___x_2680_; size_t v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = ((size_t)0ULL);
v___x_2681_ = lean_usize_of_nat(v___x_2676_);
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2473_, v_packages_2674_, v___x_2680_, v___x_2681_, v___x_2678_, v_snd_2638_);
v___y_2630_ = v_a_2672_;
v___y_2631_ = v___x_2682_;
goto v___jp_2629_;
}
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = lean_usize_of_nat(v___x_2676_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__1___redArg(v_toUpdate_2473_, v_packages_2674_, v___x_2683_, v___x_2684_, v___x_2678_, v_snd_2638_);
v___y_2630_ = v_a_2672_;
v___y_2631_ = v___x_2685_;
goto v___jp_2629_;
}
}
}
else
{
lean_object* v_a_2686_; 
v_a_2686_ = lean_ctor_get(v_fst_2637_, 0);
lean_inc(v_a_2686_);
lean_dec_ref(v_fst_2637_);
v___y_2625_ = v_a_2686_;
v___y_2626_ = v_snd_2638_;
v___y_2627_ = v_a_2471_;
goto v___jp_2624_;
}
}
}
v___jp_2689_:
{
uint8_t v___x_2691_; 
v___x_2691_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__6);
if (v___x_2691_ == 0)
{
v_fst_2637_ = v_val_2690_;
v_snd_2638_ = v_a_2474_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = lean_box(0);
v___x_2693_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__7);
if (v___x_2693_ == 0)
{
if (v___x_2691_ == 0)
{
v_fst_2637_ = v_val_2690_;
v_snd_2638_ = v_a_2474_;
goto v___jp_2636_;
}
else
{
size_t v___x_2694_; size_t v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = ((size_t)0ULL);
v___x_2695_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2688_, v___x_2694_, v___x_2695_, v___x_2692_, v_a_2471_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_dec_ref(v___x_2696_);
v_fst_2637_ = v_val_2690_;
v_snd_2638_ = v_a_2474_;
goto v___jp_2636_;
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v_val_2690_);
lean_dec_ref(v_rootName_2635_);
lean_dec_ref(v_config_2560_);
lean_dec_ref(v_dir_2559_);
lean_dec(v_a_2474_);
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
else
{
size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = ((size_t)0ULL);
v___x_2706_ = lean_usize_once(&l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8, &l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8_once, _init_l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__8);
v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v___x_2688_, v___x_2705_, v___x_2706_, v___x_2692_, v_a_2471_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_dec_ref(v___x_2707_);
v_fst_2637_ = v_val_2690_;
v_snd_2638_ = v_a_2474_;
goto v___jp_2636_;
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_val_2690_);
lean_dec_ref(v_rootName_2635_);
lean_dec_ref(v_config_2560_);
lean_dec_ref(v_dir_2559_);
lean_dec(v_a_2474_);
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
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
return v___x_2713_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4___boxed(lean_object* v_a_2733_, lean_object* v_ws_2734_, lean_object* v_toUpdate_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_a_2733_, v_ws_2734_, v_toUpdate_2735_, v_a_2736_);
lean_dec(v_toUpdate_2735_);
lean_dec_ref(v_a_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__11(lean_object* v_a_2739_, lean_object* v_ws_2740_, lean_object* v_rootDeps_2741_){
_start:
{
lean_object* v___y_2744_; lean_object* v_root_2749_; lean_object* v_lakeEnv_2750_; lean_object* v_lakeArgs_x3f_2751_; uint8_t v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2900_; lean_object* v___y_2901_; uint8_t v___y_2902_; lean_object* v_baseName_2905_; lean_object* v_dir_2906_; lean_object* v_config_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_root_2749_ = lean_ctor_get(v_ws_2740_, 0);
lean_inc_ref(v_root_2749_);
v_lakeEnv_2750_ = lean_ctor_get(v_ws_2740_, 1);
lean_inc_ref(v_lakeEnv_2750_);
v_lakeArgs_x3f_2751_ = lean_ctor_get(v_ws_2740_, 4);
lean_inc(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_ws_2740_);
v_baseName_2905_ = lean_ctor_get(v_root_2749_, 1);
lean_inc(v_baseName_2905_);
v_dir_2906_ = lean_ctor_get(v_root_2749_, 4);
lean_inc_ref(v_dir_2906_);
v_config_2907_ = lean_ctor_get(v_root_2749_, 6);
lean_inc_ref(v_config_2907_);
lean_dec_ref(v_root_2749_);
v___x_2908_ = l_Lake_toolchainFileName;
lean_inc_ref(v_dir_2906_);
v___x_2909_ = l_System_FilePath_join(v_dir_2906_, v___x_2908_);
v___x_2910_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_2909_);
lean_dec_ref(v___x_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3005_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_3005_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3005_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint8_t v_fixedToolchain_2915_; lean_object* v___x_2916_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; uint8_t v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; uint8_t v___y_2948_; lean_object* v___y_2949_; lean_object* v_src_2953_; lean_object* v_tc_x3f_2954_; lean_object* v_clashes_2955_; uint8_t v_fixed_2956_; lean_object* v___y_2980_; lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; 
v_fixedToolchain_2915_ = lean_ctor_get_uint8(v_config_2907_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_2907_);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2994_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__20));
v___x_2995_ = lean_array_get_size(v_rootDeps_2741_);
v___x_2996_ = lean_nat_dec_lt(v___x_2916_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_inc(v_a_2911_);
v_src_2953_ = v_baseName_2905_;
v_tc_x3f_2954_ = v_a_2911_;
v_clashes_2955_ = v___x_2994_;
v_fixed_2956_ = v_fixedToolchain_2915_;
goto v___jp_2952_;
}
else
{
lean_object* v___x_2997_; uint8_t v___x_2998_; 
lean_inc(v_a_2911_);
lean_inc(v_baseName_2905_);
v___x_2997_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2997_, 0, v_baseName_2905_);
lean_ctor_set(v___x_2997_, 1, v_a_2911_);
lean_ctor_set(v___x_2997_, 2, v___x_2994_);
lean_ctor_set_uint8(v___x_2997_, sizeof(void*)*3, v_fixedToolchain_2915_);
v___x_2998_ = lean_nat_dec_le(v___x_2995_, v___x_2995_);
if (v___x_2998_ == 0)
{
if (v___x_2996_ == 0)
{
lean_dec_ref(v___x_2997_);
lean_inc(v_a_2911_);
v_src_2953_ = v_baseName_2905_;
v_tc_x3f_2954_ = v_a_2911_;
v_clashes_2955_ = v___x_2994_;
v_fixed_2956_ = v_fixedToolchain_2915_;
goto v___jp_2952_;
}
else
{
size_t v___x_2999_; size_t v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v_baseName_2905_);
v___x_2999_ = ((size_t)0ULL);
v___x_3000_ = lean_usize_of_nat(v___x_2995_);
lean_inc_ref(v_dir_2906_);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2906_, v_rootDeps_2741_, v___x_2999_, v___x_3000_, v___x_2997_, v_a_2739_);
v___y_2980_ = v___x_3001_;
goto v___jp_2979_;
}
}
else
{
size_t v___x_3002_; size_t v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v_baseName_2905_);
v___x_3002_ = ((size_t)0ULL);
v___x_3003_ = lean_usize_of_nat(v___x_2995_);
lean_inc_ref(v_dir_2906_);
v___x_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__1(v_dir_2906_, v_rootDeps_2741_, v___x_3002_, v___x_3003_, v___x_2997_, v_a_2739_);
v___y_2980_ = v___x_3004_;
goto v___jp_2979_;
}
}
v___jp_2917_:
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_nat_dec_lt(v___x_2916_, v___y_2918_);
if (v___x_2921_ == 0)
{
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
v___y_2744_ = v___y_2920_;
goto v___jp_2743_;
}
else
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_nat_dec_le(v___y_2918_, v___y_2918_);
if (v___x_2922_ == 0)
{
if (v___x_2921_ == 0)
{
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
v___y_2744_ = v___y_2920_;
goto v___jp_2743_;
}
else
{
size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((size_t)0ULL);
v___x_2924_ = lean_usize_of_nat(v___y_2918_);
lean_dec(v___y_2918_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2919_, v___x_2923_, v___x_2924_, v___y_2920_);
lean_dec_ref(v___y_2919_);
v___y_2744_ = v___x_2925_;
goto v___jp_2743_;
}
}
else
{
size_t v___x_2926_; size_t v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = ((size_t)0ULL);
v___x_2927_ = lean_usize_of_nat(v___y_2918_);
lean_dec(v___y_2918_);
v___x_2928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0(v___y_2919_, v___x_2926_, v___x_2927_, v___y_2920_);
lean_dec_ref(v___y_2919_);
v___y_2744_ = v___x_2928_;
goto v___jp_2743_;
}
}
}
v___jp_2929_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2937_ = lean_string_append(v___y_2931_, v___y_2936_);
lean_dec_ref(v___y_2936_);
v___x_2938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__0));
v___x_2939_ = lean_string_append(v___x_2937_, v___x_2938_);
v___x_2940_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_2933_, v___y_2935_);
v___x_2941_ = lean_string_append(v___x_2939_, v___x_2940_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = lean_string_append(v___x_2941_, v___y_2932_);
lean_dec_ref(v___y_2932_);
v___y_2918_ = v___y_2930_;
v___y_2919_ = v___y_2934_;
v___y_2920_ = v___x_2942_;
goto v___jp_2917_;
}
v___jp_2943_:
{
lean_object* v___x_2950_; lean_object* v_toString_2951_; 
v___x_2950_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__14));
v_toString_2951_ = lean_ctor_get(v___y_2945_, 0);
lean_inc_ref(v_toString_2951_);
lean_dec_ref(v___y_2945_);
v___y_2930_ = v___y_2944_;
v___y_2931_ = v___x_2950_;
v___y_2932_ = v___y_2949_;
v___y_2933_ = v___y_2946_;
v___y_2934_ = v___y_2947_;
v___y_2935_ = v___y_2948_;
v___y_2936_ = v_toString_2951_;
goto v___jp_2929_;
}
v___jp_2952_:
{
lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2957_ = lean_array_get_size(v_clashes_2955_);
v___x_2958_ = lean_nat_dec_lt(v___x_2916_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_dec_ref(v_clashes_2955_);
lean_dec(v_src_2953_);
if (lean_obj_tag(v_tc_x3f_2954_) == 1)
{
lean_object* v_val_2959_; lean_object* v_rootToolchainFile_2960_; 
v_val_2959_ = lean_ctor_get(v_tc_x3f_2954_, 0);
lean_inc(v_val_2959_);
lean_dec_ref(v_tc_x3f_2954_);
v_rootToolchainFile_2960_ = l_Lake_joinRelative(v_dir_2906_, v___x_2908_);
if (lean_obj_tag(v_a_2911_) == 0)
{
lean_del_object(v___x_2913_);
v___y_2900_ = v_rootToolchainFile_2960_;
v___y_2901_ = v_val_2959_;
v___y_2902_ = v___x_2958_;
goto v___jp_2899_;
}
else
{
lean_object* v_val_2961_; uint8_t v___x_2962_; 
v_val_2961_ = lean_ctor_get(v_a_2911_, 0);
lean_inc(v_val_2961_);
lean_dec_ref(v_a_2911_);
lean_inc(v_val_2959_);
v___x_2962_ = l_Lake_instDecidableEqToolchainVer_decEq(v_val_2961_, v_val_2959_);
if (v___x_2962_ == 0)
{
lean_del_object(v___x_2913_);
v___y_2900_ = v_rootToolchainFile_2960_;
v___y_2901_ = v_val_2959_;
v___y_2902_ = v___x_2962_;
goto v___jp_2899_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
lean_dec_ref(v_rootToolchainFile_2960_);
lean_dec(v_val_2959_);
lean_dec(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_lakeEnv_2750_);
v___x_2963_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__16));
lean_inc_ref(v_a_2739_);
v___x_2964_ = lean_apply_2(v_a_2739_, v___x_2963_, lean_box(0));
v___x_2965_ = lean_box(0);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2965_);
v___x_2967_ = v___x_2913_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
lean_dec(v_tc_x3f_2954_);
lean_dec(v_a_2911_);
lean_dec_ref(v_dir_2906_);
lean_dec(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_lakeEnv_2750_);
v___x_2969_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__18));
lean_inc_ref(v_a_2739_);
v___x_2970_ = lean_apply_2(v_a_2739_, v___x_2969_, lean_box(0));
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2970_);
v___x_2972_ = v___x_2913_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
lean_del_object(v___x_2913_);
lean_dec(v_a_2911_);
lean_dec_ref(v_dir_2906_);
lean_dec(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_lakeEnv_2750_);
if (lean_obj_tag(v_tc_x3f_2954_) == 1)
{
if (v_fixed_2956_ == 0)
{
lean_object* v_val_2974_; lean_object* v___x_2975_; 
v_val_2974_ = lean_ctor_get(v_tc_x3f_2954_, 0);
lean_inc(v_val_2974_);
lean_dec_ref(v_tc_x3f_2954_);
v___x_2975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__2));
v___y_2944_ = v___x_2957_;
v___y_2945_ = v_val_2974_;
v___y_2946_ = v_src_2953_;
v___y_2947_ = v_clashes_2955_;
v___y_2948_ = v___x_2958_;
v___y_2949_ = v___x_2975_;
goto v___jp_2943_;
}
else
{
lean_object* v_val_2976_; lean_object* v___x_2977_; 
v_val_2976_ = lean_ctor_get(v_tc_x3f_2954_, 0);
lean_inc(v_val_2976_);
lean_dec_ref(v_tc_x3f_2954_);
v___x_2977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain_spec__0_spec__0___closed__3));
v___y_2944_ = v___x_2957_;
v___y_2945_ = v_val_2976_;
v___y_2946_ = v_src_2953_;
v___y_2947_ = v_clashes_2955_;
v___y_2948_ = v___x_2958_;
v___y_2949_ = v___x_2977_;
goto v___jp_2943_;
}
}
else
{
lean_object* v___x_2978_; 
lean_dec(v_tc_x3f_2954_);
lean_dec(v_src_2953_);
v___x_2978_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__19));
v___y_2918_ = v___x_2957_;
v___y_2919_ = v_clashes_2955_;
v___y_2920_ = v___x_2978_;
goto v___jp_2917_;
}
}
}
v___jp_2979_:
{
if (lean_obj_tag(v___y_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_src_2982_; lean_object* v_tc_x3f_2983_; lean_object* v_clashes_2984_; uint8_t v_fixed_2985_; 
v_a_2981_ = lean_ctor_get(v___y_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___y_2980_);
v_src_2982_ = lean_ctor_get(v_a_2981_, 0);
lean_inc(v_src_2982_);
v_tc_x3f_2983_ = lean_ctor_get(v_a_2981_, 1);
lean_inc(v_tc_x3f_2983_);
v_clashes_2984_ = lean_ctor_get(v_a_2981_, 2);
lean_inc_ref(v_clashes_2984_);
v_fixed_2985_ = lean_ctor_get_uint8(v_a_2981_, sizeof(void*)*3);
lean_dec(v_a_2981_);
v_src_2953_ = v_src_2982_;
v_tc_x3f_2954_ = v_tc_x3f_2983_;
v_clashes_2955_ = v_clashes_2984_;
v_fixed_2956_ = v_fixed_2985_;
goto v___jp_2952_;
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_del_object(v___x_2913_);
lean_dec(v_a_2911_);
lean_dec_ref(v_dir_2906_);
lean_dec(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_lakeEnv_2750_);
v_a_2986_ = lean_ctor_get(v___y_2980_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___y_2980_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___y_2980_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___y_2980_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3018_; 
lean_dec_ref(v_config_2907_);
lean_dec_ref(v_dir_2906_);
lean_dec(v_baseName_2905_);
lean_dec(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_lakeEnv_2750_);
v_a_3006_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3008_ = v___x_2910_;
v_isShared_3009_ = v_isSharedCheck_3018_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2910_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3018_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3010_ = lean_io_error_to_string(v_a_3006_);
v___x_3011_ = 3;
v___x_3012_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*1, v___x_3011_);
lean_inc_ref(v_a_2739_);
v___x_3013_ = lean_apply_2(v_a_2739_, v___x_3012_, lean_box(0));
v___x_3014_ = lean_box(0);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 0, v___x_3014_);
v___x_3016_ = v___x_3008_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
v___jp_2743_:
{
uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2745_ = 2;
v___x_2746_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2746_, 0, v___y_2744_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*1, v___x_2745_);
lean_inc_ref(v_a_2739_);
v___x_2747_ = lean_apply_2(v_a_2739_, v___x_2746_, lean_box(0));
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
v___jp_2752_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2757_ = lean_string_append(v___y_2755_, v___y_2756_);
v___x_2758_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__3));
v___x_2759_ = lean_string_append(v___x_2757_, v___x_2758_);
v___x_2760_ = 1;
v___x_2761_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*1, v___x_2760_);
lean_inc_ref(v_a_2739_);
v___x_2762_ = lean_apply_2(v_a_2739_, v___x_2761_, lean_box(0));
v___x_2763_ = l_IO_FS_writeFile(v___y_2754_, v___y_2756_);
lean_dec_ref(v___y_2754_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_dec_ref(v___x_2763_);
if (lean_obj_tag(v_lakeArgs_x3f_2751_) == 1)
{
lean_object* v_elan_x3f_2764_; 
v_elan_x3f_2764_ = lean_ctor_get(v_lakeEnv_2750_, 2);
if (lean_obj_tag(v_elan_x3f_2764_) == 1)
{
lean_object* v_val_2765_; lean_object* v_val_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v_elan_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v_val_2765_ = lean_ctor_get(v_lakeArgs_x3f_2751_, 0);
lean_inc(v_val_2765_);
lean_dec_ref(v_lakeArgs_x3f_2751_);
v_val_2766_ = lean_ctor_get(v_elan_x3f_2764_, 0);
v___x_2767_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__1));
lean_inc_ref(v_a_2739_);
v___x_2768_ = lean_apply_2(v_a_2739_, v___x_2767_, lean_box(0));
v___x_2769_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__2));
v_elan_2770_ = lean_ctor_get(v_val_2766_, 1);
lean_inc_ref(v_elan_2770_);
v___x_2771_ = 1;
v___x_2772_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__5));
v___x_2773_ = lean_unsigned_to_nat(4u);
v___x_2774_ = lean_mk_empty_array_with_capacity(v___x_2773_);
lean_dec_ref(v___x_2774_);
v___x_2775_ = lean_obj_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__7);
v___x_2776_ = lean_array_push(v___x_2775_, v___y_2756_);
v___x_2777_ = lean_array_push(v___x_2776_, v___x_2772_);
v___x_2778_ = l_Array_append___redArg(v___x_2777_, v_val_2765_);
lean_dec(v_val_2765_);
v___x_2779_ = lean_box(0);
v___x_2780_ = l_Lake_Env_noToolchainVars(v_lakeEnv_2750_);
v___x_2781_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2781_, 0, v___x_2769_);
lean_ctor_set(v___x_2781_, 1, v_elan_2770_);
lean_ctor_set(v___x_2781_, 2, v___x_2778_);
lean_ctor_set(v___x_2781_, 3, v___x_2779_);
lean_ctor_set(v___x_2781_, 4, v___x_2780_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*5, v___x_2771_);
lean_ctor_set_uint8(v___x_2781_, sizeof(void*)*5 + 1, v___y_2753_);
v___x_2782_ = lean_io_process_spawn(v___x_2781_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = lean_io_process_child_wait(v___x_2769_, v_a_2783_);
lean_dec(v_a_2783_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; uint32_t v___x_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
v___x_2786_ = lean_unbox_uint32(v_a_2785_);
lean_dec(v_a_2785_);
v___x_2787_ = lean_uint32_to_uint8(v___x_2786_);
v___x_2788_ = lean_io_exit(v___x_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2809_; 
v_a_2797_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2799_ = v___x_2788_;
v_isShared_2800_ = v_isSharedCheck_2809_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2788_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2809_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2801_ = lean_io_error_to_string(v_a_2797_);
v___x_2802_ = 3;
v___x_2803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set_uint8(v___x_2803_, sizeof(void*)*1, v___x_2802_);
lean_inc_ref(v_a_2739_);
v___x_2804_ = lean_apply_2(v_a_2739_, v___x_2803_, lean_box(0));
v___x_2805_ = lean_box(0);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2805_);
v___x_2807_ = v___x_2799_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2822_; 
v_a_2810_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2812_ = v___x_2784_;
v_isShared_2813_ = v_isSharedCheck_2822_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2784_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2822_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2814_ = lean_io_error_to_string(v_a_2810_);
v___x_2815_ = 3;
v___x_2816_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set_uint8(v___x_2816_, sizeof(void*)*1, v___x_2815_);
lean_inc_ref(v_a_2739_);
v___x_2817_ = lean_apply_2(v_a_2739_, v___x_2816_, lean_box(0));
v___x_2818_ = lean_box(0);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2818_);
v___x_2820_ = v___x_2812_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2835_; 
v_a_2823_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2825_ = v___x_2782_;
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2782_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2827_ = lean_io_error_to_string(v_a_2823_);
v___x_2828_ = 3;
v___x_2829_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*1, v___x_2828_);
lean_inc_ref(v_a_2739_);
v___x_2830_ = lean_apply_2(v_a_2739_, v___x_2829_, lean_box(0));
v___x_2831_ = lean_box(0);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2831_);
v___x_2833_ = v___x_2825_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; 
lean_dec_ref(v_lakeArgs_x3f_2751_);
lean_dec_ref(v___y_2756_);
lean_dec_ref(v_lakeEnv_2750_);
v___x_2836_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__9));
lean_inc_ref(v_a_2739_);
v___x_2837_ = lean_apply_2(v_a_2739_, v___x_2836_, lean_box(0));
v___x_2838_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2839_ = lean_io_exit(v___x_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2860_; 
v_a_2848_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2850_ = v___x_2839_;
v_isShared_2851_ = v_isSharedCheck_2860_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2839_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2860_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
v___x_2852_ = lean_io_error_to_string(v_a_2848_);
v___x_2853_ = 3;
v___x_2854_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*1, v___x_2853_);
lean_inc_ref(v_a_2739_);
v___x_2855_ = lean_apply_2(v_a_2739_, v___x_2854_, lean_box(0));
v___x_2856_ = lean_box(0);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2856_);
v___x_2858_ = v___x_2850_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
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
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v___y_2756_);
lean_dec(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_lakeEnv_2750_);
v___x_2861_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__12));
lean_inc_ref(v_a_2739_);
v___x_2862_ = lean_apply_2(v_a_2739_, v___x_2861_, lean_box(0));
v___x_2863_ = lean_uint8_once(&l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10, &l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10_once, _init_l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__10);
v___x_2864_ = lean_io_exit(v___x_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2885_; 
v_a_2873_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2875_ = v___x_2864_;
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2864_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2877_ = lean_io_error_to_string(v_a_2873_);
v___x_2878_ = 3;
v___x_2879_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*1, v___x_2878_);
lean_inc_ref(v_a_2739_);
v___x_2880_ = lean_apply_2(v_a_2739_, v___x_2879_, lean_box(0));
v___x_2881_ = lean_box(0);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2881_);
v___x_2883_ = v___x_2875_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2898_; 
lean_dec_ref(v___y_2756_);
lean_dec(v_lakeArgs_x3f_2751_);
lean_dec_ref(v_lakeEnv_2750_);
v_a_2886_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2888_ = v___x_2763_;
v_isShared_2889_ = v_isSharedCheck_2898_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2763_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2898_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; uint8_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2890_ = lean_io_error_to_string(v_a_2886_);
v___x_2891_ = 3;
v___x_2892_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set_uint8(v___x_2892_, sizeof(void*)*1, v___x_2891_);
lean_inc_ref(v_a_2739_);
v___x_2893_ = lean_apply_2(v_a_2739_, v___x_2892_, lean_box(0));
v___x_2894_ = lean_box(0);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2894_);
v___x_2896_ = v___x_2888_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
v___jp_2899_:
{
lean_object* v___x_2903_; lean_object* v_toString_2904_; 
v___x_2903_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___closed__13));
v_toString_2904_ = lean_ctor_get(v___y_2901_, 0);
lean_inc_ref(v_toString_2904_);
lean_dec_ref(v___y_2901_);
v___y_2753_ = v___y_2902_;
v___y_2754_ = v___y_2900_;
v___y_2755_ = v___x_2903_;
v___y_2756_ = v_toString_2904_;
goto v___jp_2752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__11___boxed(lean_object* v_a_3019_, lean_object* v_ws_3020_, lean_object* v_rootDeps_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__11(v_a_3019_, v_ws_3020_, v_rootDeps_3021_);
lean_dec_ref(v_rootDeps_3021_);
lean_dec_ref(v_a_3019_);
return v_res_3023_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11(lean_object* v_a_3024_, lean_object* v_x_3025_){
_start:
{
if (lean_obj_tag(v_x_3025_) == 0)
{
uint8_t v___x_3026_; 
v___x_3026_ = 0;
return v___x_3026_;
}
else
{
lean_object* v_head_3027_; lean_object* v_tail_3028_; uint8_t v___x_3029_; 
v_head_3027_ = lean_ctor_get(v_x_3025_, 0);
v_tail_3028_ = lean_ctor_get(v_x_3025_, 1);
v___x_3029_ = lean_name_eq(v_a_3024_, v_head_3027_);
if (v___x_3029_ == 0)
{
v_x_3025_ = v_tail_3028_;
goto _start;
}
else
{
return v___x_3029_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11___boxed(lean_object* v_a_3031_, lean_object* v_x_3032_){
_start:
{
uint8_t v_res_3033_; lean_object* v_r_3034_; 
v_res_3033_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11(v_a_3031_, v_x_3032_);
lean_dec(v_x_3032_);
lean_dec(v_a_3031_);
v_r_3034_ = lean_box(v_res_3033_);
return v_r_3034_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22_spec__28(lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
if (lean_obj_tag(v_a_3036_) == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = l_List_reverse___redArg(v_a_3037_);
return v___x_3038_;
}
else
{
lean_object* v_head_3039_; lean_object* v_tail_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3052_; 
v_head_3039_ = lean_ctor_get(v_a_3036_, 0);
v_tail_3040_ = lean_ctor_get(v_a_3036_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3042_ = v_a_3036_;
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_tail_3040_);
lean_inc(v_head_3039_);
lean_dec(v_a_3036_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3052_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3044_; uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3044_ = ((lean_object*)(l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22_spec__28___closed__0));
v___x_3045_ = 1;
v___x_3046_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_3039_, v___x_3045_);
v___x_3047_ = lean_string_append(v___x_3044_, v___x_3046_);
lean_dec_ref(v___x_3046_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v_a_3037_);
lean_ctor_set(v___x_3042_, 0, v___x_3047_);
v___x_3049_ = v___x_3042_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_a_3037_);
v___x_3049_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
v_a_3036_ = v_tail_3040_;
v_a_3037_ = v___x_3049_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22(lean_object* v_cycle_3054_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3055_ = ((lean_object*)(l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22___closed__0));
v___x_3056_ = lean_box(0);
v___x_3057_ = l_List_mapTR_loop___at___00Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22_spec__28(v_cycle_3054_, v___x_3056_);
v___x_3058_ = l_String_intercalate(v___x_3055_, v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg(lean_object* v_cycle_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3062_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1));
v___x_3063_ = l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22(v_cycle_3059_);
v___x_3064_ = lean_string_append(v___x_3062_, v___x_3063_);
lean_dec_ref(v___x_3063_);
v___x_3065_ = 3;
v___x_3066_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set_uint8(v___x_3066_, sizeof(void*)*1, v___x_3065_);
lean_inc_ref(v___y_3060_);
v___x_3067_ = lean_apply_2(v___y_3060_, v___x_3066_, lean_box(0));
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg___boxed(lean_object* v_cycle_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg(v_cycle_3070_, v___y_3071_);
lean_dec_ref(v___y_3071_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13(lean_object* v___x_3074_, uint8_t v___x_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
if (lean_obj_tag(v_a_3076_) == 0)
{
lean_object* v_fst_3078_; lean_object* v_snd_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3088_; 
v_fst_3078_ = lean_ctor_get(v_a_3077_, 0);
v_snd_3079_ = lean_ctor_get(v_a_3077_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_a_3077_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3081_ = v_a_3077_;
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_snd_3079_);
lean_inc(v_fst_3078_);
lean_dec(v_a_3077_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3083_ = l_List_reverse___redArg(v_fst_3078_);
v___x_3084_ = l_List_reverse___redArg(v_snd_3079_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 1, v___x_3084_);
lean_ctor_set(v___x_3081_, 0, v___x_3083_);
v___x_3086_ = v___x_3081_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
else
{
lean_object* v_head_3089_; lean_object* v_tail_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3112_; 
v_head_3089_ = lean_ctor_get(v_a_3076_, 0);
v_tail_3090_ = lean_ctor_get(v_a_3076_, 1);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_a_3076_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3092_ = v_a_3076_;
v_isShared_3093_ = v_isSharedCheck_3112_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_tail_3090_);
lean_inc(v_head_3089_);
lean_dec(v_a_3076_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3112_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v_fst_3094_; lean_object* v_snd_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3111_; 
v_fst_3094_ = lean_ctor_get(v_a_3077_, 0);
v_snd_3095_ = lean_ctor_get(v_a_3077_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_a_3077_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3097_ = v_a_3077_;
v_isShared_3098_ = v_isSharedCheck_3111_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_snd_3095_);
lean_inc(v_fst_3094_);
lean_dec(v_a_3077_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3111_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_name_eq(v_head_3089_, v___x_3074_);
if (v___x_3107_ == 0)
{
if (v___x_3075_ == 0)
{
goto v___jp_3099_;
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_del_object(v___x_3097_);
lean_del_object(v___x_3092_);
v___x_3108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_head_3089_);
lean_ctor_set(v___x_3108_, 1, v_fst_3094_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v_snd_3095_);
v_a_3076_ = v_tail_3090_;
v_a_3077_ = v___x_3109_;
goto _start;
}
}
else
{
goto v___jp_3099_;
}
v___jp_3099_:
{
lean_object* v___x_3101_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 1, v_snd_3095_);
v___x_3101_ = v___x_3092_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_head_3089_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_snd_3095_);
v___x_3101_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3103_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3101_);
v___x_3103_ = v___x_3097_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_fst_3094_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
v_a_3076_ = v_tail_3090_;
v_a_3077_ = v___x_3103_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13___boxed(lean_object* v___x_3113_, lean_object* v___x_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
uint8_t v___x_73701__boxed_3117_; lean_object* v_res_3118_; 
v___x_73701__boxed_3117_ = lean_unbox(v___x_3114_);
v_res_3118_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13(v___x_3113_, v___x_73701__boxed_3117_, v_a_3115_, v_a_3116_);
lean_dec(v___x_3113_);
return v_res_3118_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5(lean_object* v_a_3119_, lean_object* v_as_3120_, size_t v_i_3121_, size_t v_stop_3122_){
_start:
{
uint8_t v___x_3123_; 
v___x_3123_ = lean_usize_dec_eq(v_i_3121_, v_stop_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v_baseName_3125_; lean_object* v_name_3126_; uint8_t v___x_3127_; 
v___x_3124_ = lean_array_uget_borrowed(v_as_3120_, v_i_3121_);
v_baseName_3125_ = lean_ctor_get(v___x_3124_, 1);
v_name_3126_ = lean_ctor_get(v_a_3119_, 0);
v___x_3127_ = lean_name_eq(v_baseName_3125_, v_name_3126_);
if (v___x_3127_ == 0)
{
size_t v___x_3128_; size_t v___x_3129_; 
v___x_3128_ = ((size_t)1ULL);
v___x_3129_ = lean_usize_add(v_i_3121_, v___x_3128_);
v_i_3121_ = v___x_3129_;
goto _start;
}
else
{
return v___x_3127_;
}
}
else
{
uint8_t v___x_3131_; 
v___x_3131_ = 0;
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5___boxed(lean_object* v_a_3132_, lean_object* v_as_3133_, lean_object* v_i_3134_, lean_object* v_stop_3135_){
_start:
{
size_t v_i_boxed_3136_; size_t v_stop_boxed_3137_; uint8_t v_res_3138_; lean_object* v_r_3139_; 
v_i_boxed_3136_ = lean_unbox_usize(v_i_3134_);
lean_dec(v_i_3134_);
v_stop_boxed_3137_ = lean_unbox_usize(v_stop_3135_);
lean_dec(v_stop_3135_);
v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5(v_a_3132_, v_as_3133_, v_i_boxed_3136_, v_stop_boxed_3137_);
lean_dec_ref(v_as_3133_);
lean_dec_ref(v_a_3132_);
v_r_3139_ = lean_box(v_res_3138_);
return v_r_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(lean_object* v_pkg_3140_, lean_object* v_leanOpts_3141_, uint8_t v_updateToolchain_3142_, lean_object* v_as_3143_, size_t v_i_3144_, size_t v_stop_3145_, lean_object* v_b_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_usize_dec_eq(v_i_3144_, v_stop_3145_);
if (v___x_3151_ == 0)
{
lean_object* v_packages_3152_; size_t v___x_3153_; size_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___y_3159_; uint8_t v___x_3188_; 
v_packages_3152_ = lean_ctor_get(v___y_3147_, 5);
v___x_3153_ = ((size_t)1ULL);
v___x_3154_ = lean_usize_sub(v_i_3144_, v___x_3153_);
v___x_3155_ = lean_array_uget_borrowed(v_as_3143_, v___x_3154_);
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = lean_array_get_size(v_packages_3152_);
v___x_3188_ = lean_nat_dec_lt(v___x_3156_, v___x_3157_);
if (v___x_3188_ == 0)
{
v___y_3159_ = v___x_3151_;
goto v___jp_3158_;
}
else
{
if (v___x_3188_ == 0)
{
v___y_3159_ = v___x_3151_;
goto v___jp_3158_;
}
else
{
size_t v___x_3189_; size_t v___x_3190_; uint8_t v___x_3191_; 
v___x_3189_ = ((size_t)0ULL);
v___x_3190_ = lean_usize_of_nat(v___x_3157_);
v___x_3191_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5(v___x_3155_, v_packages_3152_, v___x_3189_, v___x_3190_);
if (v___x_3191_ == 0)
{
v___y_3159_ = v___x_3191_;
goto v___jp_3158_;
}
else
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_box(0);
v_i_3144_ = v___x_3154_;
v_b_3146_ = v___x_3192_;
goto _start;
}
}
}
v___jp_3158_:
{
lean_object* v_baseName_3160_; lean_object* v_name_3161_; uint8_t v___x_3162_; 
v_baseName_3160_ = lean_ctor_get(v_pkg_3140_, 1);
v_name_3161_ = lean_ctor_get(v___x_3155_, 0);
v___x_3162_ = lean_name_eq(v_baseName_3160_, v_name_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; 
lean_inc_ref(v___y_3149_);
lean_inc(v___x_3155_);
lean_inc_ref(v_pkg_3140_);
lean_inc_ref(v_leanOpts_3141_);
v___x_3163_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__1(v_leanOpts_3141_, v_updateToolchain_3142_, v_pkg_3140_, v___x_3155_, v___x_3157_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v_fst_3165_; lean_object* v_snd_3166_; lean_object* v_fst_3167_; lean_object* v_snd_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref(v___x_3163_);
v_fst_3165_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_fst_3165_);
v_snd_3166_ = lean_ctor_get(v_a_3164_, 1);
lean_inc(v_snd_3166_);
lean_dec(v_a_3164_);
v_fst_3167_ = lean_ctor_get(v_fst_3165_, 0);
lean_inc(v_fst_3167_);
v_snd_3168_ = lean_ctor_get(v_fst_3165_, 1);
lean_inc(v_snd_3168_);
lean_dec(v_fst_3165_);
v___x_3169_ = lean_box(0);
v___x_3170_ = l_Lake_Workspace_addPackage(v_fst_3167_, v_snd_3168_);
v_i_3144_ = v___x_3154_;
v_b_3146_ = v___x_3169_;
v___y_3147_ = v___x_3170_;
v___y_3148_ = v_snd_3166_;
goto _start;
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v_leanOpts_3141_);
lean_dec_ref(v_pkg_3140_);
v_a_3172_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3163_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3163_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc(v_baseName_3160_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec_ref(v_leanOpts_3141_);
lean_dec_ref(v_pkg_3140_);
v___x_3180_ = l_Lean_Name_toString(v_baseName_3160_, v___y_3159_);
v___x_3181_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__0));
v___x_3182_ = lean_string_append(v___x_3180_, v___x_3181_);
v___x_3183_ = 3;
v___x_3184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3184_, 0, v___x_3182_);
lean_ctor_set_uint8(v___x_3184_, sizeof(void*)*1, v___x_3183_);
lean_inc_ref(v___y_3149_);
v___x_3185_ = lean_apply_2(v___y_3149_, v___x_3184_, lean_box(0));
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
lean_dec_ref(v_leanOpts_3141_);
lean_dec_ref(v_pkg_3140_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v_b_3146_);
lean_ctor_set(v___x_3194_, 1, v___y_3147_);
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v___y_3148_);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg___boxed(lean_object* v_pkg_3197_, lean_object* v_leanOpts_3198_, lean_object* v_updateToolchain_3199_, lean_object* v_as_3200_, lean_object* v_i_3201_, lean_object* v_stop_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v_updateToolchain_boxed_3208_; size_t v_i_boxed_3209_; size_t v_stop_boxed_3210_; lean_object* v_res_3211_; 
v_updateToolchain_boxed_3208_ = lean_unbox(v_updateToolchain_3199_);
v_i_boxed_3209_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_stop_boxed_3210_ = lean_unbox_usize(v_stop_3202_);
lean_dec(v_stop_3202_);
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_3197_, v_leanOpts_3198_, v_updateToolchain_boxed_3208_, v_as_3200_, v_i_boxed_3209_, v_stop_boxed_3210_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v_as_3200_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(lean_object* v_leanOpts_3214_, uint8_t v_updateToolchain_3215_, lean_object* v___x_3216_, lean_object* v_as_3217_, size_t v_i_3218_, size_t v_stop_3219_, lean_object* v_b_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_usize_dec_eq(v_i_3218_, v_stop_3219_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_array_uget_borrowed(v_as_3217_, v_i_3218_);
lean_inc(v___x_3226_);
lean_inc_ref(v_leanOpts_3214_);
v___x_3227_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg(v_leanOpts_3214_, v_updateToolchain_3215_, v___x_3226_, v___x_3216_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v_fst_3229_; lean_object* v_snd_3230_; lean_object* v_fst_3231_; lean_object* v_snd_3232_; size_t v___x_3233_; size_t v___x_3234_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref(v___x_3227_);
v_fst_3229_ = lean_ctor_get(v_a_3228_, 0);
lean_inc(v_fst_3229_);
v_snd_3230_ = lean_ctor_get(v_a_3228_, 1);
lean_inc(v_snd_3230_);
lean_dec(v_a_3228_);
v_fst_3231_ = lean_ctor_get(v_fst_3229_, 0);
lean_inc(v_fst_3231_);
v_snd_3232_ = lean_ctor_get(v_fst_3229_, 1);
lean_inc(v_snd_3232_);
lean_dec(v_fst_3229_);
v___x_3233_ = ((size_t)1ULL);
v___x_3234_ = lean_usize_add(v_i_3218_, v___x_3233_);
v_i_3218_ = v___x_3234_;
v_b_3220_ = v_fst_3231_;
v___y_3221_ = v_snd_3232_;
v___y_3222_ = v_snd_3230_;
goto _start;
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v_leanOpts_3214_);
v_a_3236_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3227_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3227_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_dec_ref(v_leanOpts_3214_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_b_3220_);
lean_ctor_set(v___x_3244_, 1, v___y_3221_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v___y_3222_);
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
return v___x_3246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35(lean_object* v_leanOpts_3247_, uint8_t v_updateToolchain_3248_, lean_object* v___x_3249_, lean_object* v_leanOpts_3250_, uint8_t v_updateToolchain_3251_, lean_object* v_pkg_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_packages_3258_; lean_object* v_depConfigs_3259_; lean_object* v___x_3260_; lean_object* v_snd_3262_; lean_object* v_packages_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v_____x_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v_packages_3258_ = lean_ctor_get(v_a_3254_, 5);
v_depConfigs_3259_ = lean_ctor_get(v_pkg_3252_, 12);
lean_inc_ref(v_depConfigs_3259_);
v___x_3260_ = lean_array_get_size(v_packages_3258_);
v___x_3288_ = lean_array_get_size(v_depConfigs_3259_);
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = lean_box(0);
v___x_3291_ = lean_nat_dec_le(v___x_3288_, v___x_3288_);
if (v___x_3291_ == 0)
{
uint8_t v___x_3292_; 
v___x_3292_ = lean_nat_dec_lt(v___x_3289_, v___x_3288_);
if (v___x_3292_ == 0)
{
uint8_t v___x_3293_; 
lean_dec_ref(v_depConfigs_3259_);
lean_dec_ref(v_pkg_3252_);
lean_dec_ref(v_leanOpts_3250_);
v___x_3293_ = lean_nat_dec_lt(v___x_3260_, v___x_3260_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
lean_dec_ref(v_leanOpts_3247_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3290_);
lean_ctor_set(v___x_3294_, 1, v_a_3254_);
v___x_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v___y_3255_);
v___x_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
return v___x_3296_;
}
else
{
uint8_t v___x_3297_; 
v___x_3297_ = lean_nat_dec_le(v___x_3260_, v___x_3260_);
if (v___x_3297_ == 0)
{
if (v___x_3293_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec_ref(v_leanOpts_3247_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3290_);
lean_ctor_set(v___x_3298_, 1, v_a_3254_);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v___y_3255_);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
else
{
size_t v___x_3301_; lean_object* v___x_3302_; 
lean_inc_ref(v_packages_3258_);
v___x_3301_ = lean_usize_of_nat(v___x_3260_);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(v_leanOpts_3247_, v_updateToolchain_3248_, v___x_3249_, v_packages_3258_, v___x_3301_, v___x_3301_, v___x_3290_, v_a_3254_, v___y_3255_, v___y_3256_);
lean_dec_ref(v_packages_3258_);
return v___x_3302_;
}
}
else
{
size_t v___x_3303_; lean_object* v___x_3304_; 
lean_inc_ref(v_packages_3258_);
v___x_3303_ = lean_usize_of_nat(v___x_3260_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(v_leanOpts_3247_, v_updateToolchain_3248_, v___x_3249_, v_packages_3258_, v___x_3303_, v___x_3303_, v___x_3290_, v_a_3254_, v___y_3255_, v___y_3256_);
lean_dec_ref(v_packages_3258_);
return v___x_3304_;
}
}
}
else
{
size_t v___x_3305_; size_t v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_usize_of_nat(v___x_3288_);
v___x_3306_ = ((size_t)0ULL);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_3252_, v_leanOpts_3250_, v_updateToolchain_3251_, v_depConfigs_3259_, v___x_3305_, v___x_3306_, v___x_3290_, v_a_3254_, v___y_3255_, v___y_3256_);
lean_dec_ref(v_depConfigs_3259_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v_fst_3309_; lean_object* v_snd_3310_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref(v___x_3307_);
v_fst_3309_ = lean_ctor_get(v_a_3308_, 0);
lean_inc(v_fst_3309_);
v_snd_3310_ = lean_ctor_get(v_a_3308_, 1);
lean_inc(v_snd_3310_);
lean_dec(v_a_3308_);
v_____x_3283_ = v_fst_3309_;
v___y_3284_ = v_snd_3310_;
v___y_3285_ = v___y_3256_;
goto v___jp_3282_;
}
else
{
lean_dec_ref(v_leanOpts_3247_);
return v___x_3307_;
}
}
}
else
{
uint8_t v___x_3311_; 
v___x_3311_ = lean_nat_dec_lt(v___x_3289_, v___x_3288_);
if (v___x_3311_ == 0)
{
lean_inc_ref(v_packages_3258_);
lean_dec_ref(v_depConfigs_3259_);
lean_dec_ref(v_pkg_3252_);
lean_dec_ref(v_leanOpts_3250_);
v_snd_3262_ = v_a_3254_;
v_packages_3263_ = v_packages_3258_;
v___y_3264_ = v___y_3255_;
v___y_3265_ = v___y_3256_;
goto v___jp_3261_;
}
else
{
size_t v___x_3312_; size_t v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_usize_of_nat(v___x_3288_);
v___x_3313_ = ((size_t)0ULL);
v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_3252_, v_leanOpts_3250_, v_updateToolchain_3251_, v_depConfigs_3259_, v___x_3312_, v___x_3313_, v___x_3290_, v_a_3254_, v___y_3255_, v___y_3256_);
lean_dec_ref(v_depConfigs_3259_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v_fst_3316_; lean_object* v_snd_3317_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3314_);
v_fst_3316_ = lean_ctor_get(v_a_3315_, 0);
lean_inc(v_fst_3316_);
v_snd_3317_ = lean_ctor_get(v_a_3315_, 1);
lean_inc(v_snd_3317_);
lean_dec(v_a_3315_);
v_____x_3283_ = v_fst_3316_;
v___y_3284_ = v_snd_3317_;
v___y_3285_ = v___y_3256_;
goto v___jp_3282_;
}
else
{
lean_dec_ref(v_leanOpts_3247_);
return v___x_3314_;
}
}
}
v___jp_3261_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3266_ = lean_array_get_size(v_packages_3263_);
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_nat_dec_lt(v___x_3260_, v___x_3266_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec_ref(v_packages_3263_);
lean_dec_ref(v_leanOpts_3247_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v_snd_3262_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
lean_ctor_set(v___x_3270_, 1, v___y_3264_);
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
return v___x_3271_;
}
else
{
uint8_t v___x_3272_; 
v___x_3272_ = lean_nat_dec_le(v___x_3266_, v___x_3266_);
if (v___x_3272_ == 0)
{
if (v___x_3268_ == 0)
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec_ref(v_packages_3263_);
lean_dec_ref(v_leanOpts_3247_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3267_);
lean_ctor_set(v___x_3273_, 1, v_snd_3262_);
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
lean_ctor_set(v___x_3274_, 1, v___y_3264_);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
else
{
size_t v___x_3276_; size_t v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = lean_usize_of_nat(v___x_3260_);
v___x_3277_ = lean_usize_of_nat(v___x_3266_);
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(v_leanOpts_3247_, v_updateToolchain_3248_, v___x_3249_, v_packages_3263_, v___x_3276_, v___x_3277_, v___x_3267_, v_snd_3262_, v___y_3264_, v___y_3265_);
lean_dec_ref(v_packages_3263_);
return v___x_3278_;
}
}
else
{
size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_usize_of_nat(v___x_3260_);
v___x_3280_ = lean_usize_of_nat(v___x_3266_);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(v_leanOpts_3247_, v_updateToolchain_3248_, v___x_3249_, v_packages_3263_, v___x_3279_, v___x_3280_, v___x_3267_, v_snd_3262_, v___y_3264_, v___y_3265_);
lean_dec_ref(v_packages_3263_);
return v___x_3281_;
}
}
}
v___jp_3282_:
{
lean_object* v_snd_3286_; lean_object* v_packages_3287_; 
v_snd_3286_ = lean_ctor_get(v_____x_3283_, 1);
lean_inc(v_snd_3286_);
lean_dec_ref(v_____x_3283_);
v_packages_3287_ = lean_ctor_get(v_snd_3286_, 5);
lean_inc_ref(v_packages_3287_);
v_snd_3262_ = v_snd_3286_;
v_packages_3263_ = v_packages_3287_;
v___y_3264_ = v___y_3284_;
v___y_3265_ = v___y_3285_;
goto v___jp_3261_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg(lean_object* v_leanOpts_3318_, uint8_t v_updateToolchain_3319_, lean_object* v_a_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_baseName_3326_; uint8_t v___x_3327_; 
v_baseName_3326_ = lean_ctor_get(v_a_3320_, 1);
v___x_3327_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11(v_baseName_3326_, v___y_3321_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_inc(v___y_3321_);
lean_inc(v_baseName_3326_);
v___x_3328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3328_, 0, v_baseName_3326_);
lean_ctor_set(v___x_3328_, 1, v___y_3321_);
lean_inc_ref(v_leanOpts_3318_);
v___x_3329_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35(v_leanOpts_3318_, v_updateToolchain_3319_, v___x_3328_, v_leanOpts_3318_, v_updateToolchain_3319_, v_a_3320_, v___x_3328_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec_ref(v___x_3328_);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v_fst_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3343_; 
lean_inc(v_baseName_3326_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v_a_3320_);
lean_dec_ref(v_leanOpts_3318_);
v___x_3330_ = lean_box(0);
v___x_3331_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___closed__0));
lean_inc(v___y_3321_);
v___x_3332_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13(v_baseName_3326_, v___x_3327_, v___y_3321_, v___x_3331_);
v_fst_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3343_ == 0)
{
lean_object* v_unused_3344_; 
v_unused_3344_ = lean_ctor_get(v___x_3332_, 1);
lean_dec(v_unused_3344_);
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3343_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_fst_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3343_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
lean_inc(v_baseName_3326_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 1);
lean_ctor_set(v___x_3335_, 1, v_fst_3333_);
lean_ctor_set(v___x_3335_, 0, v_baseName_3326_);
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_baseName_3326_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_fst_3333_);
v___x_3338_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v_baseName_3326_);
lean_ctor_set(v___x_3339_, 1, v___x_3330_);
v___x_3340_ = l_List_appendTR___redArg(v___x_3338_, v___x_3339_);
v___x_3341_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg(v___x_3340_, v___y_3324_);
return v___x_3341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___boxed(lean_object* v_leanOpts_3345_, lean_object* v_updateToolchain_3346_, lean_object* v_a_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v_updateToolchain_boxed_3353_; lean_object* v_res_3354_; 
v_updateToolchain_boxed_3353_ = lean_unbox(v_updateToolchain_3346_);
v_res_3354_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg(v_leanOpts_3345_, v_updateToolchain_boxed_3353_, v_a_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3348_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg___boxed(lean_object* v_leanOpts_3355_, lean_object* v_updateToolchain_3356_, lean_object* v___x_3357_, lean_object* v_as_3358_, lean_object* v_i_3359_, lean_object* v_stop_3360_, lean_object* v_b_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
uint8_t v_updateToolchain_boxed_3366_; size_t v_i_boxed_3367_; size_t v_stop_boxed_3368_; lean_object* v_res_3369_; 
v_updateToolchain_boxed_3366_ = lean_unbox(v_updateToolchain_3356_);
v_i_boxed_3367_ = lean_unbox_usize(v_i_3359_);
lean_dec(v_i_3359_);
v_stop_boxed_3368_ = lean_unbox_usize(v_stop_3360_);
lean_dec(v_stop_3360_);
v_res_3369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(v_leanOpts_3355_, v_updateToolchain_boxed_3366_, v___x_3357_, v_as_3358_, v_i_boxed_3367_, v_stop_boxed_3368_, v_b_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec_ref(v___y_3364_);
lean_dec_ref(v_as_3358_);
lean_dec(v___x_3357_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35___boxed(lean_object* v_leanOpts_3370_, lean_object* v_updateToolchain_3371_, lean_object* v___x_3372_, lean_object* v_leanOpts_3373_, lean_object* v_updateToolchain_3374_, lean_object* v_pkg_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
uint8_t v_updateToolchain_boxed_3381_; uint8_t v_updateToolchain_boxed_3382_; lean_object* v_res_3383_; 
v_updateToolchain_boxed_3381_ = lean_unbox(v_updateToolchain_3371_);
v_updateToolchain_boxed_3382_ = lean_unbox(v_updateToolchain_3374_);
v_res_3383_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35(v_leanOpts_3370_, v_updateToolchain_boxed_3381_, v___x_3372_, v_leanOpts_3373_, v_updateToolchain_boxed_3382_, v_pkg_3375_, v_a_3376_, v_a_3377_, v___y_3378_, v___y_3379_);
lean_dec_ref(v___y_3379_);
lean_dec(v_a_3376_);
lean_dec(v___x_3372_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(lean_object* v_leanOpts_3384_, uint8_t v_updateToolchain_3385_, lean_object* v_ws_3386_, lean_object* v_root_3387_, lean_object* v_stack_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg(v_leanOpts_3384_, v_updateToolchain_3385_, v_root_3387_, v_stack_3388_, v_ws_3386_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3411_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3411_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3411_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v_fst_3397_; lean_object* v_snd_3398_; lean_object* v_snd_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3409_; 
v_fst_3397_ = lean_ctor_get(v_a_3393_, 0);
lean_inc(v_fst_3397_);
v_snd_3398_ = lean_ctor_get(v_a_3393_, 1);
lean_inc(v_snd_3398_);
lean_dec(v_a_3393_);
v_snd_3399_ = lean_ctor_get(v_fst_3397_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_fst_3397_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v_fst_3397_, 0);
lean_dec(v_unused_3410_);
v___x_3401_ = v_fst_3397_;
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_snd_3399_);
lean_dec(v_fst_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3409_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v_snd_3398_);
lean_ctor_set(v___x_3401_, 0, v_snd_3399_);
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_snd_3399_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_snd_3398_);
v___x_3404_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3406_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3404_);
v___x_3406_ = v___x_3395_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
v_a_3412_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3392_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3392_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10___boxed(lean_object* v_leanOpts_3420_, lean_object* v_updateToolchain_3421_, lean_object* v_ws_3422_, lean_object* v_root_3423_, lean_object* v_stack_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v_updateToolchain_boxed_3428_; lean_object* v_res_3429_; 
v_updateToolchain_boxed_3428_ = lean_unbox(v_updateToolchain_3421_);
v_res_3429_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(v_leanOpts_3420_, v_updateToolchain_boxed_3428_, v_ws_3422_, v_root_3423_, v_stack_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___y_3426_);
lean_dec(v_stack_3424_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12(lean_object* v_leanOpts_3430_, uint8_t v_updateToolchain_3431_, lean_object* v_as_3432_, size_t v_i_3433_, size_t v_stop_3434_, lean_object* v_b_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_usize_dec_eq(v_i_3433_, v_stop_3434_);
if (v___x_3439_ == 0)
{
lean_object* v_root_3440_; lean_object* v_baseName_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_root_3440_ = lean_ctor_get(v_b_3435_, 0);
v_baseName_3441_ = lean_ctor_get(v_root_3440_, 1);
v___x_3442_ = lean_array_uget_borrowed(v_as_3432_, v_i_3433_);
v___x_3443_ = lean_box(0);
lean_inc(v_baseName_3441_);
v___x_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3444_, 0, v_baseName_3441_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
lean_inc(v___x_3442_);
lean_inc_ref(v_leanOpts_3430_);
v___x_3445_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10(v_leanOpts_3430_, v_updateToolchain_3431_, v_b_3435_, v___x_3442_, v___x_3444_, v___y_3436_, v___y_3437_);
lean_dec_ref(v___x_3444_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v_fst_3447_; lean_object* v_snd_3448_; size_t v___x_3449_; size_t v___x_3450_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref(v___x_3445_);
v_fst_3447_ = lean_ctor_get(v_a_3446_, 0);
lean_inc(v_fst_3447_);
v_snd_3448_ = lean_ctor_get(v_a_3446_, 1);
lean_inc(v_snd_3448_);
lean_dec(v_a_3446_);
v___x_3449_ = ((size_t)1ULL);
v___x_3450_ = lean_usize_add(v_i_3433_, v___x_3449_);
v_i_3433_ = v___x_3450_;
v_b_3435_ = v_fst_3447_;
v___y_3436_ = v_snd_3448_;
goto _start;
}
else
{
lean_dec_ref(v_leanOpts_3430_);
return v___x_3445_;
}
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec_ref(v_leanOpts_3430_);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v_b_3435_);
lean_ctor_set(v___x_3452_, 1, v___y_3436_);
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12___boxed(lean_object* v_leanOpts_3454_, lean_object* v_updateToolchain_3455_, lean_object* v_as_3456_, lean_object* v_i_3457_, lean_object* v_stop_3458_, lean_object* v_b_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
uint8_t v_updateToolchain_boxed_3463_; size_t v_i_boxed_3464_; size_t v_stop_boxed_3465_; lean_object* v_res_3466_; 
v_updateToolchain_boxed_3463_ = lean_unbox(v_updateToolchain_3455_);
v_i_boxed_3464_ = lean_unbox_usize(v_i_3457_);
lean_dec(v_i_3457_);
v_stop_boxed_3465_ = lean_unbox_usize(v_stop_3458_);
lean_dec(v_stop_3458_);
v_res_3466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12(v_leanOpts_3454_, v_updateToolchain_boxed_3463_, v_as_3456_, v_i_boxed_3464_, v_stop_boxed_3465_, v_b_3459_, v___y_3460_, v___y_3461_);
lean_dec_ref(v___y_3461_);
lean_dec_ref(v_as_3456_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(lean_object* v_pkg_3467_, lean_object* v_leanOpts_3468_, lean_object* v_as_3469_, size_t v_i_3470_, size_t v_stop_3471_, lean_object* v_b_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_usize_dec_eq(v_i_3470_, v_stop_3471_);
if (v___x_3477_ == 0)
{
lean_object* v_packages_3478_; size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___y_3485_; uint8_t v___x_3514_; 
v_packages_3478_ = lean_ctor_get(v___y_3473_, 5);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_sub(v_i_3470_, v___x_3479_);
v___x_3481_ = lean_array_uget_borrowed(v_as_3469_, v___x_3480_);
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = lean_array_get_size(v_packages_3478_);
v___x_3514_ = lean_nat_dec_lt(v___x_3482_, v___x_3483_);
if (v___x_3514_ == 0)
{
v___y_3485_ = v___x_3477_;
goto v___jp_3484_;
}
else
{
if (v___x_3514_ == 0)
{
v___y_3485_ = v___x_3477_;
goto v___jp_3484_;
}
else
{
size_t v___x_3515_; size_t v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = ((size_t)0ULL);
v___x_3516_ = lean_usize_of_nat(v___x_3483_);
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5(v___x_3481_, v_packages_3478_, v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
v___y_3485_ = v___x_3517_;
goto v___jp_3484_;
}
else
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_box(0);
v_i_3470_ = v___x_3480_;
v_b_3472_ = v___x_3518_;
goto _start;
}
}
}
v___jp_3484_:
{
lean_object* v_baseName_3486_; lean_object* v_name_3487_; uint8_t v___x_3488_; 
v_baseName_3486_ = lean_ctor_get(v_pkg_3467_, 1);
v_name_3487_ = lean_ctor_get(v___x_3481_, 0);
v___x_3488_ = lean_name_eq(v_baseName_3486_, v_name_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; 
lean_inc_ref(v___y_3475_);
lean_inc(v___x_3481_);
lean_inc_ref(v_pkg_3467_);
lean_inc_ref(v_leanOpts_3468_);
v___x_3489_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___elam__0(v_leanOpts_3468_, v_pkg_3467_, v___x_3481_, v___x_3483_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v_fst_3491_; lean_object* v_snd_3492_; lean_object* v_fst_3493_; lean_object* v_snd_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref(v___x_3489_);
v_fst_3491_ = lean_ctor_get(v_a_3490_, 0);
lean_inc(v_fst_3491_);
v_snd_3492_ = lean_ctor_get(v_a_3490_, 1);
lean_inc(v_snd_3492_);
lean_dec(v_a_3490_);
v_fst_3493_ = lean_ctor_get(v_fst_3491_, 0);
lean_inc(v_fst_3493_);
v_snd_3494_ = lean_ctor_get(v_fst_3491_, 1);
lean_inc(v_snd_3494_);
lean_dec(v_fst_3491_);
v___x_3495_ = lean_box(0);
v___x_3496_ = l_Lake_Workspace_addPackage(v_fst_3493_, v_snd_3494_);
v_i_3470_ = v___x_3480_;
v_b_3472_ = v___x_3495_;
v___y_3473_ = v___x_3496_;
v___y_3474_ = v_snd_3492_;
goto _start;
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v_leanOpts_3468_);
lean_dec_ref(v_pkg_3467_);
v_a_3498_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3489_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3489_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_inc(v_baseName_3486_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec_ref(v_leanOpts_3468_);
lean_dec_ref(v_pkg_3467_);
v___x_3506_ = l_Lean_Name_toString(v_baseName_3486_, v___y_3485_);
v___x_3507_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__0));
v___x_3508_ = lean_string_append(v___x_3506_, v___x_3507_);
v___x_3509_ = 3;
v___x_3510_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3510_, 0, v___x_3508_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*1, v___x_3509_);
lean_inc_ref(v___y_3475_);
v___x_3511_ = lean_apply_2(v___y_3475_, v___x_3510_, lean_box(0));
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
return v___x_3513_;
}
}
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_dec_ref(v_leanOpts_3468_);
lean_dec_ref(v_pkg_3467_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v_b_3472_);
lean_ctor_set(v___x_3520_, 1, v___y_3473_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___y_3474_);
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
return v___x_3522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg___boxed(lean_object* v_pkg_3523_, lean_object* v_leanOpts_3524_, lean_object* v_as_3525_, lean_object* v_i_3526_, lean_object* v_stop_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
size_t v_i_boxed_3533_; size_t v_stop_boxed_3534_; lean_object* v_res_3535_; 
v_i_boxed_3533_ = lean_unbox_usize(v_i_3526_);
lean_dec(v_i_3526_);
v_stop_boxed_3534_ = lean_unbox_usize(v_stop_3527_);
lean_dec(v_stop_3527_);
v_res_3535_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_3523_, v_leanOpts_3524_, v_as_3525_, v_i_boxed_3533_, v_stop_boxed_3534_, v_b_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v_as_3525_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(lean_object* v_leanOpts_3536_, lean_object* v___x_3537_, lean_object* v_as_3538_, size_t v_i_3539_, size_t v_stop_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
uint8_t v___x_3546_; 
v___x_3546_ = lean_usize_dec_eq(v_i_3539_, v_stop_3540_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_array_uget_borrowed(v_as_3538_, v_i_3539_);
lean_inc(v___x_3547_);
lean_inc_ref(v_leanOpts_3536_);
v___x_3548_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg(v_leanOpts_3536_, v___x_3547_, v___x_3537_, v___y_3542_, v___y_3543_, v___y_3544_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v_fst_3550_; lean_object* v_snd_3551_; lean_object* v_fst_3552_; lean_object* v_snd_3553_; size_t v___x_3554_; size_t v___x_3555_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref(v___x_3548_);
v_fst_3550_ = lean_ctor_get(v_a_3549_, 0);
lean_inc(v_fst_3550_);
v_snd_3551_ = lean_ctor_get(v_a_3549_, 1);
lean_inc(v_snd_3551_);
lean_dec(v_a_3549_);
v_fst_3552_ = lean_ctor_get(v_fst_3550_, 0);
lean_inc(v_fst_3552_);
v_snd_3553_ = lean_ctor_get(v_fst_3550_, 1);
lean_inc(v_snd_3553_);
lean_dec(v_fst_3550_);
v___x_3554_ = ((size_t)1ULL);
v___x_3555_ = lean_usize_add(v_i_3539_, v___x_3554_);
v_i_3539_ = v___x_3555_;
v_b_3541_ = v_fst_3552_;
v___y_3542_ = v_snd_3553_;
v___y_3543_ = v_snd_3551_;
goto _start;
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref(v_leanOpts_3536_);
v_a_3557_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3548_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3548_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_dec_ref(v_leanOpts_3536_);
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v_b_3541_);
lean_ctor_set(v___x_3565_, 1, v___y_3542_);
v___x_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
lean_ctor_set(v___x_3566_, 1, v___y_3543_);
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
return v___x_3567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31(lean_object* v_leanOpts_3568_, lean_object* v___x_3569_, lean_object* v_leanOpts_3570_, lean_object* v_pkg_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_packages_3577_; lean_object* v_depConfigs_3578_; lean_object* v___x_3579_; lean_object* v_snd_3581_; lean_object* v_packages_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v_____x_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v_packages_3577_ = lean_ctor_get(v_a_3573_, 5);
v_depConfigs_3578_ = lean_ctor_get(v_pkg_3571_, 12);
lean_inc_ref(v_depConfigs_3578_);
v___x_3579_ = lean_array_get_size(v_packages_3577_);
v___x_3607_ = lean_array_get_size(v_depConfigs_3578_);
v___x_3608_ = lean_unsigned_to_nat(0u);
v___x_3609_ = lean_box(0);
v___x_3610_ = lean_nat_dec_le(v___x_3607_, v___x_3607_);
if (v___x_3610_ == 0)
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_nat_dec_lt(v___x_3608_, v___x_3607_);
if (v___x_3611_ == 0)
{
uint8_t v___x_3612_; 
lean_dec_ref(v_depConfigs_3578_);
lean_dec_ref(v_pkg_3571_);
lean_dec_ref(v_leanOpts_3570_);
v___x_3612_ = lean_nat_dec_lt(v___x_3579_, v___x_3579_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v_leanOpts_3568_);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3609_);
lean_ctor_set(v___x_3613_, 1, v_a_3573_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v___y_3574_);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
return v___x_3615_;
}
else
{
uint8_t v___x_3616_; 
v___x_3616_ = lean_nat_dec_le(v___x_3579_, v___x_3579_);
if (v___x_3616_ == 0)
{
if (v___x_3612_ == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_dec_ref(v_leanOpts_3568_);
v___x_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3609_);
lean_ctor_set(v___x_3617_, 1, v_a_3573_);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v___y_3574_);
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
return v___x_3619_;
}
else
{
size_t v___x_3620_; lean_object* v___x_3621_; 
lean_inc_ref(v_packages_3577_);
v___x_3620_ = lean_usize_of_nat(v___x_3579_);
v___x_3621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(v_leanOpts_3568_, v___x_3569_, v_packages_3577_, v___x_3620_, v___x_3620_, v___x_3609_, v_a_3573_, v___y_3574_, v___y_3575_);
lean_dec_ref(v_packages_3577_);
return v___x_3621_;
}
}
else
{
size_t v___x_3622_; lean_object* v___x_3623_; 
lean_inc_ref(v_packages_3577_);
v___x_3622_ = lean_usize_of_nat(v___x_3579_);
v___x_3623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(v_leanOpts_3568_, v___x_3569_, v_packages_3577_, v___x_3622_, v___x_3622_, v___x_3609_, v_a_3573_, v___y_3574_, v___y_3575_);
lean_dec_ref(v_packages_3577_);
return v___x_3623_;
}
}
}
else
{
size_t v___x_3624_; size_t v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = lean_usize_of_nat(v___x_3607_);
v___x_3625_ = ((size_t)0ULL);
v___x_3626_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_3571_, v_leanOpts_3570_, v_depConfigs_3578_, v___x_3624_, v___x_3625_, v___x_3609_, v_a_3573_, v___y_3574_, v___y_3575_);
lean_dec_ref(v_depConfigs_3578_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v_fst_3628_; lean_object* v_snd_3629_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref(v___x_3626_);
v_fst_3628_ = lean_ctor_get(v_a_3627_, 0);
lean_inc(v_fst_3628_);
v_snd_3629_ = lean_ctor_get(v_a_3627_, 1);
lean_inc(v_snd_3629_);
lean_dec(v_a_3627_);
v_____x_3602_ = v_fst_3628_;
v___y_3603_ = v_snd_3629_;
v___y_3604_ = v___y_3575_;
goto v___jp_3601_;
}
else
{
lean_dec_ref(v_leanOpts_3568_);
return v___x_3626_;
}
}
}
else
{
uint8_t v___x_3630_; 
v___x_3630_ = lean_nat_dec_lt(v___x_3608_, v___x_3607_);
if (v___x_3630_ == 0)
{
lean_inc_ref(v_packages_3577_);
lean_dec_ref(v_depConfigs_3578_);
lean_dec_ref(v_pkg_3571_);
lean_dec_ref(v_leanOpts_3570_);
v_snd_3581_ = v_a_3573_;
v_packages_3582_ = v_packages_3577_;
v___y_3583_ = v___y_3574_;
v___y_3584_ = v___y_3575_;
goto v___jp_3580_;
}
else
{
size_t v___x_3631_; size_t v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = lean_usize_of_nat(v___x_3607_);
v___x_3632_ = ((size_t)0ULL);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_3571_, v_leanOpts_3570_, v_depConfigs_3578_, v___x_3631_, v___x_3632_, v___x_3609_, v_a_3573_, v___y_3574_, v___y_3575_);
lean_dec_ref(v_depConfigs_3578_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v_fst_3635_; lean_object* v_snd_3636_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref(v___x_3633_);
v_fst_3635_ = lean_ctor_get(v_a_3634_, 0);
lean_inc(v_fst_3635_);
v_snd_3636_ = lean_ctor_get(v_a_3634_, 1);
lean_inc(v_snd_3636_);
lean_dec(v_a_3634_);
v_____x_3602_ = v_fst_3635_;
v___y_3603_ = v_snd_3636_;
v___y_3604_ = v___y_3575_;
goto v___jp_3601_;
}
else
{
lean_dec_ref(v_leanOpts_3568_);
return v___x_3633_;
}
}
}
v___jp_3580_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v___x_3585_ = lean_array_get_size(v_packages_3582_);
v___x_3586_ = lean_box(0);
v___x_3587_ = lean_nat_dec_lt(v___x_3579_, v___x_3585_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec_ref(v_packages_3582_);
lean_dec_ref(v_leanOpts_3568_);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set(v___x_3588_, 1, v_snd_3581_);
v___x_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v___y_3583_);
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
else
{
uint8_t v___x_3591_; 
v___x_3591_ = lean_nat_dec_le(v___x_3585_, v___x_3585_);
if (v___x_3591_ == 0)
{
if (v___x_3587_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
lean_dec_ref(v_packages_3582_);
lean_dec_ref(v_leanOpts_3568_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3586_);
lean_ctor_set(v___x_3592_, 1, v_snd_3581_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v___y_3583_);
v___x_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
return v___x_3594_;
}
else
{
size_t v___x_3595_; size_t v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = lean_usize_of_nat(v___x_3579_);
v___x_3596_ = lean_usize_of_nat(v___x_3585_);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(v_leanOpts_3568_, v___x_3569_, v_packages_3582_, v___x_3595_, v___x_3596_, v___x_3586_, v_snd_3581_, v___y_3583_, v___y_3584_);
lean_dec_ref(v_packages_3582_);
return v___x_3597_;
}
}
else
{
size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = lean_usize_of_nat(v___x_3579_);
v___x_3599_ = lean_usize_of_nat(v___x_3585_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(v_leanOpts_3568_, v___x_3569_, v_packages_3582_, v___x_3598_, v___x_3599_, v___x_3586_, v_snd_3581_, v___y_3583_, v___y_3584_);
lean_dec_ref(v_packages_3582_);
return v___x_3600_;
}
}
}
v___jp_3601_:
{
lean_object* v_snd_3605_; lean_object* v_packages_3606_; 
v_snd_3605_ = lean_ctor_get(v_____x_3602_, 1);
lean_inc(v_snd_3605_);
lean_dec_ref(v_____x_3602_);
v_packages_3606_ = lean_ctor_get(v_snd_3605_, 5);
lean_inc_ref(v_packages_3606_);
v_snd_3581_ = v_snd_3605_;
v_packages_3582_ = v_packages_3606_;
v___y_3583_ = v___y_3603_;
v___y_3584_ = v___y_3604_;
goto v___jp_3580_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg(lean_object* v_leanOpts_3637_, lean_object* v_a_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_baseName_3644_; uint8_t v___x_3645_; 
v_baseName_3644_ = lean_ctor_get(v_a_3638_, 1);
v___x_3645_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11(v_baseName_3644_, v___y_3639_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_inc(v___y_3639_);
lean_inc(v_baseName_3644_);
v___x_3646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3646_, 0, v_baseName_3644_);
lean_ctor_set(v___x_3646_, 1, v___y_3639_);
lean_inc_ref(v_leanOpts_3637_);
v___x_3647_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31(v_leanOpts_3637_, v___x_3646_, v_leanOpts_3637_, v_a_3638_, v___x_3646_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec_ref(v___x_3646_);
return v___x_3647_;
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v_fst_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3661_; 
lean_inc(v_baseName_3644_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v_a_3638_);
lean_dec_ref(v_leanOpts_3637_);
v___x_3648_ = lean_box(0);
v___x_3649_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___closed__0));
lean_inc(v___y_3639_);
v___x_3650_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13(v_baseName_3644_, v___x_3645_, v___y_3639_, v___x_3649_);
v_fst_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; 
v_unused_3662_ = lean_ctor_get(v___x_3650_, 1);
lean_dec(v_unused_3662_);
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3661_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_fst_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3661_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
lean_inc(v_baseName_3644_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 1);
lean_ctor_set(v___x_3653_, 1, v_fst_3651_);
lean_ctor_set(v___x_3653_, 0, v_baseName_3644_);
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_baseName_3644_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_fst_3651_);
v___x_3656_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3657_, 0, v_baseName_3644_);
lean_ctor_set(v___x_3657_, 1, v___x_3648_);
v___x_3658_ = l_List_appendTR___redArg(v___x_3656_, v___x_3657_);
v___x_3659_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg(v___x_3658_, v___y_3642_);
return v___x_3659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg___boxed(lean_object* v_leanOpts_3663_, lean_object* v_a_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg(v_leanOpts_3663_, v_a_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3665_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg___boxed(lean_object* v_leanOpts_3671_, lean_object* v___x_3672_, lean_object* v_as_3673_, lean_object* v_i_3674_, lean_object* v_stop_3675_, lean_object* v_b_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
size_t v_i_boxed_3681_; size_t v_stop_boxed_3682_; lean_object* v_res_3683_; 
v_i_boxed_3681_ = lean_unbox_usize(v_i_3674_);
lean_dec(v_i_3674_);
v_stop_boxed_3682_ = lean_unbox_usize(v_stop_3675_);
lean_dec(v_stop_3675_);
v_res_3683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(v_leanOpts_3671_, v___x_3672_, v_as_3673_, v_i_boxed_3681_, v_stop_boxed_3682_, v_b_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
lean_dec_ref(v___y_3679_);
lean_dec_ref(v_as_3673_);
lean_dec(v___x_3672_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31___boxed(lean_object* v_leanOpts_3684_, lean_object* v___x_3685_, lean_object* v_leanOpts_3686_, lean_object* v_pkg_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31(v_leanOpts_3684_, v___x_3685_, v_leanOpts_3686_, v_pkg_3687_, v_a_3688_, v_a_3689_, v___y_3690_, v___y_3691_);
lean_dec_ref(v___y_3691_);
lean_dec(v_a_3688_);
lean_dec(v___x_3685_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(lean_object* v_leanOpts_3694_, lean_object* v_ws_3695_, lean_object* v_root_3696_, lean_object* v_stack_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg(v_leanOpts_3694_, v_root_3696_, v_stack_3697_, v_ws_3695_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3720_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3720_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3720_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v_fst_3706_; lean_object* v_snd_3707_; lean_object* v_snd_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3718_; 
v_fst_3706_ = lean_ctor_get(v_a_3702_, 0);
lean_inc(v_fst_3706_);
v_snd_3707_ = lean_ctor_get(v_a_3702_, 1);
lean_inc(v_snd_3707_);
lean_dec(v_a_3702_);
v_snd_3708_ = lean_ctor_get(v_fst_3706_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_fst_3706_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; 
v_unused_3719_ = lean_ctor_get(v_fst_3706_, 0);
lean_dec(v_unused_3719_);
v___x_3710_ = v_fst_3706_;
v_isShared_3711_ = v_isSharedCheck_3718_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_snd_3708_);
lean_dec(v_fst_3706_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3718_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 1, v_snd_3707_);
lean_ctor_set(v___x_3710_, 0, v_snd_3708_);
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_snd_3708_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_snd_3707_);
v___x_3713_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3715_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3713_);
v___x_3715_ = v___x_3704_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
v_a_3721_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3701_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3701_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6___boxed(lean_object* v_leanOpts_3729_, lean_object* v_ws_3730_, lean_object* v_root_3731_, lean_object* v_stack_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_leanOpts_3729_, v_ws_3730_, v_root_3731_, v_stack_3732_, v___y_3733_, v___y_3734_);
lean_dec_ref(v___y_3734_);
lean_dec(v_stack_3732_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18___redArg(lean_object* v_msg_3737_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_box(1);
v___x_3739_ = lean_panic_fn(v___x_3738_, v_msg_3737_);
return v___x_3739_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3743_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__2));
v___x_3744_ = lean_unsigned_to_nat(35u);
v___x_3745_ = lean_unsigned_to_nat(276u);
v___x_3746_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__1));
v___x_3747_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__0));
v___x_3748_ = l_mkPanicMessageWithDecl(v___x_3747_, v___x_3746_, v___x_3745_, v___x_3744_, v___x_3743_);
return v___x_3748_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3749_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__2));
v___x_3750_ = lean_unsigned_to_nat(21u);
v___x_3751_ = lean_unsigned_to_nat(277u);
v___x_3752_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__1));
v___x_3753_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__0));
v___x_3754_ = l_mkPanicMessageWithDecl(v___x_3753_, v___x_3752_, v___x_3751_, v___x_3750_, v___x_3749_);
return v___x_3754_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__7(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3757_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__6));
v___x_3758_ = lean_unsigned_to_nat(35u);
v___x_3759_ = lean_unsigned_to_nat(182u);
v___x_3760_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__5));
v___x_3761_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__0));
v___x_3762_ = l_mkPanicMessageWithDecl(v___x_3761_, v___x_3760_, v___x_3759_, v___x_3758_, v___x_3757_);
return v___x_3762_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__8(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3763_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__6));
v___x_3764_ = lean_unsigned_to_nat(21u);
v___x_3765_ = lean_unsigned_to_nat(183u);
v___x_3766_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__5));
v___x_3767_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__0));
v___x_3768_ = l_mkPanicMessageWithDecl(v___x_3767_, v___x_3766_, v___x_3765_, v___x_3764_, v___x_3763_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg(lean_object* v_k_3769_, lean_object* v_v_3770_, lean_object* v_t_3771_){
_start:
{
if (lean_obj_tag(v_t_3771_) == 0)
{
lean_object* v_size_3772_; lean_object* v_k_3773_; lean_object* v_v_3774_; lean_object* v_l_3775_; lean_object* v_r_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_4133_; 
v_size_3772_ = lean_ctor_get(v_t_3771_, 0);
v_k_3773_ = lean_ctor_get(v_t_3771_, 1);
v_v_3774_ = lean_ctor_get(v_t_3771_, 2);
v_l_3775_ = lean_ctor_get(v_t_3771_, 3);
v_r_3776_ = lean_ctor_get(v_t_3771_, 4);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_t_3771_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_3778_ = v_t_3771_;
v_isShared_3779_ = v_isSharedCheck_4133_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_r_3776_);
lean_inc(v_l_3775_);
lean_inc(v_v_3774_);
lean_inc(v_k_3773_);
lean_inc(v_size_3772_);
lean_dec(v_t_3771_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_4133_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
uint8_t v___x_3780_; 
v___x_3780_ = lean_string_dec_lt(v_k_3769_, v_k_3773_);
if (v___x_3780_ == 0)
{
uint8_t v___x_3781_; 
v___x_3781_ = lean_string_dec_eq(v_k_3769_, v_k_3773_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; 
lean_dec(v_size_3772_);
v___x_3782_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg(v_k_3769_, v_v_3770_, v_r_3776_);
if (lean_obj_tag(v_l_3775_) == 0)
{
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_size_3783_; lean_object* v_size_3784_; lean_object* v_k_3785_; lean_object* v_v_3786_; lean_object* v_l_3787_; lean_object* v_r_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; 
v_size_3783_ = lean_ctor_get(v_l_3775_, 0);
v_size_3784_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_size_3784_);
v_k_3785_ = lean_ctor_get(v___x_3782_, 1);
lean_inc(v_k_3785_);
v_v_3786_ = lean_ctor_get(v___x_3782_, 2);
lean_inc(v_v_3786_);
v_l_3787_ = lean_ctor_get(v___x_3782_, 3);
lean_inc(v_l_3787_);
v_r_3788_ = lean_ctor_get(v___x_3782_, 4);
lean_inc(v_r_3788_);
v___x_3789_ = lean_unsigned_to_nat(3u);
v___x_3790_ = lean_nat_mul(v___x_3789_, v_size_3783_);
v___x_3791_ = lean_nat_dec_lt(v___x_3790_, v_size_3784_);
lean_dec(v___x_3790_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
lean_dec(v_r_3788_);
lean_dec(v_l_3787_);
lean_dec(v_v_3786_);
lean_dec(v_k_3785_);
v___x_3792_ = lean_unsigned_to_nat(1u);
v___x_3793_ = lean_nat_add(v___x_3792_, v_size_3783_);
v___x_3794_ = lean_nat_add(v___x_3793_, v_size_3784_);
lean_dec(v_size_3784_);
lean_dec(v___x_3793_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3782_);
lean_ctor_set(v___x_3778_, 0, v___x_3794_);
v___x_3796_ = v___x_3778_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3797_, 4, v___x_3782_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
else
{
lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3867_; 
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; 
v_unused_3868_ = lean_ctor_get(v___x_3782_, 4);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v___x_3782_, 3);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v___x_3782_, 2);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v___x_3782_, 1);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v___x_3782_, 0);
lean_dec(v_unused_3872_);
v___x_3799_ = v___x_3782_;
v_isShared_3800_ = v_isSharedCheck_3867_;
goto v_resetjp_3798_;
}
else
{
lean_dec(v___x_3782_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3867_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
if (lean_obj_tag(v_l_3787_) == 0)
{
if (lean_obj_tag(v_r_3788_) == 0)
{
lean_object* v_size_3801_; lean_object* v_k_3802_; lean_object* v_v_3803_; lean_object* v_l_3804_; lean_object* v_r_3805_; lean_object* v_size_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v_size_3801_ = lean_ctor_get(v_l_3787_, 0);
v_k_3802_ = lean_ctor_get(v_l_3787_, 1);
v_v_3803_ = lean_ctor_get(v_l_3787_, 2);
v_l_3804_ = lean_ctor_get(v_l_3787_, 3);
v_r_3805_ = lean_ctor_get(v_l_3787_, 4);
v_size_3806_ = lean_ctor_get(v_r_3788_, 0);
v___x_3807_ = lean_unsigned_to_nat(2u);
v___x_3808_ = lean_nat_mul(v___x_3807_, v_size_3806_);
v___x_3809_ = lean_nat_dec_lt(v_size_3801_, v___x_3808_);
lean_dec(v___x_3808_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3838_; 
lean_inc(v_r_3805_);
lean_inc(v_l_3804_);
lean_inc(v_v_3803_);
lean_inc(v_k_3802_);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_l_3787_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; lean_object* v_unused_3840_; lean_object* v_unused_3841_; lean_object* v_unused_3842_; lean_object* v_unused_3843_; 
v_unused_3839_ = lean_ctor_get(v_l_3787_, 4);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_l_3787_, 3);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_l_3787_, 2);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_l_3787_, 1);
lean_dec(v_unused_3842_);
v_unused_3843_ = lean_ctor_get(v_l_3787_, 0);
lean_dec(v_unused_3843_);
v___x_3811_ = v_l_3787_;
v_isShared_3812_ = v_isSharedCheck_3838_;
goto v_resetjp_3810_;
}
else
{
lean_dec(v_l_3787_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3838_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3828_; 
v___x_3813_ = lean_unsigned_to_nat(1u);
v___x_3814_ = lean_nat_add(v___x_3813_, v_size_3783_);
v___x_3815_ = lean_nat_add(v___x_3814_, v_size_3784_);
lean_dec(v_size_3784_);
if (lean_obj_tag(v_l_3804_) == 0)
{
lean_object* v_size_3836_; 
v_size_3836_ = lean_ctor_get(v_l_3804_, 0);
lean_inc(v_size_3836_);
v___y_3828_ = v_size_3836_;
goto v___jp_3827_;
}
else
{
lean_object* v___x_3837_; 
v___x_3837_ = lean_unsigned_to_nat(0u);
v___y_3828_ = v___x_3837_;
goto v___jp_3827_;
}
v___jp_3816_:
{
lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3820_ = lean_nat_add(v___y_3817_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec(v___y_3817_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 4, v_r_3788_);
lean_ctor_set(v___x_3811_, 3, v_r_3805_);
lean_ctor_set(v___x_3811_, 2, v_v_3786_);
lean_ctor_set(v___x_3811_, 1, v_k_3785_);
lean_ctor_set(v___x_3811_, 0, v___x_3820_);
v___x_3822_ = v___x_3811_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_k_3785_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v_v_3786_);
lean_ctor_set(v_reuseFailAlloc_3826_, 3, v_r_3805_);
lean_ctor_set(v_reuseFailAlloc_3826_, 4, v_r_3788_);
v___x_3822_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3824_; 
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 4, v___x_3822_);
lean_ctor_set(v___x_3799_, 3, v___y_3818_);
lean_ctor_set(v___x_3799_, 2, v_v_3803_);
lean_ctor_set(v___x_3799_, 1, v_k_3802_);
lean_ctor_set(v___x_3799_, 0, v___x_3815_);
v___x_3824_ = v___x_3799_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v_k_3802_);
lean_ctor_set(v_reuseFailAlloc_3825_, 2, v_v_3803_);
lean_ctor_set(v_reuseFailAlloc_3825_, 3, v___y_3818_);
lean_ctor_set(v_reuseFailAlloc_3825_, 4, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
v___jp_3827_:
{
lean_object* v___x_3829_; lean_object* v___x_3831_; 
v___x_3829_ = lean_nat_add(v___x_3814_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec(v___x_3814_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_l_3804_);
lean_ctor_set(v___x_3778_, 0, v___x_3829_);
v___x_3831_ = v___x_3778_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3835_, 4, v_l_3804_);
v___x_3831_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_nat_add(v___x_3813_, v_size_3806_);
if (lean_obj_tag(v_r_3805_) == 0)
{
lean_object* v_size_3833_; 
v_size_3833_ = lean_ctor_get(v_r_3805_, 0);
lean_inc(v_size_3833_);
v___y_3817_ = v___x_3832_;
v___y_3818_ = v___x_3831_;
v___y_3819_ = v_size_3833_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_unsigned_to_nat(0u);
v___y_3817_ = v___x_3832_;
v___y_3818_ = v___x_3831_;
v___y_3819_ = v___x_3834_;
goto v___jp_3816_;
}
}
}
}
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3849_; 
lean_del_object(v___x_3778_);
v___x_3844_ = lean_unsigned_to_nat(1u);
v___x_3845_ = lean_nat_add(v___x_3844_, v_size_3783_);
v___x_3846_ = lean_nat_add(v___x_3845_, v_size_3784_);
lean_dec(v_size_3784_);
v___x_3847_ = lean_nat_add(v___x_3845_, v_size_3801_);
lean_dec(v___x_3845_);
lean_inc_ref(v_l_3775_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 4, v_l_3787_);
lean_ctor_set(v___x_3799_, 3, v_l_3775_);
lean_ctor_set(v___x_3799_, 2, v_v_3774_);
lean_ctor_set(v___x_3799_, 1, v_k_3773_);
lean_ctor_set(v___x_3799_, 0, v___x_3847_);
v___x_3849_ = v___x_3799_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v_l_3787_);
v___x_3849_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_isSharedCheck_3856_ = !lean_is_exclusive(v_l_3775_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; lean_object* v_unused_3858_; lean_object* v_unused_3859_; lean_object* v_unused_3860_; lean_object* v_unused_3861_; 
v_unused_3857_ = lean_ctor_get(v_l_3775_, 4);
lean_dec(v_unused_3857_);
v_unused_3858_ = lean_ctor_get(v_l_3775_, 3);
lean_dec(v_unused_3858_);
v_unused_3859_ = lean_ctor_get(v_l_3775_, 2);
lean_dec(v_unused_3859_);
v_unused_3860_ = lean_ctor_get(v_l_3775_, 1);
lean_dec(v_unused_3860_);
v_unused_3861_ = lean_ctor_get(v_l_3775_, 0);
lean_dec(v_unused_3861_);
v___x_3851_ = v_l_3775_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_dec(v_l_3775_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
lean_ctor_set(v___x_3851_, 4, v_r_3788_);
lean_ctor_set(v___x_3851_, 3, v___x_3849_);
lean_ctor_set(v___x_3851_, 2, v_v_3786_);
lean_ctor_set(v___x_3851_, 1, v_k_3785_);
lean_ctor_set(v___x_3851_, 0, v___x_3846_);
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3785_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3786_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v_r_3788_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
else
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_dec_ref(v_l_3787_);
lean_del_object(v___x_3799_);
lean_dec(v_v_3786_);
lean_dec(v_k_3785_);
lean_dec(v_size_3784_);
lean_dec_ref(v_l_3775_);
lean_del_object(v___x_3778_);
lean_dec(v_v_3774_);
lean_dec(v_k_3773_);
v___x_3863_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__3);
v___x_3864_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18___redArg(v___x_3863_);
return v___x_3864_;
}
}
else
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_del_object(v___x_3799_);
lean_dec(v_r_3788_);
lean_dec(v_v_3786_);
lean_dec(v_k_3785_);
lean_dec(v_size_3784_);
lean_dec_ref(v_l_3775_);
lean_del_object(v___x_3778_);
lean_dec(v_v_3774_);
lean_dec(v_k_3773_);
v___x_3865_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__4, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__4_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__4);
v___x_3866_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18___redArg(v___x_3865_);
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_size_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v_size_3873_ = lean_ctor_get(v_l_3775_, 0);
v___x_3874_ = lean_unsigned_to_nat(1u);
v___x_3875_ = lean_nat_add(v___x_3874_, v_size_3873_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3782_);
lean_ctor_set(v___x_3778_, 0, v___x_3875_);
v___x_3877_ = v___x_3778_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3878_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3878_, 4, v___x_3782_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
else
{
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_l_3879_; 
v_l_3879_ = lean_ctor_get(v___x_3782_, 3);
lean_inc(v_l_3879_);
if (lean_obj_tag(v_l_3879_) == 0)
{
lean_object* v_r_3880_; 
v_r_3880_ = lean_ctor_get(v___x_3782_, 4);
lean_inc(v_r_3880_);
if (lean_obj_tag(v_r_3880_) == 0)
{
lean_object* v_size_3881_; lean_object* v_k_3882_; lean_object* v_v_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3897_; 
v_size_3881_ = lean_ctor_get(v___x_3782_, 0);
v_k_3882_ = lean_ctor_get(v___x_3782_, 1);
v_v_3883_ = lean_ctor_get(v___x_3782_, 2);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3897_ == 0)
{
lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3898_ = lean_ctor_get(v___x_3782_, 4);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v___x_3782_, 3);
lean_dec(v_unused_3899_);
v___x_3885_ = v___x_3782_;
v_isShared_3886_ = v_isSharedCheck_3897_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_v_3883_);
lean_inc(v_k_3882_);
lean_inc(v_size_3881_);
lean_dec(v___x_3782_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3897_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v_size_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
v_size_3887_ = lean_ctor_get(v_l_3879_, 0);
v___x_3888_ = lean_unsigned_to_nat(1u);
v___x_3889_ = lean_nat_add(v___x_3888_, v_size_3881_);
lean_dec(v_size_3881_);
v___x_3890_ = lean_nat_add(v___x_3888_, v_size_3887_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 4, v_l_3879_);
lean_ctor_set(v___x_3885_, 3, v_l_3775_);
lean_ctor_set(v___x_3885_, 2, v_v_3774_);
lean_ctor_set(v___x_3885_, 1, v_k_3773_);
lean_ctor_set(v___x_3885_, 0, v___x_3890_);
v___x_3892_ = v___x_3885_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3890_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3896_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3896_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3896_, 4, v_l_3879_);
v___x_3892_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3894_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_r_3880_);
lean_ctor_set(v___x_3778_, 3, v___x_3892_);
lean_ctor_set(v___x_3778_, 2, v_v_3883_);
lean_ctor_set(v___x_3778_, 1, v_k_3882_);
lean_ctor_set(v___x_3778_, 0, v___x_3889_);
v___x_3894_ = v___x_3778_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_k_3882_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v_v_3883_);
lean_ctor_set(v_reuseFailAlloc_3895_, 3, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3895_, 4, v_r_3880_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_object* v_k_3900_; lean_object* v_v_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3925_; 
v_k_3900_ = lean_ctor_get(v___x_3782_, 1);
v_v_3901_ = lean_ctor_get(v___x_3782_, 2);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; lean_object* v_unused_3927_; lean_object* v_unused_3928_; 
v_unused_3926_ = lean_ctor_get(v___x_3782_, 4);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v___x_3782_, 3);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v___x_3782_, 0);
lean_dec(v_unused_3928_);
v___x_3903_ = v___x_3782_;
v_isShared_3904_ = v_isSharedCheck_3925_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_v_3901_);
lean_inc(v_k_3900_);
lean_dec(v___x_3782_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3925_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v_k_3905_; lean_object* v_v_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3921_; 
v_k_3905_ = lean_ctor_get(v_l_3879_, 1);
v_v_3906_ = lean_ctor_get(v_l_3879_, 2);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_l_3879_);
if (v_isSharedCheck_3921_ == 0)
{
lean_object* v_unused_3922_; lean_object* v_unused_3923_; lean_object* v_unused_3924_; 
v_unused_3922_ = lean_ctor_get(v_l_3879_, 4);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_l_3879_, 3);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_l_3879_, 0);
lean_dec(v_unused_3924_);
v___x_3908_ = v_l_3879_;
v_isShared_3909_ = v_isSharedCheck_3921_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_v_3906_);
lean_inc(v_k_3905_);
lean_dec(v_l_3879_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3921_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3910_ = lean_unsigned_to_nat(3u);
v___x_3911_ = lean_unsigned_to_nat(1u);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 4, v_r_3880_);
lean_ctor_set(v___x_3908_, 3, v_r_3880_);
lean_ctor_set(v___x_3908_, 2, v_v_3774_);
lean_ctor_set(v___x_3908_, 1, v_k_3773_);
lean_ctor_set(v___x_3908_, 0, v___x_3911_);
v___x_3913_ = v___x_3908_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3920_, 3, v_r_3880_);
lean_ctor_set(v_reuseFailAlloc_3920_, 4, v_r_3880_);
v___x_3913_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 3, v_r_3880_);
lean_ctor_set(v___x_3903_, 0, v___x_3911_);
v___x_3915_ = v___x_3903_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_k_3900_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v_v_3901_);
lean_ctor_set(v_reuseFailAlloc_3919_, 3, v_r_3880_);
lean_ctor_set(v_reuseFailAlloc_3919_, 4, v_r_3880_);
v___x_3915_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3915_);
lean_ctor_set(v___x_3778_, 3, v___x_3913_);
lean_ctor_set(v___x_3778_, 2, v_v_3906_);
lean_ctor_set(v___x_3778_, 1, v_k_3905_);
lean_ctor_set(v___x_3778_, 0, v___x_3910_);
v___x_3917_ = v___x_3778_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_k_3905_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v_v_3906_);
lean_ctor_set(v_reuseFailAlloc_3918_, 3, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3918_, 4, v___x_3915_);
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
}
}
else
{
lean_object* v_r_3929_; 
v_r_3929_ = lean_ctor_get(v___x_3782_, 4);
lean_inc(v_r_3929_);
if (lean_obj_tag(v_r_3929_) == 0)
{
lean_object* v_k_3930_; lean_object* v_v_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3943_; 
v_k_3930_ = lean_ctor_get(v___x_3782_, 1);
v_v_3931_ = lean_ctor_get(v___x_3782_, 2);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; lean_object* v_unused_3945_; lean_object* v_unused_3946_; 
v_unused_3944_ = lean_ctor_get(v___x_3782_, 4);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v___x_3782_, 3);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v___x_3782_, 0);
lean_dec(v_unused_3946_);
v___x_3933_ = v___x_3782_;
v_isShared_3934_ = v_isSharedCheck_3943_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_v_3931_);
lean_inc(v_k_3930_);
lean_dec(v___x_3782_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3943_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3935_ = lean_unsigned_to_nat(3u);
v___x_3936_ = lean_unsigned_to_nat(1u);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 4, v_l_3879_);
lean_ctor_set(v___x_3933_, 2, v_v_3774_);
lean_ctor_set(v___x_3933_, 1, v_k_3773_);
lean_ctor_set(v___x_3933_, 0, v___x_3936_);
v___x_3938_ = v___x_3933_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3942_, 3, v_l_3879_);
lean_ctor_set(v_reuseFailAlloc_3942_, 4, v_l_3879_);
v___x_3938_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_r_3929_);
lean_ctor_set(v___x_3778_, 3, v___x_3938_);
lean_ctor_set(v___x_3778_, 2, v_v_3931_);
lean_ctor_set(v___x_3778_, 1, v_k_3930_);
lean_ctor_set(v___x_3778_, 0, v___x_3935_);
v___x_3940_ = v___x_3778_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_k_3930_);
lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_v_3931_);
lean_ctor_set(v_reuseFailAlloc_3941_, 3, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_r_3929_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3947_ = lean_unsigned_to_nat(2u);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3782_);
lean_ctor_set(v___x_3778_, 3, v_r_3929_);
lean_ctor_set(v___x_3778_, 0, v___x_3947_);
v___x_3949_ = v___x_3778_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3950_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3950_, 3, v_r_3929_);
lean_ctor_set(v_reuseFailAlloc_3950_, 4, v___x_3782_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3953_; 
v___x_3951_ = lean_unsigned_to_nat(1u);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3782_);
lean_ctor_set(v___x_3778_, 3, v___x_3782_);
lean_ctor_set(v___x_3778_, 0, v___x_3951_);
v___x_3953_ = v___x_3778_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3954_, 3, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3954_, 4, v___x_3782_);
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
else
{
lean_object* v___x_3956_; 
lean_dec(v_v_3774_);
lean_dec(v_k_3773_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 2, v_v_3770_);
lean_ctor_set(v___x_3778_, 1, v_k_3769_);
v___x_3956_ = v___x_3778_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_size_3772_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v_k_3769_);
lean_ctor_set(v_reuseFailAlloc_3957_, 2, v_v_3770_);
lean_ctor_set(v_reuseFailAlloc_3957_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3957_, 4, v_r_3776_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
else
{
lean_object* v___x_3958_; 
lean_dec(v_size_3772_);
v___x_3958_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg(v_k_3769_, v_v_3770_, v_l_3775_);
if (lean_obj_tag(v_r_3776_) == 0)
{
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_size_3959_; lean_object* v_size_3960_; lean_object* v_k_3961_; lean_object* v_v_3962_; lean_object* v_l_3963_; lean_object* v_r_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v_size_3959_ = lean_ctor_get(v_r_3776_, 0);
v_size_3960_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_size_3960_);
v_k_3961_ = lean_ctor_get(v___x_3958_, 1);
lean_inc(v_k_3961_);
v_v_3962_ = lean_ctor_get(v___x_3958_, 2);
lean_inc(v_v_3962_);
v_l_3963_ = lean_ctor_get(v___x_3958_, 3);
lean_inc(v_l_3963_);
v_r_3964_ = lean_ctor_get(v___x_3958_, 4);
lean_inc(v_r_3964_);
v___x_3965_ = lean_unsigned_to_nat(3u);
v___x_3966_ = lean_nat_mul(v___x_3965_, v_size_3959_);
v___x_3967_ = lean_nat_dec_lt(v___x_3966_, v_size_3960_);
lean_dec(v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3972_; 
lean_dec(v_r_3964_);
lean_dec(v_l_3963_);
lean_dec(v_v_3962_);
lean_dec(v_k_3961_);
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_nat_add(v___x_3968_, v_size_3960_);
lean_dec(v_size_3960_);
v___x_3970_ = lean_nat_add(v___x_3969_, v_size_3959_);
lean_dec(v___x_3969_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 3, v___x_3958_);
lean_ctor_set(v___x_3778_, 0, v___x_3970_);
v___x_3972_ = v___x_3778_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_3973_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_3973_, 3, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3973_, 4, v_r_3776_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
else
{
lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4045_; 
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4045_ == 0)
{
lean_object* v_unused_4046_; lean_object* v_unused_4047_; lean_object* v_unused_4048_; lean_object* v_unused_4049_; lean_object* v_unused_4050_; 
v_unused_4046_ = lean_ctor_get(v___x_3958_, 4);
lean_dec(v_unused_4046_);
v_unused_4047_ = lean_ctor_get(v___x_3958_, 3);
lean_dec(v_unused_4047_);
v_unused_4048_ = lean_ctor_get(v___x_3958_, 2);
lean_dec(v_unused_4048_);
v_unused_4049_ = lean_ctor_get(v___x_3958_, 1);
lean_dec(v_unused_4049_);
v_unused_4050_ = lean_ctor_get(v___x_3958_, 0);
lean_dec(v_unused_4050_);
v___x_3975_ = v___x_3958_;
v_isShared_3976_ = v_isSharedCheck_4045_;
goto v_resetjp_3974_;
}
else
{
lean_dec(v___x_3958_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4045_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
if (lean_obj_tag(v_l_3963_) == 0)
{
if (lean_obj_tag(v_r_3964_) == 0)
{
lean_object* v_size_3977_; lean_object* v_size_3978_; lean_object* v_k_3979_; lean_object* v_v_3980_; lean_object* v_l_3981_; lean_object* v_r_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; 
v_size_3977_ = lean_ctor_get(v_l_3963_, 0);
v_size_3978_ = lean_ctor_get(v_r_3964_, 0);
v_k_3979_ = lean_ctor_get(v_r_3964_, 1);
v_v_3980_ = lean_ctor_get(v_r_3964_, 2);
v_l_3981_ = lean_ctor_get(v_r_3964_, 3);
v_r_3982_ = lean_ctor_get(v_r_3964_, 4);
v___x_3983_ = lean_unsigned_to_nat(2u);
v___x_3984_ = lean_nat_mul(v___x_3983_, v_size_3977_);
v___x_3985_ = lean_nat_dec_lt(v_size_3978_, v___x_3984_);
lean_dec(v___x_3984_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4015_; 
lean_inc(v_r_3982_);
lean_inc(v_l_3981_);
lean_inc(v_v_3980_);
lean_inc(v_k_3979_);
v_isSharedCheck_4015_ = !lean_is_exclusive(v_r_3964_);
if (v_isSharedCheck_4015_ == 0)
{
lean_object* v_unused_4016_; lean_object* v_unused_4017_; lean_object* v_unused_4018_; lean_object* v_unused_4019_; lean_object* v_unused_4020_; 
v_unused_4016_ = lean_ctor_get(v_r_3964_, 4);
lean_dec(v_unused_4016_);
v_unused_4017_ = lean_ctor_get(v_r_3964_, 3);
lean_dec(v_unused_4017_);
v_unused_4018_ = lean_ctor_get(v_r_3964_, 2);
lean_dec(v_unused_4018_);
v_unused_4019_ = lean_ctor_get(v_r_3964_, 1);
lean_dec(v_unused_4019_);
v_unused_4020_ = lean_ctor_get(v_r_3964_, 0);
lean_dec(v_unused_4020_);
v___x_3987_ = v_r_3964_;
v_isShared_3988_ = v_isSharedCheck_4015_;
goto v_resetjp_3986_;
}
else
{
lean_dec(v_r_3964_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4015_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___x_4003_; lean_object* v___y_4005_; 
v___x_3989_ = lean_unsigned_to_nat(1u);
v___x_3990_ = lean_nat_add(v___x_3989_, v_size_3960_);
lean_dec(v_size_3960_);
v___x_3991_ = lean_nat_add(v___x_3990_, v_size_3959_);
lean_dec(v___x_3990_);
v___x_4003_ = lean_nat_add(v___x_3989_, v_size_3977_);
if (lean_obj_tag(v_l_3981_) == 0)
{
lean_object* v_size_4013_; 
v_size_4013_ = lean_ctor_get(v_l_3981_, 0);
lean_inc(v_size_4013_);
v___y_4005_ = v_size_4013_;
goto v___jp_4004_;
}
else
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_unsigned_to_nat(0u);
v___y_4005_ = v___x_4014_;
goto v___jp_4004_;
}
v___jp_3992_:
{
lean_object* v___x_3996_; lean_object* v___x_3998_; 
v___x_3996_ = lean_nat_add(v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec(v___y_3994_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 4, v_r_3776_);
lean_ctor_set(v___x_3987_, 3, v_r_3982_);
lean_ctor_set(v___x_3987_, 2, v_v_3774_);
lean_ctor_set(v___x_3987_, 1, v_k_3773_);
lean_ctor_set(v___x_3987_, 0, v___x_3996_);
v___x_3998_ = v___x_3987_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3996_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4002_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4002_, 3, v_r_3982_);
lean_ctor_set(v_reuseFailAlloc_4002_, 4, v_r_3776_);
v___x_3998_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_4000_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 4, v___x_3998_);
lean_ctor_set(v___x_3975_, 3, v___y_3993_);
lean_ctor_set(v___x_3975_, 2, v_v_3980_);
lean_ctor_set(v___x_3975_, 1, v_k_3979_);
lean_ctor_set(v___x_3975_, 0, v___x_3991_);
v___x_4000_ = v___x_3975_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_k_3979_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_v_3980_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v___y_3993_);
lean_ctor_set(v_reuseFailAlloc_4001_, 4, v___x_3998_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
v___jp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4008_; 
v___x_4006_ = lean_nat_add(v___x_4003_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec(v___x_4003_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_l_3981_);
lean_ctor_set(v___x_3778_, 3, v_l_3963_);
lean_ctor_set(v___x_3778_, 2, v_v_3962_);
lean_ctor_set(v___x_3778_, 1, v_k_3961_);
lean_ctor_set(v___x_3778_, 0, v___x_4006_);
v___x_4008_ = v___x_3778_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_k_3961_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_v_3962_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_l_3963_);
lean_ctor_set(v_reuseFailAlloc_4012_, 4, v_l_3981_);
v___x_4008_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4009_; 
v___x_4009_ = lean_nat_add(v___x_3989_, v_size_3959_);
if (lean_obj_tag(v_r_3982_) == 0)
{
lean_object* v_size_4010_; 
v_size_4010_ = lean_ctor_get(v_r_3982_, 0);
lean_inc(v_size_4010_);
v___y_3993_ = v___x_4008_;
v___y_3994_ = v___x_4009_;
v___y_3995_ = v_size_4010_;
goto v___jp_3992_;
}
else
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_unsigned_to_nat(0u);
v___y_3993_ = v___x_4008_;
v___y_3994_ = v___x_4009_;
v___y_3995_ = v___x_4011_;
goto v___jp_3992_;
}
}
}
}
}
else
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
lean_del_object(v___x_3778_);
v___x_4021_ = lean_unsigned_to_nat(1u);
v___x_4022_ = lean_nat_add(v___x_4021_, v_size_3960_);
lean_dec(v_size_3960_);
v___x_4023_ = lean_nat_add(v___x_4022_, v_size_3959_);
lean_dec(v___x_4022_);
v___x_4024_ = lean_nat_add(v___x_4021_, v_size_3959_);
v___x_4025_ = lean_nat_add(v___x_4024_, v_size_3978_);
lean_dec(v___x_4024_);
lean_inc_ref(v_r_3776_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 4, v_r_3776_);
lean_ctor_set(v___x_3975_, 3, v_r_3964_);
lean_ctor_set(v___x_3975_, 2, v_v_3774_);
lean_ctor_set(v___x_3975_, 1, v_k_3773_);
lean_ctor_set(v___x_3975_, 0, v___x_4025_);
v___x_4027_ = v___x_3975_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_r_3964_);
lean_ctor_set(v_reuseFailAlloc_4040_, 4, v_r_3776_);
v___x_4027_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
v_isSharedCheck_4034_ = !lean_is_exclusive(v_r_3776_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; lean_object* v_unused_4036_; lean_object* v_unused_4037_; lean_object* v_unused_4038_; lean_object* v_unused_4039_; 
v_unused_4035_ = lean_ctor_get(v_r_3776_, 4);
lean_dec(v_unused_4035_);
v_unused_4036_ = lean_ctor_get(v_r_3776_, 3);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_r_3776_, 2);
lean_dec(v_unused_4037_);
v_unused_4038_ = lean_ctor_get(v_r_3776_, 1);
lean_dec(v_unused_4038_);
v_unused_4039_ = lean_ctor_get(v_r_3776_, 0);
lean_dec(v_unused_4039_);
v___x_4029_ = v_r_3776_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v_r_3776_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 4, v___x_4027_);
lean_ctor_set(v___x_4029_, 3, v_l_3963_);
lean_ctor_set(v___x_4029_, 2, v_v_3962_);
lean_ctor_set(v___x_4029_, 1, v_k_3961_);
lean_ctor_set(v___x_4029_, 0, v___x_4023_);
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4023_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_k_3961_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_v_3962_);
lean_ctor_set(v_reuseFailAlloc_4033_, 3, v_l_3963_);
lean_ctor_set(v_reuseFailAlloc_4033_, 4, v___x_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_dec_ref(v_l_3963_);
lean_del_object(v___x_3975_);
lean_dec(v_v_3962_);
lean_dec(v_k_3961_);
lean_dec(v_size_3960_);
lean_dec_ref(v_r_3776_);
lean_del_object(v___x_3778_);
lean_dec(v_v_3774_);
lean_dec(v_k_3773_);
v___x_4041_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__7, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__7_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__7);
v___x_4042_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18___redArg(v___x_4041_);
return v___x_4042_;
}
}
else
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
lean_del_object(v___x_3975_);
lean_dec(v_r_3964_);
lean_dec(v_v_3962_);
lean_dec(v_k_3961_);
lean_dec(v_size_3960_);
lean_dec_ref(v_r_3776_);
lean_del_object(v___x_3778_);
lean_dec(v_v_3774_);
lean_dec(v_k_3773_);
v___x_4043_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__8, &l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg___closed__8);
v___x_4044_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18___redArg(v___x_4043_);
return v___x_4044_;
}
}
}
}
else
{
lean_object* v_size_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
v_size_4051_ = lean_ctor_get(v_r_3776_, 0);
v___x_4052_ = lean_unsigned_to_nat(1u);
v___x_4053_ = lean_nat_add(v___x_4052_, v_size_4051_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 3, v___x_3958_);
lean_ctor_set(v___x_3778_, 0, v___x_4053_);
v___x_4055_ = v___x_3778_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4056_, 3, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_4056_, 4, v_r_3776_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
else
{
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_l_4057_; 
v_l_4057_ = lean_ctor_get(v___x_3958_, 3);
lean_inc(v_l_4057_);
if (lean_obj_tag(v_l_4057_) == 0)
{
lean_object* v_r_4058_; 
v_r_4058_ = lean_ctor_get(v___x_3958_, 4);
lean_inc(v_r_4058_);
if (lean_obj_tag(v_r_4058_) == 0)
{
lean_object* v_size_4059_; lean_object* v_k_4060_; lean_object* v_v_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4075_; 
v_size_4059_ = lean_ctor_get(v___x_3958_, 0);
v_k_4060_ = lean_ctor_get(v___x_3958_, 1);
v_v_4061_ = lean_ctor_get(v___x_3958_, 2);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; lean_object* v_unused_4077_; 
v_unused_4076_ = lean_ctor_get(v___x_3958_, 4);
lean_dec(v_unused_4076_);
v_unused_4077_ = lean_ctor_get(v___x_3958_, 3);
lean_dec(v_unused_4077_);
v___x_4063_ = v___x_3958_;
v_isShared_4064_ = v_isSharedCheck_4075_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_v_4061_);
lean_inc(v_k_4060_);
lean_inc(v_size_4059_);
lean_dec(v___x_3958_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4075_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_size_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
v_size_4065_ = lean_ctor_get(v_r_4058_, 0);
v___x_4066_ = lean_unsigned_to_nat(1u);
v___x_4067_ = lean_nat_add(v___x_4066_, v_size_4059_);
lean_dec(v_size_4059_);
v___x_4068_ = lean_nat_add(v___x_4066_, v_size_4065_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 4, v_r_3776_);
lean_ctor_set(v___x_4063_, 3, v_r_4058_);
lean_ctor_set(v___x_4063_, 2, v_v_3774_);
lean_ctor_set(v___x_4063_, 1, v_k_3773_);
lean_ctor_set(v___x_4063_, 0, v___x_4068_);
v___x_4070_ = v___x_4063_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4074_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4074_, 3, v_r_4058_);
lean_ctor_set(v_reuseFailAlloc_4074_, 4, v_r_3776_);
v___x_4070_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4072_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_4070_);
lean_ctor_set(v___x_3778_, 3, v_l_4057_);
lean_ctor_set(v___x_3778_, 2, v_v_4061_);
lean_ctor_set(v___x_3778_, 1, v_k_4060_);
lean_ctor_set(v___x_3778_, 0, v___x_4067_);
v___x_4072_ = v___x_3778_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4073_, 1, v_k_4060_);
lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_v_4061_);
lean_ctor_set(v_reuseFailAlloc_4073_, 3, v_l_4057_);
lean_ctor_set(v_reuseFailAlloc_4073_, 4, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
else
{
lean_object* v_k_4078_; lean_object* v_v_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4091_; 
v_k_4078_ = lean_ctor_get(v___x_3958_, 1);
v_v_4079_ = lean_ctor_get(v___x_3958_, 2);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; lean_object* v_unused_4093_; lean_object* v_unused_4094_; 
v_unused_4092_ = lean_ctor_get(v___x_3958_, 4);
lean_dec(v_unused_4092_);
v_unused_4093_ = lean_ctor_get(v___x_3958_, 3);
lean_dec(v_unused_4093_);
v_unused_4094_ = lean_ctor_get(v___x_3958_, 0);
lean_dec(v_unused_4094_);
v___x_4081_ = v___x_3958_;
v_isShared_4082_ = v_isSharedCheck_4091_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_v_4079_);
lean_inc(v_k_4078_);
lean_dec(v___x_3958_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4091_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4086_; 
v___x_4083_ = lean_unsigned_to_nat(3u);
v___x_4084_ = lean_unsigned_to_nat(1u);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 3, v_r_4058_);
lean_ctor_set(v___x_4081_, 2, v_v_3774_);
lean_ctor_set(v___x_4081_, 1, v_k_3773_);
lean_ctor_set(v___x_4081_, 0, v___x_4084_);
v___x_4086_ = v___x_4081_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4090_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4090_, 3, v_r_4058_);
lean_ctor_set(v_reuseFailAlloc_4090_, 4, v_r_4058_);
v___x_4086_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_object* v___x_4088_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_4086_);
lean_ctor_set(v___x_3778_, 3, v_l_4057_);
lean_ctor_set(v___x_3778_, 2, v_v_4079_);
lean_ctor_set(v___x_3778_, 1, v_k_4078_);
lean_ctor_set(v___x_3778_, 0, v___x_4083_);
v___x_4088_ = v___x_3778_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_k_4078_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_v_4079_);
lean_ctor_set(v_reuseFailAlloc_4089_, 3, v_l_4057_);
lean_ctor_set(v_reuseFailAlloc_4089_, 4, v___x_4086_);
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
lean_object* v_r_4095_; 
v_r_4095_ = lean_ctor_get(v___x_3958_, 4);
lean_inc(v_r_4095_);
if (lean_obj_tag(v_r_4095_) == 0)
{
lean_object* v_k_4096_; lean_object* v_v_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4121_; 
v_k_4096_ = lean_ctor_get(v___x_3958_, 1);
v_v_4097_ = lean_ctor_get(v___x_3958_, 2);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; lean_object* v_unused_4123_; lean_object* v_unused_4124_; 
v_unused_4122_ = lean_ctor_get(v___x_3958_, 4);
lean_dec(v_unused_4122_);
v_unused_4123_ = lean_ctor_get(v___x_3958_, 3);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v___x_3958_, 0);
lean_dec(v_unused_4124_);
v___x_4099_ = v___x_3958_;
v_isShared_4100_ = v_isSharedCheck_4121_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_v_4097_);
lean_inc(v_k_4096_);
lean_dec(v___x_3958_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4121_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v_k_4101_; lean_object* v_v_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4117_; 
v_k_4101_ = lean_ctor_get(v_r_4095_, 1);
v_v_4102_ = lean_ctor_get(v_r_4095_, 2);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_r_4095_);
if (v_isSharedCheck_4117_ == 0)
{
lean_object* v_unused_4118_; lean_object* v_unused_4119_; lean_object* v_unused_4120_; 
v_unused_4118_ = lean_ctor_get(v_r_4095_, 4);
lean_dec(v_unused_4118_);
v_unused_4119_ = lean_ctor_get(v_r_4095_, 3);
lean_dec(v_unused_4119_);
v_unused_4120_ = lean_ctor_get(v_r_4095_, 0);
lean_dec(v_unused_4120_);
v___x_4104_ = v_r_4095_;
v_isShared_4105_ = v_isSharedCheck_4117_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_v_4102_);
lean_inc(v_k_4101_);
lean_dec(v_r_4095_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4117_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v___x_4106_ = lean_unsigned_to_nat(3u);
v___x_4107_ = lean_unsigned_to_nat(1u);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 4, v_l_4057_);
lean_ctor_set(v___x_4104_, 3, v_l_4057_);
lean_ctor_set(v___x_4104_, 2, v_v_4097_);
lean_ctor_set(v___x_4104_, 1, v_k_4096_);
lean_ctor_set(v___x_4104_, 0, v___x_4107_);
v___x_4109_ = v___x_4104_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4107_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_k_4096_);
lean_ctor_set(v_reuseFailAlloc_4116_, 2, v_v_4097_);
lean_ctor_set(v_reuseFailAlloc_4116_, 3, v_l_4057_);
lean_ctor_set(v_reuseFailAlloc_4116_, 4, v_l_4057_);
v___x_4109_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4111_; 
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 4, v_l_4057_);
lean_ctor_set(v___x_4099_, 2, v_v_3774_);
lean_ctor_set(v___x_4099_, 1, v_k_3773_);
lean_ctor_set(v___x_4099_, 0, v___x_4107_);
v___x_4111_ = v___x_4099_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4107_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4115_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4115_, 3, v_l_4057_);
lean_ctor_set(v_reuseFailAlloc_4115_, 4, v_l_4057_);
v___x_4111_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4113_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_4111_);
lean_ctor_set(v___x_3778_, 3, v___x_4109_);
lean_ctor_set(v___x_3778_, 2, v_v_4102_);
lean_ctor_set(v___x_3778_, 1, v_k_4101_);
lean_ctor_set(v___x_3778_, 0, v___x_4106_);
v___x_4113_ = v___x_3778_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4106_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_k_4101_);
lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_v_4102_);
lean_ctor_set(v_reuseFailAlloc_4114_, 3, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4114_, 4, v___x_4111_);
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
}
else
{
lean_object* v___x_4125_; lean_object* v___x_4127_; 
v___x_4125_ = lean_unsigned_to_nat(2u);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_r_4095_);
lean_ctor_set(v___x_3778_, 3, v___x_3958_);
lean_ctor_set(v___x_3778_, 0, v___x_4125_);
v___x_4127_ = v___x_3778_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4128_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4128_, 3, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_4128_, 4, v_r_4095_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4129_ = lean_unsigned_to_nat(1u);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3958_);
lean_ctor_set(v___x_3778_, 3, v___x_3958_);
lean_ctor_set(v___x_3778_, 0, v___x_4129_);
v___x_4131_ = v___x_3778_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_k_3773_);
lean_ctor_set(v_reuseFailAlloc_4132_, 2, v_v_3774_);
lean_ctor_set(v_reuseFailAlloc_4132_, 3, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_4132_, 4, v___x_3958_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_unsigned_to_nat(1u);
v___x_4135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
lean_ctor_set(v___x_4135_, 1, v_k_3769_);
lean_ctor_set(v___x_4135_, 2, v_v_3770_);
lean_ctor_set(v___x_4135_, 3, v_t_3771_);
lean_ctor_set(v___x_4135_, 4, v_t_3771_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__12_spec__20(lean_object* v_init_4136_, lean_object* v_x_4137_){
_start:
{
if (lean_obj_tag(v_x_4137_) == 0)
{
lean_object* v_k_4138_; lean_object* v_v_4139_; lean_object* v_l_4140_; lean_object* v_r_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v_k_4138_ = lean_ctor_get(v_x_4137_, 1);
lean_inc(v_k_4138_);
v_v_4139_ = lean_ctor_get(v_x_4137_, 2);
lean_inc(v_v_4139_);
v_l_4140_ = lean_ctor_get(v_x_4137_, 3);
lean_inc(v_l_4140_);
v_r_4141_ = lean_ctor_get(v_x_4137_, 4);
lean_inc(v_r_4141_);
lean_dec_ref(v_x_4137_);
v___x_4142_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__12_spec__20(v_init_4136_, v_l_4140_);
v___x_4143_ = 1;
v___x_4144_ = l_Lean_Name_toString(v_k_4138_, v___x_4143_);
v___x_4145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4145_, 0, v_v_4139_);
v___x_4146_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg(v___x_4144_, v___x_4145_, v___x_4142_);
v_init_4136_ = v___x_4146_;
v_x_4137_ = v_r_4141_;
goto _start;
}
else
{
return v_init_4136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(lean_object* v_m_4148_){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4149_ = lean_box(1);
v___x_4150_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__12_spec__20(v___x_4149_, v_m_4148_);
v___x_4151_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(lean_object* v___x_4154_, uint8_t v_updateToolchain_4155_, lean_object* v___x_4156_, size_t v_sz_4157_, size_t v_i_4158_, lean_object* v_bs_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
uint8_t v___x_4163_; 
v___x_4163_ = lean_usize_dec_lt(v_i_4158_, v_sz_4157_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_dec_ref(v___x_4156_);
lean_dec_ref(v___x_4154_);
v___x_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4164_, 0, v_bs_4159_);
lean_ctor_set(v___x_4164_, 1, v___y_4160_);
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
return v___x_4165_;
}
else
{
lean_object* v_baseName_4166_; lean_object* v_v_4167_; lean_object* v_name_4168_; lean_object* v_opts_4169_; uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v_baseName_4166_ = lean_ctor_get(v___x_4154_, 1);
v_v_4167_ = lean_array_uget_borrowed(v_bs_4159_, v_i_4158_);
v_name_4168_ = lean_ctor_get(v_v_4167_, 0);
v_opts_4169_ = lean_ctor_get(v_v_4167_, 4);
v___x_4170_ = 0;
lean_inc(v_baseName_4166_);
v___x_4171_ = l_Lean_Name_toString(v_baseName_4166_, v___x_4170_);
v___x_4172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__0));
v___x_4173_ = lean_string_append(v___x_4171_, v___x_4172_);
lean_inc(v_name_4168_);
v___x_4174_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4168_, v_updateToolchain_4155_);
v___x_4175_ = lean_string_append(v___x_4173_, v___x_4174_);
lean_dec_ref(v___x_4174_);
v___x_4176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___closed__1));
v___x_4177_ = lean_string_append(v___x_4175_, v___x_4176_);
lean_inc(v_opts_4169_);
v___x_4178_ = l_Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7(v_opts_4169_);
v___x_4179_ = lean_unsigned_to_nat(80u);
v___x_4180_ = l_Lean_Json_pretty(v___x_4178_, v___x_4179_);
v___x_4181_ = lean_string_append(v___x_4177_, v___x_4180_);
lean_dec_ref(v___x_4180_);
v___x_4182_ = 0;
v___x_4183_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4183_, 0, v___x_4181_);
lean_ctor_set_uint8(v___x_4183_, sizeof(void*)*1, v___x_4182_);
lean_inc_ref(v___y_4161_);
v___x_4184_ = lean_apply_2(v___y_4161_, v___x_4183_, lean_box(0));
lean_inc(v_v_4167_);
lean_inc_ref(v___x_4154_);
lean_inc_ref(v___x_4156_);
v___x_4185_ = l___private_Lake_Load_Resolve_0__Lake_updateAndMaterializeDep(v___x_4156_, v___x_4154_, v_v_4167_, v___y_4160_, v___y_4161_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v_fst_4187_; lean_object* v_snd_4188_; lean_object* v___x_4189_; lean_object* v_bs_x27_4190_; size_t v___x_4191_; size_t v___x_4192_; lean_object* v___x_4193_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref(v___x_4185_);
v_fst_4187_ = lean_ctor_get(v_a_4186_, 0);
lean_inc(v_fst_4187_);
v_snd_4188_ = lean_ctor_get(v_a_4186_, 1);
lean_inc(v_snd_4188_);
lean_dec(v_a_4186_);
v___x_4189_ = lean_unsigned_to_nat(0u);
v_bs_x27_4190_ = lean_array_uset(v_bs_4159_, v_i_4158_, v___x_4189_);
v___x_4191_ = ((size_t)1ULL);
v___x_4192_ = lean_usize_add(v_i_4158_, v___x_4191_);
v___x_4193_ = lean_array_uset(v_bs_x27_4190_, v_i_4158_, v_fst_4187_);
v_i_4158_ = v___x_4192_;
v_bs_4159_ = v___x_4193_;
v___y_4160_ = v_snd_4188_;
goto _start;
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec_ref(v_bs_4159_);
lean_dec_ref(v___x_4156_);
lean_dec_ref(v___x_4154_);
v_a_4195_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4185_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4185_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8___boxed(lean_object* v___x_4203_, lean_object* v_updateToolchain_4204_, lean_object* v___x_4205_, lean_object* v_sz_4206_, lean_object* v_i_4207_, lean_object* v_bs_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
uint8_t v_updateToolchain_boxed_4212_; size_t v_sz_boxed_4213_; size_t v_i_boxed_4214_; lean_object* v_res_4215_; 
v_updateToolchain_boxed_4212_ = lean_unbox(v_updateToolchain_4204_);
v_sz_boxed_4213_ = lean_unbox_usize(v_sz_4206_);
lean_dec(v_sz_4206_);
v_i_boxed_4214_ = lean_unbox_usize(v_i_4207_);
lean_dec(v_i_4207_);
v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v___x_4203_, v_updateToolchain_boxed_4212_, v___x_4205_, v_sz_boxed_4213_, v_i_boxed_4214_, v_bs_4208_, v___y_4209_, v___y_4210_);
lean_dec_ref(v___y_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13(lean_object* v_leanOpts_4216_, uint8_t v_updateToolchain_4217_, lean_object* v_as_4218_, size_t v_i_4219_, size_t v_stop_4220_, lean_object* v_b_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
uint8_t v___x_4228_; 
v___x_4228_ = lean_usize_dec_eq(v_i_4219_, v_stop_4220_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; lean_object* v_fst_4230_; lean_object* v_snd_4231_; lean_object* v_packages_4232_; lean_object* v_opts_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4229_ = lean_array_uget_borrowed(v_as_4218_, v_i_4219_);
v_fst_4230_ = lean_ctor_get(v___x_4229_, 0);
v_snd_4231_ = lean_ctor_get(v___x_4229_, 1);
v_packages_4232_ = lean_ctor_get(v_b_4221_, 5);
v_opts_4233_ = lean_ctor_get(v_fst_4230_, 4);
v___x_4234_ = lean_array_get_size(v_packages_4232_);
v___x_4235_ = lean_unsigned_to_nat(0u);
v___x_4236_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_4216_);
lean_inc(v_opts_4233_);
lean_inc(v_snd_4231_);
v___x_4237_ = l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(v___x_4234_, v_snd_4231_, v_opts_4233_, v_leanOpts_4216_, v_updateToolchain_4217_, v_b_4221_, v___x_4236_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v_a_4239_; lean_object* v_snd_4241_; lean_object* v___x_4259_; uint8_t v___x_4260_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
v_a_4239_ = lean_ctor_get(v___x_4237_, 1);
lean_inc(v_a_4239_);
lean_dec_ref(v___x_4237_);
v___x_4259_ = lean_array_get_size(v_a_4239_);
v___x_4260_ = lean_nat_dec_lt(v___x_4235_, v___x_4259_);
if (v___x_4260_ == 0)
{
lean_dec(v_a_4239_);
v_snd_4241_ = v___y_4222_;
goto v___jp_4240_;
}
else
{
lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4261_ = lean_box(0);
v___x_4262_ = lean_nat_dec_le(v___x_4259_, v___x_4259_);
if (v___x_4262_ == 0)
{
if (v___x_4260_ == 0)
{
lean_dec(v_a_4239_);
v_snd_4241_ = v___y_4222_;
goto v___jp_4240_;
}
else
{
size_t v___x_4263_; size_t v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = ((size_t)0ULL);
v___x_4264_ = lean_usize_of_nat(v___x_4259_);
v___x_4265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4239_, v___x_4263_, v___x_4264_, v___x_4261_, v___y_4223_);
lean_dec(v_a_4239_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_dec_ref(v___x_4265_);
v_snd_4241_ = v___y_4222_;
goto v___jp_4240_;
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v_a_4238_);
lean_dec(v___y_4222_);
lean_dec_ref(v_leanOpts_4216_);
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4265_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4265_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
}
else
{
size_t v___x_4274_; size_t v___x_4275_; lean_object* v___x_4276_; 
v___x_4274_ = ((size_t)0ULL);
v___x_4275_ = lean_usize_of_nat(v___x_4259_);
v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4239_, v___x_4274_, v___x_4275_, v___x_4261_, v___y_4223_);
lean_dec(v_a_4239_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_dec_ref(v___x_4276_);
v_snd_4241_ = v___y_4222_;
goto v___jp_4240_;
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_a_4238_);
lean_dec(v___y_4222_);
lean_dec_ref(v_leanOpts_4216_);
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4276_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4276_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
v___jp_4240_:
{
lean_object* v_fst_4242_; lean_object* v_snd_4243_; lean_object* v___x_4244_; 
v_fst_4242_ = lean_ctor_get(v_a_4238_, 0);
lean_inc(v_fst_4242_);
v_snd_4243_ = lean_ctor_get(v_a_4238_, 1);
lean_inc(v_snd_4243_);
lean_dec(v_a_4238_);
lean_inc(v_snd_4231_);
lean_inc(v_fst_4242_);
v___x_4244_ = l___private_Lake_Load_Resolve_0__Lake_addDependencyEntries(v_fst_4242_, v_snd_4231_, v_snd_4241_, v___y_4223_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v_snd_4246_; lean_object* v___x_4247_; size_t v___x_4248_; size_t v___x_4249_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref(v___x_4244_);
v_snd_4246_ = lean_ctor_get(v_a_4245_, 1);
lean_inc(v_snd_4246_);
lean_dec(v_a_4245_);
v___x_4247_ = l_Lake_Workspace_addPackage(v_fst_4242_, v_snd_4243_);
v___x_4248_ = ((size_t)1ULL);
v___x_4249_ = lean_usize_add(v_i_4219_, v___x_4248_);
v_i_4219_ = v___x_4249_;
v_b_4221_ = v___x_4247_;
v___y_4222_ = v_snd_4246_;
goto _start;
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec(v_snd_4243_);
lean_dec(v_fst_4242_);
lean_dec_ref(v_leanOpts_4216_);
v_a_4251_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4244_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4244_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; 
lean_dec(v___y_4222_);
lean_dec_ref(v_leanOpts_4216_);
v_a_4285_ = lean_ctor_get(v___x_4237_, 1);
lean_inc(v_a_4285_);
lean_dec_ref(v___x_4237_);
v___x_4286_ = lean_array_get_size(v_a_4285_);
v___x_4287_ = lean_nat_dec_lt(v___x_4235_, v___x_4286_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec(v_a_4285_);
v___x_4288_ = lean_box(0);
v___x_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
return v___x_4289_;
}
else
{
lean_object* v___x_4290_; uint8_t v___x_4291_; 
v___x_4290_ = lean_box(0);
v___x_4291_ = lean_nat_dec_le(v___x_4286_, v___x_4286_);
if (v___x_4291_ == 0)
{
if (v___x_4287_ == 0)
{
lean_dec(v_a_4285_);
goto v___jp_4225_;
}
else
{
size_t v___x_4292_; size_t v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = ((size_t)0ULL);
v___x_4293_ = lean_usize_of_nat(v___x_4286_);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4285_, v___x_4292_, v___x_4293_, v___x_4290_, v___y_4223_);
lean_dec(v_a_4285_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_dec_ref(v___x_4294_);
goto v___jp_4225_;
}
else
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4302_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4302_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4300_; 
if (v_isShared_4298_ == 0)
{
v___x_4300_ = v___x_4297_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
else
{
size_t v___x_4303_; size_t v___x_4304_; lean_object* v___x_4305_; 
v___x_4303_ = ((size_t)0ULL);
v___x_4304_ = lean_usize_of_nat(v___x_4286_);
v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_4285_, v___x_4303_, v___x_4304_, v___x_4290_, v___y_4223_);
lean_dec(v_a_4285_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_dec_ref(v___x_4305_);
goto v___jp_4225_;
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_dec_ref(v_leanOpts_4216_);
v___x_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4314_, 0, v_b_4221_);
lean_ctor_set(v___x_4314_, 1, v___y_4222_);
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
v___jp_4225_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_box(0);
v___x_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
return v___x_4227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13___boxed(lean_object* v_leanOpts_4316_, lean_object* v_updateToolchain_4317_, lean_object* v_as_4318_, lean_object* v_i_4319_, lean_object* v_stop_4320_, lean_object* v_b_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
uint8_t v_updateToolchain_boxed_4325_; size_t v_i_boxed_4326_; size_t v_stop_boxed_4327_; lean_object* v_res_4328_; 
v_updateToolchain_boxed_4325_ = lean_unbox(v_updateToolchain_4317_);
v_i_boxed_4326_ = lean_unbox_usize(v_i_4319_);
lean_dec(v_i_4319_);
v_stop_boxed_4327_ = lean_unbox_usize(v_stop_4320_);
lean_dec(v_stop_4320_);
v_res_4328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13(v_leanOpts_4316_, v_updateToolchain_boxed_4325_, v_as_4318_, v_i_boxed_4326_, v_stop_boxed_4327_, v_b_4321_, v___y_4322_, v___y_4323_);
lean_dec_ref(v___y_4323_);
lean_dec_ref(v_as_4318_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(lean_object* v_ws_4329_, lean_object* v_toUpdate_4330_, lean_object* v_leanOpts_4331_, uint8_t v_updateToolchain_4332_, lean_object* v_a_4333_){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_box(1);
lean_inc_ref(v_ws_4329_);
v___x_4336_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_a_4333_, v_ws_4329_, v_toUpdate_4330_, v___x_4335_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v_snd_4338_; lean_object* v_root_4339_; lean_object* v___x_4340_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref(v___x_4336_);
v_snd_4338_ = lean_ctor_get(v_a_4337_, 1);
lean_inc(v_snd_4338_);
lean_dec(v_a_4337_);
v_root_4339_ = lean_ctor_get(v_ws_4329_, 0);
lean_inc_ref(v_root_4339_);
v___x_4340_ = l_Lake_Workspace_addPackage(v_root_4339_, v_ws_4329_);
if (v_updateToolchain_4332_ == 0)
{
lean_object* v_root_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v_root_4341_ = lean_ctor_get(v___x_4340_, 0);
lean_inc_ref(v_root_4341_);
v___x_4342_ = lean_box(0);
v___x_4343_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_leanOpts_4331_, v___x_4340_, v_root_4341_, v___x_4342_, v_snd_4338_, v_a_4333_);
return v___x_4343_;
}
else
{
lean_object* v_root_4344_; lean_object* v_packages_4345_; lean_object* v___y_4347_; lean_object* v_fst_4348_; lean_object* v_snd_4349_; lean_object* v___y_4362_; lean_object* v_depConfigs_4366_; lean_object* v___x_4367_; size_t v_sz_4368_; size_t v___x_4369_; lean_object* v___x_4370_; 
v_root_4344_ = lean_ctor_get(v___x_4340_, 0);
lean_inc_ref(v_root_4344_);
v_packages_4345_ = lean_ctor_get(v___x_4340_, 5);
lean_inc_ref(v_packages_4345_);
v_depConfigs_4366_ = lean_ctor_get(v_root_4344_, 12);
lean_inc_ref(v_depConfigs_4366_);
v___x_4367_ = l_Array_reverse___redArg(v_depConfigs_4366_);
v_sz_4368_ = lean_array_size(v___x_4367_);
v___x_4369_ = ((size_t)0ULL);
lean_inc_ref(v___x_4367_);
lean_inc_ref(v___x_4340_);
v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_root_4344_, v_updateToolchain_4332_, v___x_4340_, v_sz_4368_, v___x_4369_, v___x_4367_, v_snd_4338_, v_a_4333_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v_fst_4372_; lean_object* v_snd_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4412_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref(v___x_4370_);
v_fst_4372_ = lean_ctor_get(v_a_4371_, 0);
v_snd_4373_ = lean_ctor_get(v_a_4371_, 1);
v_isSharedCheck_4412_ = !lean_is_exclusive(v_a_4371_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4375_ = v_a_4371_;
v_isShared_4376_ = v_isSharedCheck_4412_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_snd_4373_);
lean_inc(v_fst_4372_);
lean_dec(v_a_4371_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4412_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; 
lean_inc_ref(v___x_4340_);
v___x_4377_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__11(v_a_4333_, v___x_4340_, v_fst_4372_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4402_; 
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; 
v_unused_4403_ = lean_ctor_get(v___x_4377_, 0);
lean_dec(v_unused_4403_);
v___x_4379_ = v___x_4377_;
v_isShared_4380_ = v_isSharedCheck_4402_;
goto v_resetjp_4378_;
}
else
{
lean_dec(v___x_4377_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4402_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4381_ = l_Array_zip___redArg(v___x_4367_, v_fst_4372_);
lean_dec(v_fst_4372_);
lean_dec_ref(v___x_4367_);
v___x_4382_ = lean_unsigned_to_nat(0u);
v___x_4383_ = lean_array_get_size(v___x_4381_);
v___x_4384_ = lean_nat_dec_lt(v___x_4382_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4386_; 
lean_dec_ref(v___x_4381_);
lean_inc(v_snd_4373_);
lean_inc_ref(v___x_4340_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4340_);
v___x_4386_ = v___x_4375_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_snd_4373_);
v___x_4386_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
lean_object* v___x_4388_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4386_);
v___x_4388_ = v___x_4379_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
v___y_4347_ = v___x_4388_;
v_fst_4348_ = v___x_4340_;
v_snd_4349_ = v_snd_4373_;
goto v___jp_4346_;
}
}
}
else
{
uint8_t v___x_4391_; 
v___x_4391_ = lean_nat_dec_le(v___x_4383_, v___x_4383_);
if (v___x_4391_ == 0)
{
if (v___x_4384_ == 0)
{
lean_object* v___x_4393_; 
lean_dec_ref(v___x_4381_);
lean_inc(v_snd_4373_);
lean_inc_ref(v___x_4340_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4340_);
v___x_4393_ = v___x_4375_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_snd_4373_);
v___x_4393_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4395_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set(v___x_4379_, 0, v___x_4393_);
v___x_4395_ = v___x_4379_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
v___y_4347_ = v___x_4395_;
v_fst_4348_ = v___x_4340_;
v_snd_4349_ = v_snd_4373_;
goto v___jp_4346_;
}
}
}
else
{
size_t v___x_4398_; lean_object* v___x_4399_; 
lean_del_object(v___x_4379_);
lean_del_object(v___x_4375_);
v___x_4398_ = lean_usize_of_nat(v___x_4383_);
lean_inc_ref(v_leanOpts_4331_);
v___x_4399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13(v_leanOpts_4331_, v_updateToolchain_4332_, v___x_4381_, v___x_4369_, v___x_4398_, v___x_4340_, v_snd_4373_, v_a_4333_);
lean_dec_ref(v___x_4381_);
v___y_4362_ = v___x_4399_;
goto v___jp_4361_;
}
}
else
{
size_t v___x_4400_; lean_object* v___x_4401_; 
lean_del_object(v___x_4379_);
lean_del_object(v___x_4375_);
v___x_4400_ = lean_usize_of_nat(v___x_4383_);
lean_inc_ref(v_leanOpts_4331_);
v___x_4401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13(v_leanOpts_4331_, v_updateToolchain_4332_, v___x_4381_, v___x_4369_, v___x_4400_, v___x_4340_, v_snd_4373_, v_a_4333_);
lean_dec_ref(v___x_4381_);
v___y_4362_ = v___x_4401_;
goto v___jp_4361_;
}
}
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_del_object(v___x_4375_);
lean_dec(v_snd_4373_);
lean_dec(v_fst_4372_);
lean_dec_ref(v___x_4367_);
lean_dec_ref(v_packages_4345_);
lean_dec_ref(v___x_4340_);
lean_dec_ref(v_leanOpts_4331_);
v_a_4404_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4377_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4377_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec_ref(v___x_4367_);
lean_dec_ref(v_packages_4345_);
lean_dec_ref(v___x_4340_);
lean_dec_ref(v_leanOpts_4331_);
v_a_4413_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4370_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4370_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
v___jp_4346_:
{
lean_object* v_packages_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v_packages_4350_ = lean_ctor_get(v_fst_4348_, 5);
lean_inc_ref(v_packages_4350_);
v___x_4351_ = lean_array_get_size(v_packages_4345_);
lean_dec_ref(v_packages_4345_);
v___x_4352_ = lean_array_get_size(v_packages_4350_);
v___x_4353_ = lean_nat_dec_lt(v___x_4351_, v___x_4352_);
if (v___x_4353_ == 0)
{
lean_dec_ref(v_packages_4350_);
lean_dec(v_snd_4349_);
lean_dec_ref(v_fst_4348_);
lean_dec_ref(v_leanOpts_4331_);
return v___y_4347_;
}
else
{
uint8_t v___x_4354_; 
v___x_4354_ = lean_nat_dec_le(v___x_4352_, v___x_4352_);
if (v___x_4354_ == 0)
{
if (v___x_4353_ == 0)
{
lean_dec_ref(v_packages_4350_);
lean_dec(v_snd_4349_);
lean_dec_ref(v_fst_4348_);
lean_dec_ref(v_leanOpts_4331_);
return v___y_4347_;
}
else
{
size_t v___x_4355_; size_t v___x_4356_; lean_object* v___x_4357_; 
lean_dec_ref(v___y_4347_);
v___x_4355_ = lean_usize_of_nat(v___x_4351_);
v___x_4356_ = lean_usize_of_nat(v___x_4352_);
v___x_4357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12(v_leanOpts_4331_, v_updateToolchain_4332_, v_packages_4350_, v___x_4355_, v___x_4356_, v_fst_4348_, v_snd_4349_, v_a_4333_);
lean_dec_ref(v_packages_4350_);
return v___x_4357_;
}
}
else
{
size_t v___x_4358_; size_t v___x_4359_; lean_object* v___x_4360_; 
lean_dec_ref(v___y_4347_);
v___x_4358_ = lean_usize_of_nat(v___x_4351_);
v___x_4359_ = lean_usize_of_nat(v___x_4352_);
v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12(v_leanOpts_4331_, v_updateToolchain_4332_, v_packages_4350_, v___x_4358_, v___x_4359_, v_fst_4348_, v_snd_4349_, v_a_4333_);
lean_dec_ref(v_packages_4350_);
return v___x_4360_;
}
}
}
v___jp_4361_:
{
if (lean_obj_tag(v___y_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v_fst_4364_; lean_object* v_snd_4365_; 
v_a_4363_ = lean_ctor_get(v___y_4362_, 0);
v_fst_4364_ = lean_ctor_get(v_a_4363_, 0);
lean_inc(v_fst_4364_);
v_snd_4365_ = lean_ctor_get(v_a_4363_, 1);
lean_inc(v_snd_4365_);
v___y_4347_ = v___y_4362_;
v_fst_4348_ = v_fst_4364_;
v_snd_4349_ = v_snd_4365_;
goto v___jp_4346_;
}
else
{
lean_dec_ref(v_packages_4345_);
lean_dec_ref(v_leanOpts_4331_);
return v___y_4362_;
}
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec_ref(v_leanOpts_4331_);
lean_dec_ref(v_ws_4329_);
v_a_4421_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4336_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4336_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___boxed(lean_object* v_ws_4429_, lean_object* v_toUpdate_4430_, lean_object* v_leanOpts_4431_, lean_object* v_updateToolchain_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
uint8_t v_updateToolchain_boxed_4435_; lean_object* v_res_4436_; 
v_updateToolchain_boxed_4435_ = lean_unbox(v_updateToolchain_4432_);
v_res_4436_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore(v_ws_4429_, v_toUpdate_4430_, v_leanOpts_4431_, v_updateToolchain_boxed_4435_, v_a_4433_);
lean_dec_ref(v_a_4433_);
lean_dec(v_toUpdate_4430_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(lean_object* v___y_4437_, lean_object* v_as_4438_, size_t v_i_4439_, size_t v_stop_4440_, lean_object* v_b_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
uint8_t v___x_4447_; 
v___x_4447_ = lean_usize_dec_eq(v_i_4439_, v_stop_4440_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = lean_array_uget_borrowed(v_as_4438_, v_i_4439_);
lean_inc_ref(v___y_4437_);
lean_inc_ref(v___y_4445_);
lean_inc(v___y_4442_);
lean_inc(v___x_4448_);
v___x_4449_ = lean_apply_6(v___y_4437_, v___x_4448_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, lean_box(0));
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v_fst_4451_; lean_object* v_snd_4452_; lean_object* v_fst_4453_; lean_object* v_snd_4454_; size_t v___x_4455_; size_t v___x_4456_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref(v___x_4449_);
v_fst_4451_ = lean_ctor_get(v_a_4450_, 0);
lean_inc(v_fst_4451_);
v_snd_4452_ = lean_ctor_get(v_a_4450_, 1);
lean_inc(v_snd_4452_);
lean_dec(v_a_4450_);
v_fst_4453_ = lean_ctor_get(v_fst_4451_, 0);
lean_inc(v_fst_4453_);
v_snd_4454_ = lean_ctor_get(v_fst_4451_, 1);
lean_inc(v_snd_4454_);
lean_dec(v_fst_4451_);
v___x_4455_ = ((size_t)1ULL);
v___x_4456_ = lean_usize_add(v_i_4439_, v___x_4455_);
v_i_4439_ = v___x_4456_;
v_b_4441_ = v_fst_4453_;
v___y_4443_ = v_snd_4454_;
v___y_4444_ = v_snd_4452_;
goto _start;
}
else
{
lean_dec_ref(v___y_4437_);
return v___x_4449_;
}
}
else
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
lean_dec_ref(v___y_4437_);
v___x_4458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4458_, 0, v_b_4441_);
lean_ctor_set(v___x_4458_, 1, v___y_4443_);
v___x_4459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
lean_ctor_set(v___x_4459_, 1, v___y_4444_);
v___x_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
return v___x_4460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6___boxed(lean_object* v___y_4461_, lean_object* v_as_4462_, lean_object* v_i_4463_, lean_object* v_stop_4464_, lean_object* v_b_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
size_t v_i_boxed_4471_; size_t v_stop_boxed_4472_; lean_object* v_res_4473_; 
v_i_boxed_4471_ = lean_unbox_usize(v_i_4463_);
lean_dec(v_i_4463_);
v_stop_boxed_4472_ = lean_unbox_usize(v_stop_4464_);
lean_dec(v_stop_4464_);
v_res_4473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4461_, v_as_4462_, v_i_boxed_4471_, v_stop_boxed_4472_, v_b_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4466_);
lean_dec_ref(v_as_4462_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(lean_object* v_leanOpts_4474_, lean_object* v___y_4475_, lean_object* v_pkg_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v_packages_4482_; lean_object* v_depConfigs_4483_; lean_object* v___x_4484_; lean_object* v_snd_4486_; lean_object* v_packages_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v_____x_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v_packages_4482_ = lean_ctor_get(v_a_4478_, 5);
v_depConfigs_4483_ = lean_ctor_get(v_pkg_4476_, 12);
lean_inc_ref(v_depConfigs_4483_);
v___x_4484_ = lean_array_get_size(v_packages_4482_);
v___x_4512_ = lean_array_get_size(v_depConfigs_4483_);
v___x_4513_ = lean_unsigned_to_nat(0u);
v___x_4514_ = lean_box(0);
v___x_4515_ = lean_nat_dec_le(v___x_4512_, v___x_4512_);
if (v___x_4515_ == 0)
{
uint8_t v___x_4516_; 
v___x_4516_ = lean_nat_dec_lt(v___x_4513_, v___x_4512_);
if (v___x_4516_ == 0)
{
uint8_t v___x_4517_; 
lean_dec_ref(v_depConfigs_4483_);
lean_dec_ref(v_pkg_4476_);
lean_dec_ref(v_leanOpts_4474_);
v___x_4517_ = lean_nat_dec_lt(v___x_4484_, v___x_4484_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
lean_dec_ref(v___y_4475_);
v___x_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4514_);
lean_ctor_set(v___x_4518_, 1, v_a_4478_);
v___x_4519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4518_);
lean_ctor_set(v___x_4519_, 1, v___y_4479_);
v___x_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
return v___x_4520_;
}
else
{
uint8_t v___x_4521_; 
v___x_4521_ = lean_nat_dec_le(v___x_4484_, v___x_4484_);
if (v___x_4521_ == 0)
{
if (v___x_4517_ == 0)
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
lean_dec_ref(v___y_4475_);
v___x_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4514_);
lean_ctor_set(v___x_4522_, 1, v_a_4478_);
v___x_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
lean_ctor_set(v___x_4523_, 1, v___y_4479_);
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
return v___x_4524_;
}
else
{
size_t v___x_4525_; lean_object* v___x_4526_; 
lean_inc_ref(v_packages_4482_);
v___x_4525_ = lean_usize_of_nat(v___x_4484_);
v___x_4526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4475_, v_packages_4482_, v___x_4525_, v___x_4525_, v___x_4514_, v_a_4477_, v_a_4478_, v___y_4479_, v___y_4480_);
lean_dec_ref(v_packages_4482_);
return v___x_4526_;
}
}
else
{
size_t v___x_4527_; lean_object* v___x_4528_; 
lean_inc_ref(v_packages_4482_);
v___x_4527_ = lean_usize_of_nat(v___x_4484_);
v___x_4528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4475_, v_packages_4482_, v___x_4527_, v___x_4527_, v___x_4514_, v_a_4477_, v_a_4478_, v___y_4479_, v___y_4480_);
lean_dec_ref(v_packages_4482_);
return v___x_4528_;
}
}
}
else
{
size_t v___x_4529_; size_t v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = lean_usize_of_nat(v___x_4512_);
v___x_4530_ = ((size_t)0ULL);
v___x_4531_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_4476_, v_leanOpts_4474_, v_depConfigs_4483_, v___x_4529_, v___x_4530_, v___x_4514_, v_a_4478_, v___y_4479_, v___y_4480_);
lean_dec_ref(v_depConfigs_4483_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v_fst_4533_; lean_object* v_snd_4534_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref(v___x_4531_);
v_fst_4533_ = lean_ctor_get(v_a_4532_, 0);
lean_inc(v_fst_4533_);
v_snd_4534_ = lean_ctor_get(v_a_4532_, 1);
lean_inc(v_snd_4534_);
lean_dec(v_a_4532_);
v_____x_4507_ = v_fst_4533_;
v___y_4508_ = v_snd_4534_;
v___y_4509_ = v___y_4480_;
goto v___jp_4506_;
}
else
{
lean_dec_ref(v___y_4475_);
return v___x_4531_;
}
}
}
else
{
uint8_t v___x_4535_; 
v___x_4535_ = lean_nat_dec_lt(v___x_4513_, v___x_4512_);
if (v___x_4535_ == 0)
{
lean_inc_ref(v_packages_4482_);
lean_dec_ref(v_depConfigs_4483_);
lean_dec_ref(v_pkg_4476_);
lean_dec_ref(v_leanOpts_4474_);
v_snd_4486_ = v_a_4478_;
v_packages_4487_ = v_packages_4482_;
v___y_4488_ = v___y_4479_;
v___y_4489_ = v___y_4480_;
goto v___jp_4485_;
}
else
{
size_t v___x_4536_; size_t v___x_4537_; lean_object* v___x_4538_; 
v___x_4536_ = lean_usize_of_nat(v___x_4512_);
v___x_4537_ = ((size_t)0ULL);
v___x_4538_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_4476_, v_leanOpts_4474_, v_depConfigs_4483_, v___x_4536_, v___x_4537_, v___x_4514_, v_a_4478_, v___y_4479_, v___y_4480_);
lean_dec_ref(v_depConfigs_4483_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v_fst_4540_; lean_object* v_snd_4541_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref(v___x_4538_);
v_fst_4540_ = lean_ctor_get(v_a_4539_, 0);
lean_inc(v_fst_4540_);
v_snd_4541_ = lean_ctor_get(v_a_4539_, 1);
lean_inc(v_snd_4541_);
lean_dec(v_a_4539_);
v_____x_4507_ = v_fst_4540_;
v___y_4508_ = v_snd_4541_;
v___y_4509_ = v___y_4480_;
goto v___jp_4506_;
}
else
{
lean_dec_ref(v___y_4475_);
return v___x_4538_;
}
}
}
v___jp_4485_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; uint8_t v___x_4492_; 
v___x_4490_ = lean_array_get_size(v_packages_4487_);
v___x_4491_ = lean_box(0);
v___x_4492_ = lean_nat_dec_lt(v___x_4484_, v___x_4490_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
lean_dec_ref(v_packages_4487_);
lean_dec_ref(v___y_4475_);
v___x_4493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4491_);
lean_ctor_set(v___x_4493_, 1, v_snd_4486_);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
lean_ctor_set(v___x_4494_, 1, v___y_4488_);
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
else
{
uint8_t v___x_4496_; 
v___x_4496_ = lean_nat_dec_le(v___x_4490_, v___x_4490_);
if (v___x_4496_ == 0)
{
if (v___x_4492_ == 0)
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; 
lean_dec_ref(v_packages_4487_);
lean_dec_ref(v___y_4475_);
v___x_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4491_);
lean_ctor_set(v___x_4497_, 1, v_snd_4486_);
v___x_4498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
lean_ctor_set(v___x_4498_, 1, v___y_4488_);
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
else
{
size_t v___x_4500_; size_t v___x_4501_; lean_object* v___x_4502_; 
v___x_4500_ = lean_usize_of_nat(v___x_4484_);
v___x_4501_ = lean_usize_of_nat(v___x_4490_);
v___x_4502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4475_, v_packages_4487_, v___x_4500_, v___x_4501_, v___x_4491_, v_a_4477_, v_snd_4486_, v___y_4488_, v___y_4489_);
lean_dec_ref(v_packages_4487_);
return v___x_4502_;
}
}
else
{
size_t v___x_4503_; size_t v___x_4504_; lean_object* v___x_4505_; 
v___x_4503_ = lean_usize_of_nat(v___x_4484_);
v___x_4504_ = lean_usize_of_nat(v___x_4490_);
v___x_4505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4475_, v_packages_4487_, v___x_4503_, v___x_4504_, v___x_4491_, v_a_4477_, v_snd_4486_, v___y_4488_, v___y_4489_);
lean_dec_ref(v_packages_4487_);
return v___x_4505_;
}
}
}
v___jp_4506_:
{
lean_object* v_snd_4510_; lean_object* v_packages_4511_; 
v_snd_4510_ = lean_ctor_get(v_____x_4507_, 1);
lean_inc(v_snd_4510_);
lean_dec_ref(v_____x_4507_);
v_packages_4511_ = lean_ctor_get(v_snd_4510_, 5);
lean_inc_ref(v_packages_4511_);
v_snd_4486_ = v_snd_4510_;
v_packages_4487_ = v_packages_4511_;
v___y_4488_ = v___y_4508_;
v___y_4489_ = v___y_4509_;
goto v___jp_4485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___boxed(lean_object* v_leanOpts_4542_, lean_object* v___y_4543_, lean_object* v_pkg_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5(v_leanOpts_4542_, v___y_4543_, v_pkg_4544_, v_a_4545_, v_a_4546_, v___y_4547_, v___y_4548_);
lean_dec_ref(v___y_4548_);
lean_dec(v_a_4545_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(lean_object* v_leanOpts_4551_, uint8_t v_updateToolchain_4552_, lean_object* v___y_4553_, lean_object* v_pkg_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_packages_4560_; lean_object* v_depConfigs_4561_; lean_object* v___x_4562_; lean_object* v_snd_4564_; lean_object* v_packages_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v_____x_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; uint8_t v___x_4593_; 
v_packages_4560_ = lean_ctor_get(v_a_4556_, 5);
v_depConfigs_4561_ = lean_ctor_get(v_pkg_4554_, 12);
lean_inc_ref(v_depConfigs_4561_);
v___x_4562_ = lean_array_get_size(v_packages_4560_);
v___x_4590_ = lean_array_get_size(v_depConfigs_4561_);
v___x_4591_ = lean_unsigned_to_nat(0u);
v___x_4592_ = lean_box(0);
v___x_4593_ = lean_nat_dec_le(v___x_4590_, v___x_4590_);
if (v___x_4593_ == 0)
{
uint8_t v___x_4594_; 
v___x_4594_ = lean_nat_dec_lt(v___x_4591_, v___x_4590_);
if (v___x_4594_ == 0)
{
uint8_t v___x_4595_; 
lean_dec_ref(v_depConfigs_4561_);
lean_dec_ref(v_pkg_4554_);
lean_dec_ref(v_leanOpts_4551_);
v___x_4595_ = lean_nat_dec_lt(v___x_4562_, v___x_4562_);
if (v___x_4595_ == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
lean_dec_ref(v___y_4553_);
v___x_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4592_);
lean_ctor_set(v___x_4596_, 1, v_a_4556_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
lean_ctor_set(v___x_4597_, 1, v___y_4557_);
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4597_);
return v___x_4598_;
}
else
{
uint8_t v___x_4599_; 
v___x_4599_ = lean_nat_dec_le(v___x_4562_, v___x_4562_);
if (v___x_4599_ == 0)
{
if (v___x_4595_ == 0)
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
lean_dec_ref(v___y_4553_);
v___x_4600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4592_);
lean_ctor_set(v___x_4600_, 1, v_a_4556_);
v___x_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
lean_ctor_set(v___x_4601_, 1, v___y_4557_);
v___x_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
return v___x_4602_;
}
else
{
size_t v___x_4603_; lean_object* v___x_4604_; 
lean_inc_ref(v_packages_4560_);
v___x_4603_ = lean_usize_of_nat(v___x_4562_);
v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4553_, v_packages_4560_, v___x_4603_, v___x_4603_, v___x_4592_, v_a_4555_, v_a_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v_packages_4560_);
return v___x_4604_;
}
}
else
{
size_t v___x_4605_; lean_object* v___x_4606_; 
lean_inc_ref(v_packages_4560_);
v___x_4605_ = lean_usize_of_nat(v___x_4562_);
v___x_4606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4553_, v_packages_4560_, v___x_4605_, v___x_4605_, v___x_4592_, v_a_4555_, v_a_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v_packages_4560_);
return v___x_4606_;
}
}
}
else
{
size_t v___x_4607_; size_t v___x_4608_; lean_object* v___x_4609_; 
v___x_4607_ = lean_usize_of_nat(v___x_4590_);
v___x_4608_ = ((size_t)0ULL);
v___x_4609_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_4554_, v_leanOpts_4551_, v_updateToolchain_4552_, v_depConfigs_4561_, v___x_4607_, v___x_4608_, v___x_4592_, v_a_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v_depConfigs_4561_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v_fst_4611_; lean_object* v_snd_4612_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
lean_inc(v_a_4610_);
lean_dec_ref(v___x_4609_);
v_fst_4611_ = lean_ctor_get(v_a_4610_, 0);
lean_inc(v_fst_4611_);
v_snd_4612_ = lean_ctor_get(v_a_4610_, 1);
lean_inc(v_snd_4612_);
lean_dec(v_a_4610_);
v_____x_4585_ = v_fst_4611_;
v___y_4586_ = v_snd_4612_;
v___y_4587_ = v___y_4558_;
goto v___jp_4584_;
}
else
{
lean_dec_ref(v___y_4553_);
return v___x_4609_;
}
}
}
else
{
uint8_t v___x_4613_; 
v___x_4613_ = lean_nat_dec_lt(v___x_4591_, v___x_4590_);
if (v___x_4613_ == 0)
{
lean_inc_ref(v_packages_4560_);
lean_dec_ref(v_depConfigs_4561_);
lean_dec_ref(v_pkg_4554_);
lean_dec_ref(v_leanOpts_4551_);
v_snd_4564_ = v_a_4556_;
v_packages_4565_ = v_packages_4560_;
v___y_4566_ = v___y_4557_;
v___y_4567_ = v___y_4558_;
goto v___jp_4563_;
}
else
{
size_t v___x_4614_; size_t v___x_4615_; lean_object* v___x_4616_; 
v___x_4614_ = lean_usize_of_nat(v___x_4590_);
v___x_4615_ = ((size_t)0ULL);
v___x_4616_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_4554_, v_leanOpts_4551_, v_updateToolchain_4552_, v_depConfigs_4561_, v___x_4614_, v___x_4615_, v___x_4592_, v_a_4556_, v___y_4557_, v___y_4558_);
lean_dec_ref(v_depConfigs_4561_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v_fst_4618_; lean_object* v_snd_4619_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_a_4617_);
lean_dec_ref(v___x_4616_);
v_fst_4618_ = lean_ctor_get(v_a_4617_, 0);
lean_inc(v_fst_4618_);
v_snd_4619_ = lean_ctor_get(v_a_4617_, 1);
lean_inc(v_snd_4619_);
lean_dec(v_a_4617_);
v_____x_4585_ = v_fst_4618_;
v___y_4586_ = v_snd_4619_;
v___y_4587_ = v___y_4558_;
goto v___jp_4584_;
}
else
{
lean_dec_ref(v___y_4553_);
return v___x_4616_;
}
}
}
v___jp_4563_:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; 
v___x_4568_ = lean_array_get_size(v_packages_4565_);
v___x_4569_ = lean_box(0);
v___x_4570_ = lean_nat_dec_lt(v___x_4562_, v___x_4568_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
lean_dec_ref(v_packages_4565_);
lean_dec_ref(v___y_4553_);
v___x_4571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set(v___x_4571_, 1, v_snd_4564_);
v___x_4572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
lean_ctor_set(v___x_4572_, 1, v___y_4566_);
v___x_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
return v___x_4573_;
}
else
{
uint8_t v___x_4574_; 
v___x_4574_ = lean_nat_dec_le(v___x_4568_, v___x_4568_);
if (v___x_4574_ == 0)
{
if (v___x_4570_ == 0)
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
lean_dec_ref(v_packages_4565_);
lean_dec_ref(v___y_4553_);
v___x_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4569_);
lean_ctor_set(v___x_4575_, 1, v_snd_4564_);
v___x_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4575_);
lean_ctor_set(v___x_4576_, 1, v___y_4566_);
v___x_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
return v___x_4577_;
}
else
{
size_t v___x_4578_; size_t v___x_4579_; lean_object* v___x_4580_; 
v___x_4578_ = lean_usize_of_nat(v___x_4562_);
v___x_4579_ = lean_usize_of_nat(v___x_4568_);
v___x_4580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4553_, v_packages_4565_, v___x_4578_, v___x_4579_, v___x_4569_, v_a_4555_, v_snd_4564_, v___y_4566_, v___y_4567_);
lean_dec_ref(v_packages_4565_);
return v___x_4580_;
}
}
else
{
size_t v___x_4581_; size_t v___x_4582_; lean_object* v___x_4583_; 
v___x_4581_ = lean_usize_of_nat(v___x_4562_);
v___x_4582_ = lean_usize_of_nat(v___x_4568_);
v___x_4583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__6(v___y_4553_, v_packages_4565_, v___x_4581_, v___x_4582_, v___x_4569_, v_a_4555_, v_snd_4564_, v___y_4566_, v___y_4567_);
lean_dec_ref(v_packages_4565_);
return v___x_4583_;
}
}
}
v___jp_4584_:
{
lean_object* v_snd_4588_; lean_object* v_packages_4589_; 
v_snd_4588_ = lean_ctor_get(v_____x_4585_, 1);
lean_inc(v_snd_4588_);
lean_dec_ref(v_____x_4585_);
v_packages_4589_ = lean_ctor_get(v_snd_4588_, 5);
lean_inc_ref(v_packages_4589_);
v_snd_4564_ = v_snd_4588_;
v_packages_4565_ = v_packages_4589_;
v___y_4566_ = v___y_4586_;
v___y_4567_ = v___y_4587_;
goto v___jp_4563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___boxed(lean_object* v_leanOpts_4620_, lean_object* v_updateToolchain_4621_, lean_object* v___y_4622_, lean_object* v_pkg_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
uint8_t v_updateToolchain_boxed_4629_; lean_object* v_res_4630_; 
v_updateToolchain_boxed_4629_ = lean_unbox(v_updateToolchain_4621_);
v_res_4630_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9(v_leanOpts_4620_, v_updateToolchain_boxed_4629_, v___y_4622_, v_pkg_4623_, v_a_4624_, v_a_4625_, v___y_4626_, v___y_4627_);
lean_dec_ref(v___y_4627_);
lean_dec(v_a_4624_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(lean_object* v_pkg_4631_, lean_object* v_leanOpts_4632_, lean_object* v_as_4633_, size_t v_i_4634_, size_t v_stop_4635_, lean_object* v_b_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_4631_, v_leanOpts_4632_, v_as_4633_, v_i_4634_, v_stop_4635_, v_b_4636_, v___y_4638_, v___y_4639_, v___y_4640_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___boxed(lean_object* v_pkg_4643_, lean_object* v_leanOpts_4644_, lean_object* v_as_4645_, lean_object* v_i_4646_, lean_object* v_stop_4647_, lean_object* v_b_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
size_t v_i_boxed_4654_; size_t v_stop_boxed_4655_; lean_object* v_res_4656_; 
v_i_boxed_4654_ = lean_unbox_usize(v_i_4646_);
lean_dec(v_i_4646_);
v_stop_boxed_4655_ = lean_unbox_usize(v_stop_4647_);
lean_dec(v_stop_4647_);
v_res_4656_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7(v_pkg_4643_, v_leanOpts_4644_, v_as_4645_, v_i_boxed_4654_, v_stop_boxed_4655_, v_b_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4649_);
lean_dec_ref(v_as_4645_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9(lean_object* v_leanOpts_4657_, lean_object* v_a_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg(v_leanOpts_4657_, v_a_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9___boxed(lean_object* v_leanOpts_4665_, lean_object* v_a_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9(v_leanOpts_4665_, v_a_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4667_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18(lean_object* v_00_u03b2_4673_, lean_object* v_msg_4674_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11_spec__18___redArg(v_msg_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11(lean_object* v_00_u03b2_4676_, lean_object* v_k_4677_, lean_object* v_v_4678_, lean_object* v_t_4679_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__11___redArg(v_k_4677_, v_v_4678_, v_t_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__12(lean_object* v_init_4681_, lean_object* v_t_4682_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__7_spec__12_spec__20(v_init_4681_, v_t_4682_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15(lean_object* v_pkg_4684_, lean_object* v_leanOpts_4685_, uint8_t v_updateToolchain_4686_, lean_object* v_as_4687_, size_t v_i_4688_, size_t v_stop_4689_, lean_object* v_b_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v___x_4696_; 
v___x_4696_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_4684_, v_leanOpts_4685_, v_updateToolchain_4686_, v_as_4687_, v_i_4688_, v_stop_4689_, v_b_4690_, v___y_4692_, v___y_4693_, v___y_4694_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___boxed(lean_object* v_pkg_4697_, lean_object* v_leanOpts_4698_, lean_object* v_updateToolchain_4699_, lean_object* v_as_4700_, lean_object* v_i_4701_, lean_object* v_stop_4702_, lean_object* v_b_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
uint8_t v_updateToolchain_boxed_4709_; size_t v_i_boxed_4710_; size_t v_stop_boxed_4711_; lean_object* v_res_4712_; 
v_updateToolchain_boxed_4709_ = lean_unbox(v_updateToolchain_4699_);
v_i_boxed_4710_ = lean_unbox_usize(v_i_4701_);
lean_dec(v_i_4701_);
v_stop_boxed_4711_ = lean_unbox_usize(v_stop_4702_);
lean_dec(v_stop_4702_);
v_res_4712_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15(v_pkg_4697_, v_leanOpts_4698_, v_updateToolchain_boxed_4709_, v_as_4700_, v_i_boxed_4710_, v_stop_boxed_4711_, v_b_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4704_);
lean_dec_ref(v_as_4700_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17(lean_object* v_leanOpts_4713_, uint8_t v_updateToolchain_4714_, lean_object* v_a_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg(v_leanOpts_4713_, v_updateToolchain_4714_, v_a_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17___boxed(lean_object* v_leanOpts_4722_, lean_object* v_updateToolchain_4723_, lean_object* v_a_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
uint8_t v_updateToolchain_boxed_4730_; lean_object* v_res_4731_; 
v_updateToolchain_boxed_4730_ = lean_unbox(v_updateToolchain_4723_);
v_res_4731_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17(v_leanOpts_4722_, v_updateToolchain_boxed_4730_, v_a_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4725_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(lean_object* v___y_4732_, lean_object* v___x_4733_, lean_object* v_as_4734_, size_t v_i_4735_, size_t v_stop_4736_, lean_object* v_b_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_){
_start:
{
uint8_t v___x_4742_; 
v___x_4742_ = lean_usize_dec_eq(v_i_4735_, v_stop_4736_);
if (v___x_4742_ == 0)
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = lean_array_uget_borrowed(v_as_4734_, v_i_4735_);
lean_inc_ref(v___y_4732_);
lean_inc_ref(v___y_4740_);
lean_inc(v___x_4733_);
lean_inc(v___x_4743_);
v___x_4744_ = lean_apply_6(v___y_4732_, v___x_4743_, v___x_4733_, v___y_4738_, v___y_4739_, v___y_4740_, lean_box(0));
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v_fst_4746_; lean_object* v_snd_4747_; lean_object* v_fst_4748_; lean_object* v_snd_4749_; size_t v___x_4750_; size_t v___x_4751_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref(v___x_4744_);
v_fst_4746_ = lean_ctor_get(v_a_4745_, 0);
lean_inc(v_fst_4746_);
v_snd_4747_ = lean_ctor_get(v_a_4745_, 1);
lean_inc(v_snd_4747_);
lean_dec(v_a_4745_);
v_fst_4748_ = lean_ctor_get(v_fst_4746_, 0);
lean_inc(v_fst_4748_);
v_snd_4749_ = lean_ctor_get(v_fst_4746_, 1);
lean_inc(v_snd_4749_);
lean_dec(v_fst_4746_);
v___x_4750_ = ((size_t)1ULL);
v___x_4751_ = lean_usize_add(v_i_4735_, v___x_4750_);
v_i_4735_ = v___x_4751_;
v_b_4737_ = v_fst_4748_;
v___y_4738_ = v_snd_4749_;
v___y_4739_ = v_snd_4747_;
goto _start;
}
else
{
lean_dec(v___x_4733_);
lean_dec_ref(v___y_4732_);
return v___x_4744_;
}
}
else
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
lean_dec(v___x_4733_);
lean_dec_ref(v___y_4732_);
v___x_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4753_, 0, v_b_4737_);
lean_ctor_set(v___x_4753_, 1, v___y_4738_);
v___x_4754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
lean_ctor_set(v___x_4754_, 1, v___y_4739_);
v___x_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
return v___x_4755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg___boxed(lean_object* v___y_4756_, lean_object* v___x_4757_, lean_object* v_as_4758_, lean_object* v_i_4759_, lean_object* v_stop_4760_, lean_object* v_b_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
size_t v_i_boxed_4766_; size_t v_stop_boxed_4767_; lean_object* v_res_4768_; 
v_i_boxed_4766_ = lean_unbox_usize(v_i_4759_);
lean_dec(v_i_4759_);
v_stop_boxed_4767_ = lean_unbox_usize(v_stop_4760_);
lean_dec(v_stop_4760_);
v_res_4768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4756_, v___x_4757_, v_as_4758_, v_i_boxed_4766_, v_stop_boxed_4767_, v_b_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec_ref(v___y_4764_);
lean_dec_ref(v_as_4758_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12(lean_object* v___y_4769_, lean_object* v___x_4770_, lean_object* v_leanOpts_4771_, lean_object* v_pkg_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v_packages_4778_; lean_object* v_depConfigs_4779_; lean_object* v___x_4780_; lean_object* v_snd_4782_; lean_object* v_packages_4783_; lean_object* v___y_4784_; lean_object* v___y_4785_; lean_object* v_____x_4803_; lean_object* v___y_4804_; lean_object* v___y_4805_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; 
v_packages_4778_ = lean_ctor_get(v_a_4774_, 5);
v_depConfigs_4779_ = lean_ctor_get(v_pkg_4772_, 12);
lean_inc_ref(v_depConfigs_4779_);
v___x_4780_ = lean_array_get_size(v_packages_4778_);
v___x_4808_ = lean_array_get_size(v_depConfigs_4779_);
v___x_4809_ = lean_unsigned_to_nat(0u);
v___x_4810_ = lean_box(0);
v___x_4811_ = lean_nat_dec_le(v___x_4808_, v___x_4808_);
if (v___x_4811_ == 0)
{
uint8_t v___x_4812_; 
v___x_4812_ = lean_nat_dec_lt(v___x_4809_, v___x_4808_);
if (v___x_4812_ == 0)
{
uint8_t v___x_4813_; 
lean_dec_ref(v_depConfigs_4779_);
lean_dec_ref(v_pkg_4772_);
lean_dec_ref(v_leanOpts_4771_);
v___x_4813_ = lean_nat_dec_lt(v___x_4780_, v___x_4780_);
if (v___x_4813_ == 0)
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
lean_dec(v___x_4770_);
lean_dec_ref(v___y_4769_);
v___x_4814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4810_);
lean_ctor_set(v___x_4814_, 1, v_a_4774_);
v___x_4815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
lean_ctor_set(v___x_4815_, 1, v___y_4775_);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
else
{
uint8_t v___x_4817_; 
v___x_4817_ = lean_nat_dec_le(v___x_4780_, v___x_4780_);
if (v___x_4817_ == 0)
{
if (v___x_4813_ == 0)
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
lean_dec(v___x_4770_);
lean_dec_ref(v___y_4769_);
v___x_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4810_);
lean_ctor_set(v___x_4818_, 1, v_a_4774_);
v___x_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
lean_ctor_set(v___x_4819_, 1, v___y_4775_);
v___x_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
return v___x_4820_;
}
else
{
size_t v___x_4821_; lean_object* v___x_4822_; 
lean_inc_ref(v_packages_4778_);
v___x_4821_ = lean_usize_of_nat(v___x_4780_);
v___x_4822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4769_, v___x_4770_, v_packages_4778_, v___x_4821_, v___x_4821_, v___x_4810_, v_a_4774_, v___y_4775_, v___y_4776_);
lean_dec_ref(v_packages_4778_);
return v___x_4822_;
}
}
else
{
size_t v___x_4823_; lean_object* v___x_4824_; 
lean_inc_ref(v_packages_4778_);
v___x_4823_ = lean_usize_of_nat(v___x_4780_);
v___x_4824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4769_, v___x_4770_, v_packages_4778_, v___x_4823_, v___x_4823_, v___x_4810_, v_a_4774_, v___y_4775_, v___y_4776_);
lean_dec_ref(v_packages_4778_);
return v___x_4824_;
}
}
}
else
{
size_t v___x_4825_; size_t v___x_4826_; lean_object* v___x_4827_; 
v___x_4825_ = lean_usize_of_nat(v___x_4808_);
v___x_4826_ = ((size_t)0ULL);
v___x_4827_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_4772_, v_leanOpts_4771_, v_depConfigs_4779_, v___x_4825_, v___x_4826_, v___x_4810_, v_a_4774_, v___y_4775_, v___y_4776_);
lean_dec_ref(v_depConfigs_4779_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v_fst_4829_; lean_object* v_snd_4830_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref(v___x_4827_);
v_fst_4829_ = lean_ctor_get(v_a_4828_, 0);
lean_inc(v_fst_4829_);
v_snd_4830_ = lean_ctor_get(v_a_4828_, 1);
lean_inc(v_snd_4830_);
lean_dec(v_a_4828_);
v_____x_4803_ = v_fst_4829_;
v___y_4804_ = v_snd_4830_;
v___y_4805_ = v___y_4776_;
goto v___jp_4802_;
}
else
{
lean_dec(v___x_4770_);
lean_dec_ref(v___y_4769_);
return v___x_4827_;
}
}
}
else
{
uint8_t v___x_4831_; 
v___x_4831_ = lean_nat_dec_lt(v___x_4809_, v___x_4808_);
if (v___x_4831_ == 0)
{
lean_inc_ref(v_packages_4778_);
lean_dec_ref(v_depConfigs_4779_);
lean_dec_ref(v_pkg_4772_);
lean_dec_ref(v_leanOpts_4771_);
v_snd_4782_ = v_a_4774_;
v_packages_4783_ = v_packages_4778_;
v___y_4784_ = v___y_4775_;
v___y_4785_ = v___y_4776_;
goto v___jp_4781_;
}
else
{
size_t v___x_4832_; size_t v___x_4833_; lean_object* v___x_4834_; 
v___x_4832_ = lean_usize_of_nat(v___x_4808_);
v___x_4833_ = ((size_t)0ULL);
v___x_4834_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__7___redArg(v_pkg_4772_, v_leanOpts_4771_, v_depConfigs_4779_, v___x_4832_, v___x_4833_, v___x_4810_, v_a_4774_, v___y_4775_, v___y_4776_);
lean_dec_ref(v_depConfigs_4779_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v_a_4835_; lean_object* v_fst_4836_; lean_object* v_snd_4837_; 
v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
lean_inc(v_a_4835_);
lean_dec_ref(v___x_4834_);
v_fst_4836_ = lean_ctor_get(v_a_4835_, 0);
lean_inc(v_fst_4836_);
v_snd_4837_ = lean_ctor_get(v_a_4835_, 1);
lean_inc(v_snd_4837_);
lean_dec(v_a_4835_);
v_____x_4803_ = v_fst_4836_;
v___y_4804_ = v_snd_4837_;
v___y_4805_ = v___y_4776_;
goto v___jp_4802_;
}
else
{
lean_dec(v___x_4770_);
lean_dec_ref(v___y_4769_);
return v___x_4834_;
}
}
}
v___jp_4781_:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4786_ = lean_array_get_size(v_packages_4783_);
v___x_4787_ = lean_box(0);
v___x_4788_ = lean_nat_dec_lt(v___x_4780_, v___x_4786_);
if (v___x_4788_ == 0)
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
lean_dec_ref(v_packages_4783_);
lean_dec(v___x_4770_);
lean_dec_ref(v___y_4769_);
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4787_);
lean_ctor_set(v___x_4789_, 1, v_snd_4782_);
v___x_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4789_);
lean_ctor_set(v___x_4790_, 1, v___y_4784_);
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
return v___x_4791_;
}
else
{
uint8_t v___x_4792_; 
v___x_4792_ = lean_nat_dec_le(v___x_4786_, v___x_4786_);
if (v___x_4792_ == 0)
{
if (v___x_4788_ == 0)
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
lean_dec_ref(v_packages_4783_);
lean_dec(v___x_4770_);
lean_dec_ref(v___y_4769_);
v___x_4793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4787_);
lean_ctor_set(v___x_4793_, 1, v_snd_4782_);
v___x_4794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4793_);
lean_ctor_set(v___x_4794_, 1, v___y_4784_);
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
return v___x_4795_;
}
else
{
size_t v___x_4796_; size_t v___x_4797_; lean_object* v___x_4798_; 
v___x_4796_ = lean_usize_of_nat(v___x_4780_);
v___x_4797_ = lean_usize_of_nat(v___x_4786_);
v___x_4798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4769_, v___x_4770_, v_packages_4783_, v___x_4796_, v___x_4797_, v___x_4787_, v_snd_4782_, v___y_4784_, v___y_4785_);
lean_dec_ref(v_packages_4783_);
return v___x_4798_;
}
}
else
{
size_t v___x_4799_; size_t v___x_4800_; lean_object* v___x_4801_; 
v___x_4799_ = lean_usize_of_nat(v___x_4780_);
v___x_4800_ = lean_usize_of_nat(v___x_4786_);
v___x_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4769_, v___x_4770_, v_packages_4783_, v___x_4799_, v___x_4800_, v___x_4787_, v_snd_4782_, v___y_4784_, v___y_4785_);
lean_dec_ref(v_packages_4783_);
return v___x_4801_;
}
}
}
v___jp_4802_:
{
lean_object* v_snd_4806_; lean_object* v_packages_4807_; 
v_snd_4806_ = lean_ctor_get(v_____x_4803_, 1);
lean_inc(v_snd_4806_);
lean_dec_ref(v_____x_4803_);
v_packages_4807_ = lean_ctor_get(v_snd_4806_, 5);
lean_inc_ref(v_packages_4807_);
v_snd_4782_ = v_snd_4806_;
v_packages_4783_ = v_packages_4807_;
v___y_4784_ = v___y_4804_;
v___y_4785_ = v___y_4805_;
goto v___jp_4781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___boxed(lean_object* v___y_4838_, lean_object* v___x_4839_, lean_object* v_leanOpts_4840_, lean_object* v_pkg_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12(v___y_4838_, v___x_4839_, v_leanOpts_4840_, v_pkg_4841_, v_a_4842_, v_a_4843_, v___y_4844_, v___y_4845_);
lean_dec_ref(v___y_4845_);
lean_dec(v_a_4842_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14(lean_object* v_00_u03b1_4848_, lean_object* v_cycle_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___redArg(v_cycle_4849_, v___y_4853_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14___boxed(lean_object* v_00_u03b1_4856_, lean_object* v_cycle_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14(v_00_u03b1_4856_, v_cycle_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec(v___y_4858_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26(lean_object* v___y_4864_, lean_object* v___x_4865_, lean_object* v_leanOpts_4866_, uint8_t v_updateToolchain_4867_, lean_object* v_pkg_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v_packages_4874_; lean_object* v_depConfigs_4875_; lean_object* v___x_4876_; lean_object* v_snd_4878_; lean_object* v_packages_4879_; lean_object* v___y_4880_; lean_object* v___y_4881_; lean_object* v_____x_4899_; lean_object* v___y_4900_; lean_object* v___y_4901_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; uint8_t v___x_4907_; 
v_packages_4874_ = lean_ctor_get(v_a_4870_, 5);
v_depConfigs_4875_ = lean_ctor_get(v_pkg_4868_, 12);
lean_inc_ref(v_depConfigs_4875_);
v___x_4876_ = lean_array_get_size(v_packages_4874_);
v___x_4904_ = lean_array_get_size(v_depConfigs_4875_);
v___x_4905_ = lean_unsigned_to_nat(0u);
v___x_4906_ = lean_box(0);
v___x_4907_ = lean_nat_dec_le(v___x_4904_, v___x_4904_);
if (v___x_4907_ == 0)
{
uint8_t v___x_4908_; 
v___x_4908_ = lean_nat_dec_lt(v___x_4905_, v___x_4904_);
if (v___x_4908_ == 0)
{
uint8_t v___x_4909_; 
lean_dec_ref(v_depConfigs_4875_);
lean_dec_ref(v_pkg_4868_);
lean_dec_ref(v_leanOpts_4866_);
v___x_4909_ = lean_nat_dec_lt(v___x_4876_, v___x_4876_);
if (v___x_4909_ == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
lean_dec(v___x_4865_);
lean_dec_ref(v___y_4864_);
v___x_4910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4906_);
lean_ctor_set(v___x_4910_, 1, v_a_4870_);
v___x_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
lean_ctor_set(v___x_4911_, 1, v___y_4871_);
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4911_);
return v___x_4912_;
}
else
{
uint8_t v___x_4913_; 
v___x_4913_ = lean_nat_dec_le(v___x_4876_, v___x_4876_);
if (v___x_4913_ == 0)
{
if (v___x_4909_ == 0)
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
lean_dec(v___x_4865_);
lean_dec_ref(v___y_4864_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4906_);
lean_ctor_set(v___x_4914_, 1, v_a_4870_);
v___x_4915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
lean_ctor_set(v___x_4915_, 1, v___y_4871_);
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4915_);
return v___x_4916_;
}
else
{
size_t v___x_4917_; lean_object* v___x_4918_; 
lean_inc_ref(v_packages_4874_);
v___x_4917_ = lean_usize_of_nat(v___x_4876_);
v___x_4918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4864_, v___x_4865_, v_packages_4874_, v___x_4917_, v___x_4917_, v___x_4906_, v_a_4870_, v___y_4871_, v___y_4872_);
lean_dec_ref(v_packages_4874_);
return v___x_4918_;
}
}
else
{
size_t v___x_4919_; lean_object* v___x_4920_; 
lean_inc_ref(v_packages_4874_);
v___x_4919_ = lean_usize_of_nat(v___x_4876_);
v___x_4920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4864_, v___x_4865_, v_packages_4874_, v___x_4919_, v___x_4919_, v___x_4906_, v_a_4870_, v___y_4871_, v___y_4872_);
lean_dec_ref(v_packages_4874_);
return v___x_4920_;
}
}
}
else
{
size_t v___x_4921_; size_t v___x_4922_; lean_object* v___x_4923_; 
v___x_4921_ = lean_usize_of_nat(v___x_4904_);
v___x_4922_ = ((size_t)0ULL);
v___x_4923_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_4868_, v_leanOpts_4866_, v_updateToolchain_4867_, v_depConfigs_4875_, v___x_4921_, v___x_4922_, v___x_4906_, v_a_4870_, v___y_4871_, v___y_4872_);
lean_dec_ref(v_depConfigs_4875_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v_fst_4925_; lean_object* v_snd_4926_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref(v___x_4923_);
v_fst_4925_ = lean_ctor_get(v_a_4924_, 0);
lean_inc(v_fst_4925_);
v_snd_4926_ = lean_ctor_get(v_a_4924_, 1);
lean_inc(v_snd_4926_);
lean_dec(v_a_4924_);
v_____x_4899_ = v_fst_4925_;
v___y_4900_ = v_snd_4926_;
v___y_4901_ = v___y_4872_;
goto v___jp_4898_;
}
else
{
lean_dec(v___x_4865_);
lean_dec_ref(v___y_4864_);
return v___x_4923_;
}
}
}
else
{
uint8_t v___x_4927_; 
v___x_4927_ = lean_nat_dec_lt(v___x_4905_, v___x_4904_);
if (v___x_4927_ == 0)
{
lean_inc_ref(v_packages_4874_);
lean_dec_ref(v_depConfigs_4875_);
lean_dec_ref(v_pkg_4868_);
lean_dec_ref(v_leanOpts_4866_);
v_snd_4878_ = v_a_4870_;
v_packages_4879_ = v_packages_4874_;
v___y_4880_ = v___y_4871_;
v___y_4881_ = v___y_4872_;
goto v___jp_4877_;
}
else
{
size_t v___x_4928_; size_t v___x_4929_; lean_object* v___x_4930_; 
v___x_4928_ = lean_usize_of_nat(v___x_4904_);
v___x_4929_ = ((size_t)0ULL);
v___x_4930_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9_spec__15___redArg(v_pkg_4868_, v_leanOpts_4866_, v_updateToolchain_4867_, v_depConfigs_4875_, v___x_4928_, v___x_4929_, v___x_4906_, v_a_4870_, v___y_4871_, v___y_4872_);
lean_dec_ref(v_depConfigs_4875_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v_fst_4932_; lean_object* v_snd_4933_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref(v___x_4930_);
v_fst_4932_ = lean_ctor_get(v_a_4931_, 0);
lean_inc(v_fst_4932_);
v_snd_4933_ = lean_ctor_get(v_a_4931_, 1);
lean_inc(v_snd_4933_);
lean_dec(v_a_4931_);
v_____x_4899_ = v_fst_4932_;
v___y_4900_ = v_snd_4933_;
v___y_4901_ = v___y_4872_;
goto v___jp_4898_;
}
else
{
lean_dec(v___x_4865_);
lean_dec_ref(v___y_4864_);
return v___x_4930_;
}
}
}
v___jp_4877_:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4882_ = lean_array_get_size(v_packages_4879_);
v___x_4883_ = lean_box(0);
v___x_4884_ = lean_nat_dec_lt(v___x_4876_, v___x_4882_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
lean_dec_ref(v_packages_4879_);
lean_dec(v___x_4865_);
lean_dec_ref(v___y_4864_);
v___x_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4883_);
lean_ctor_set(v___x_4885_, 1, v_snd_4878_);
v___x_4886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4885_);
lean_ctor_set(v___x_4886_, 1, v___y_4880_);
v___x_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
return v___x_4887_;
}
else
{
uint8_t v___x_4888_; 
v___x_4888_ = lean_nat_dec_le(v___x_4882_, v___x_4882_);
if (v___x_4888_ == 0)
{
if (v___x_4884_ == 0)
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
lean_dec_ref(v_packages_4879_);
lean_dec(v___x_4865_);
lean_dec_ref(v___y_4864_);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4883_);
lean_ctor_set(v___x_4889_, 1, v_snd_4878_);
v___x_4890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
lean_ctor_set(v___x_4890_, 1, v___y_4880_);
v___x_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
return v___x_4891_;
}
else
{
size_t v___x_4892_; size_t v___x_4893_; lean_object* v___x_4894_; 
v___x_4892_ = lean_usize_of_nat(v___x_4876_);
v___x_4893_ = lean_usize_of_nat(v___x_4882_);
v___x_4894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4864_, v___x_4865_, v_packages_4879_, v___x_4892_, v___x_4893_, v___x_4883_, v_snd_4878_, v___y_4880_, v___y_4881_);
lean_dec_ref(v_packages_4879_);
return v___x_4894_;
}
}
else
{
size_t v___x_4895_; size_t v___x_4896_; lean_object* v___x_4897_; 
v___x_4895_ = lean_usize_of_nat(v___x_4876_);
v___x_4896_ = lean_usize_of_nat(v___x_4882_);
v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4864_, v___x_4865_, v_packages_4879_, v___x_4895_, v___x_4896_, v___x_4883_, v_snd_4878_, v___y_4880_, v___y_4881_);
lean_dec_ref(v_packages_4879_);
return v___x_4897_;
}
}
}
v___jp_4898_:
{
lean_object* v_snd_4902_; lean_object* v_packages_4903_; 
v_snd_4902_ = lean_ctor_get(v_____x_4899_, 1);
lean_inc(v_snd_4902_);
lean_dec_ref(v_____x_4899_);
v_packages_4903_ = lean_ctor_get(v_snd_4902_, 5);
lean_inc_ref(v_packages_4903_);
v_snd_4878_ = v_snd_4902_;
v_packages_4879_ = v_packages_4903_;
v___y_4880_ = v___y_4900_;
v___y_4881_ = v___y_4901_;
goto v___jp_4877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___boxed(lean_object* v___y_4934_, lean_object* v___x_4935_, lean_object* v_leanOpts_4936_, lean_object* v_updateToolchain_4937_, lean_object* v_pkg_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
uint8_t v_updateToolchain_boxed_4944_; lean_object* v_res_4945_; 
v_updateToolchain_boxed_4944_ = lean_unbox(v_updateToolchain_4937_);
v_res_4945_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26(v___y_4934_, v___x_4935_, v_leanOpts_4936_, v_updateToolchain_boxed_4944_, v_pkg_4938_, v_a_4939_, v_a_4940_, v___y_4941_, v___y_4942_);
lean_dec_ref(v___y_4942_);
lean_dec(v_a_4939_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19(lean_object* v___y_4946_, lean_object* v___x_4947_, lean_object* v_as_4948_, size_t v_i_4949_, size_t v_stop_4950_, lean_object* v_b_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___redArg(v___y_4946_, v___x_4947_, v_as_4948_, v_i_4949_, v_stop_4950_, v_b_4951_, v___y_4953_, v___y_4954_, v___y_4955_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19___boxed(lean_object* v___y_4958_, lean_object* v___x_4959_, lean_object* v_as_4960_, lean_object* v_i_4961_, lean_object* v_stop_4962_, lean_object* v_b_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
size_t v_i_boxed_4969_; size_t v_stop_boxed_4970_; lean_object* v_res_4971_; 
v_i_boxed_4969_ = lean_unbox_usize(v_i_4961_);
lean_dec(v_i_4961_);
v_stop_boxed_4970_ = lean_unbox_usize(v_stop_4962_);
lean_dec(v_stop_4962_);
v_res_4971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12_spec__19(v___y_4958_, v___x_4959_, v_as_4960_, v_i_boxed_4969_, v_stop_boxed_4970_, v_b_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4964_);
lean_dec_ref(v_as_4960_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15(lean_object* v_leanOpts_4972_, lean_object* v_inst_4973_, lean_object* v_a_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___redArg(v_leanOpts_4972_, v_a_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15___boxed(lean_object* v_leanOpts_4981_, lean_object* v_inst_4982_, lean_object* v_a_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15(v_leanOpts_4981_, v_inst_4982_, v_a_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
lean_dec_ref(v___y_4987_);
lean_dec(v___y_4984_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27(lean_object* v_leanOpts_4990_, uint8_t v_updateToolchain_4991_, lean_object* v_inst_4992_, lean_object* v_a_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg(v_leanOpts_4990_, v_updateToolchain_4991_, v_a_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___boxed(lean_object* v_leanOpts_5000_, lean_object* v_updateToolchain_5001_, lean_object* v_inst_5002_, lean_object* v_a_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_){
_start:
{
uint8_t v_updateToolchain_boxed_5009_; lean_object* v_res_5010_; 
v_updateToolchain_boxed_5009_ = lean_unbox(v_updateToolchain_5001_);
v_res_5010_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27(v_leanOpts_5000_, v_updateToolchain_boxed_5009_, v_inst_5002_, v_a_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_);
lean_dec_ref(v___y_5007_);
lean_dec(v___y_5004_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33(lean_object* v_leanOpts_5011_, lean_object* v___x_5012_, lean_object* v_as_5013_, size_t v_i_5014_, size_t v_stop_5015_, lean_object* v_b_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___redArg(v_leanOpts_5011_, v___x_5012_, v_as_5013_, v_i_5014_, v_stop_5015_, v_b_5016_, v___y_5018_, v___y_5019_, v___y_5020_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33___boxed(lean_object* v_leanOpts_5023_, lean_object* v___x_5024_, lean_object* v_as_5025_, lean_object* v_i_5026_, lean_object* v_stop_5027_, lean_object* v_b_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
size_t v_i_boxed_5034_; size_t v_stop_boxed_5035_; lean_object* v_res_5036_; 
v_i_boxed_5034_ = lean_unbox_usize(v_i_5026_);
lean_dec(v_i_5026_);
v_stop_boxed_5035_ = lean_unbox_usize(v_stop_5027_);
lean_dec(v_stop_5027_);
v_res_5036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__12___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__15_spec__31_spec__33(v_leanOpts_5023_, v___x_5024_, v_as_5025_, v_i_boxed_5034_, v_stop_boxed_5035_, v_b_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec_ref(v___y_5032_);
lean_dec(v___y_5029_);
lean_dec_ref(v_as_5025_);
lean_dec(v___x_5024_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36(lean_object* v_leanOpts_5037_, uint8_t v_updateToolchain_5038_, lean_object* v___x_5039_, lean_object* v_as_5040_, size_t v_i_5041_, size_t v_stop_5042_, lean_object* v_b_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v___x_5049_; 
v___x_5049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___redArg(v_leanOpts_5037_, v_updateToolchain_5038_, v___x_5039_, v_as_5040_, v_i_5041_, v_stop_5042_, v_b_5043_, v___y_5045_, v___y_5046_, v___y_5047_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36___boxed(lean_object* v_leanOpts_5050_, lean_object* v_updateToolchain_5051_, lean_object* v___x_5052_, lean_object* v_as_5053_, lean_object* v_i_5054_, lean_object* v_stop_5055_, lean_object* v_b_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
uint8_t v_updateToolchain_boxed_5062_; size_t v_i_boxed_5063_; size_t v_stop_boxed_5064_; lean_object* v_res_5065_; 
v_updateToolchain_boxed_5062_ = lean_unbox(v_updateToolchain_5051_);
v_i_boxed_5063_ = lean_unbox_usize(v_i_5054_);
lean_dec(v_i_5054_);
v_stop_boxed_5064_ = lean_unbox_usize(v_stop_5055_);
lean_dec(v_stop_5055_);
v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__9___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__26___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27_spec__35_spec__36(v_leanOpts_5050_, v_updateToolchain_boxed_5062_, v___x_5052_, v_as_5053_, v_i_boxed_5063_, v_stop_boxed_5064_, v_b_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5057_);
lean_dec_ref(v_as_5053_);
lean_dec(v___x_5052_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(lean_object* v_entries_5066_, lean_object* v_as_5067_, size_t v_i_5068_, size_t v_stop_5069_, lean_object* v_b_5070_){
_start:
{
lean_object* v___y_5072_; uint8_t v___x_5076_; 
v___x_5076_ = lean_usize_dec_eq(v_i_5068_, v_stop_5069_);
if (v___x_5076_ == 0)
{
lean_object* v___x_5077_; lean_object* v_baseName_5078_; lean_object* v_relConfigFile_5079_; lean_object* v_relManifestFile_5080_; lean_object* v___x_5081_; 
v___x_5077_ = lean_array_uget_borrowed(v_as_5067_, v_i_5068_);
v_baseName_5078_ = lean_ctor_get(v___x_5077_, 1);
v_relConfigFile_5079_ = lean_ctor_get(v___x_5077_, 8);
v_relManifestFile_5080_ = lean_ctor_get(v___x_5077_, 9);
v___x_5081_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_5066_, v_baseName_5078_);
if (lean_obj_tag(v___x_5081_) == 0)
{
v___y_5072_ = v_b_5070_;
goto v___jp_5071_;
}
else
{
lean_object* v_val_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5103_; 
v_val_5082_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5084_ = v___x_5081_;
v_isShared_5085_ = v_isSharedCheck_5103_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_val_5082_);
lean_dec(v___x_5081_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5103_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v_name_5086_; lean_object* v_scope_5087_; uint8_t v_inherited_5088_; lean_object* v_src_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5100_; 
v_name_5086_ = lean_ctor_get(v_val_5082_, 0);
v_scope_5087_ = lean_ctor_get(v_val_5082_, 1);
v_inherited_5088_ = lean_ctor_get_uint8(v_val_5082_, sizeof(void*)*5);
v_src_5089_ = lean_ctor_get(v_val_5082_, 4);
v_isSharedCheck_5100_ = !lean_is_exclusive(v_val_5082_);
if (v_isSharedCheck_5100_ == 0)
{
lean_object* v_unused_5101_; lean_object* v_unused_5102_; 
v_unused_5101_ = lean_ctor_get(v_val_5082_, 3);
lean_dec(v_unused_5101_);
v_unused_5102_ = lean_ctor_get(v_val_5082_, 2);
lean_dec(v_unused_5102_);
v___x_5091_ = v_val_5082_;
v_isShared_5092_ = v_isSharedCheck_5100_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_src_5089_);
lean_inc(v_scope_5087_);
lean_inc(v_name_5086_);
lean_dec(v_val_5082_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5100_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
lean_inc_ref(v_relManifestFile_5080_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 0, v_relManifestFile_5080_);
v___x_5094_ = v___x_5084_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_relManifestFile_5080_);
v___x_5094_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5096_; 
lean_inc_ref(v_relConfigFile_5079_);
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 3, v___x_5094_);
lean_ctor_set(v___x_5091_, 2, v_relConfigFile_5079_);
v___x_5096_ = v___x_5091_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_name_5086_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v_scope_5087_);
lean_ctor_set(v_reuseFailAlloc_5098_, 2, v_relConfigFile_5079_);
lean_ctor_set(v_reuseFailAlloc_5098_, 3, v___x_5094_);
lean_ctor_set(v_reuseFailAlloc_5098_, 4, v_src_5089_);
lean_ctor_set_uint8(v_reuseFailAlloc_5098_, sizeof(void*)*5, v_inherited_5088_);
v___x_5096_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5097_; 
v___x_5097_ = lean_array_push(v_b_5070_, v___x_5096_);
v___y_5072_ = v___x_5097_;
goto v___jp_5071_;
}
}
}
}
}
}
else
{
return v_b_5070_;
}
v___jp_5071_:
{
size_t v___x_5073_; size_t v___x_5074_; 
v___x_5073_ = ((size_t)1ULL);
v___x_5074_ = lean_usize_add(v_i_5068_, v___x_5073_);
v_i_5068_ = v___x_5074_;
v_b_5070_ = v___y_5072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0___boxed(lean_object* v_entries_5104_, lean_object* v_as_5105_, lean_object* v_i_5106_, lean_object* v_stop_5107_, lean_object* v_b_5108_){
_start:
{
size_t v_i_boxed_5109_; size_t v_stop_boxed_5110_; lean_object* v_res_5111_; 
v_i_boxed_5109_ = lean_unbox_usize(v_i_5106_);
lean_dec(v_i_5106_);
v_stop_boxed_5110_ = lean_unbox_usize(v_stop_5107_);
lean_dec(v_stop_5107_);
v_res_5111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_5104_, v_as_5105_, v_i_boxed_5109_, v_stop_boxed_5110_, v_b_5108_);
lean_dec_ref(v_as_5105_);
lean_dec(v_entries_5104_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(lean_object* v_ws_5112_, lean_object* v_entries_5113_){
_start:
{
lean_object* v_root_5115_; lean_object* v_packages_5116_; lean_object* v___y_5118_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; uint8_t v___x_5134_; 
v_root_5115_ = lean_ctor_get(v_ws_5112_, 0);
lean_inc_ref(v_root_5115_);
v_packages_5116_ = lean_ctor_get(v_ws_5112_, 5);
lean_inc_ref(v_packages_5116_);
lean_dec_ref(v_ws_5112_);
v___x_5131_ = lean_unsigned_to_nat(0u);
v___x_5132_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_loadDepPackage___closed__0));
v___x_5133_ = lean_array_get_size(v_packages_5116_);
v___x_5134_ = lean_nat_dec_lt(v___x_5131_, v___x_5133_);
if (v___x_5134_ == 0)
{
lean_dec_ref(v_packages_5116_);
v___y_5118_ = v___x_5132_;
goto v___jp_5117_;
}
else
{
uint8_t v___x_5135_; 
v___x_5135_ = lean_nat_dec_le(v___x_5133_, v___x_5133_);
if (v___x_5135_ == 0)
{
if (v___x_5134_ == 0)
{
lean_dec_ref(v_packages_5116_);
v___y_5118_ = v___x_5132_;
goto v___jp_5117_;
}
else
{
size_t v___x_5136_; size_t v___x_5137_; lean_object* v___x_5138_; 
v___x_5136_ = ((size_t)0ULL);
v___x_5137_ = lean_usize_of_nat(v___x_5133_);
v___x_5138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_5113_, v_packages_5116_, v___x_5136_, v___x_5137_, v___x_5132_);
lean_dec_ref(v_packages_5116_);
v___y_5118_ = v___x_5138_;
goto v___jp_5117_;
}
}
else
{
size_t v___x_5139_; size_t v___x_5140_; lean_object* v___x_5141_; 
v___x_5139_ = ((size_t)0ULL);
v___x_5140_ = lean_usize_of_nat(v___x_5133_);
v___x_5141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest_spec__0(v_entries_5113_, v_packages_5116_, v___x_5139_, v___x_5140_, v___x_5132_);
lean_dec_ref(v_packages_5116_);
v___y_5118_ = v___x_5141_;
goto v___jp_5117_;
}
}
v___jp_5117_:
{
lean_object* v_config_5119_; lean_object* v_baseName_5120_; lean_object* v_dir_5121_; lean_object* v_relManifestFile_5122_; lean_object* v_toWorkspaceConfig_5123_; uint8_t v_fixedToolchain_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v_manifest_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v_config_5119_ = lean_ctor_get(v_root_5115_, 6);
lean_inc_ref(v_config_5119_);
v_baseName_5120_ = lean_ctor_get(v_root_5115_, 1);
lean_inc(v_baseName_5120_);
v_dir_5121_ = lean_ctor_get(v_root_5115_, 4);
lean_inc_ref(v_dir_5121_);
v_relManifestFile_5122_ = lean_ctor_get(v_root_5115_, 9);
lean_inc_ref(v_relManifestFile_5122_);
lean_dec_ref(v_root_5115_);
v_toWorkspaceConfig_5123_ = lean_ctor_get(v_config_5119_, 0);
lean_inc_ref(v_toWorkspaceConfig_5123_);
v_fixedToolchain_5124_ = lean_ctor_get_uint8(v_config_5119_, sizeof(void*)*26 + 6);
lean_dec_ref(v_config_5119_);
v___x_5125_ = l_Lake_defaultLakeDir;
v___x_5126_ = l_System_FilePath_normalize(v_toWorkspaceConfig_5123_);
v___x_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5127_, 0, v___x_5126_);
v_manifest_5128_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_manifest_5128_, 0, v_baseName_5120_);
lean_ctor_set(v_manifest_5128_, 1, v___x_5125_);
lean_ctor_set(v_manifest_5128_, 2, v___x_5127_);
lean_ctor_set(v_manifest_5128_, 3, v___y_5118_);
lean_ctor_set_uint8(v_manifest_5128_, sizeof(void*)*4, v_fixedToolchain_5124_);
v___x_5129_ = l_Lake_joinRelative(v_dir_5121_, v_relManifestFile_5122_);
v___x_5130_ = l_Lake_Manifest_save(v_manifest_5128_, v___x_5129_);
lean_dec_ref(v___x_5129_);
return v___x_5130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest___boxed(lean_object* v_ws_5142_, lean_object* v_entries_5143_, lean_object* v_a_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_ws_5142_, v_entries_5143_);
lean_dec(v_entries_5143_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(lean_object* v_pkg_5146_, lean_object* v_as_5147_, size_t v_i_5148_, size_t v_stop_5149_, lean_object* v_b_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v_a_5155_; lean_object* v___y_5160_; uint8_t v___x_5165_; 
v___x_5165_ = lean_usize_dec_eq(v_i_5148_, v_stop_5149_);
if (v___x_5165_ == 0)
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_9315__overap_5168_; lean_object* v___x_5169_; 
v___x_5166_ = lean_unsigned_to_nat(0u);
v___x_5167_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
v___x_9315__overap_5168_ = lean_array_uget_borrowed(v_as_5147_, v_i_5148_);
lean_inc(v___x_9315__overap_5168_);
lean_inc(v___y_5151_);
lean_inc_ref(v_pkg_5146_);
v___x_5169_ = lean_apply_4(v___x_9315__overap_5168_, v_pkg_5146_, v___y_5151_, v___x_5167_, lean_box(0));
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; lean_object* v_a_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
v_a_5171_ = lean_ctor_get(v___x_5169_, 1);
lean_inc(v_a_5171_);
lean_dec_ref(v___x_5169_);
v___x_5172_ = lean_array_get_size(v_a_5171_);
v___x_5173_ = lean_nat_dec_lt(v___x_5166_, v___x_5172_);
if (v___x_5173_ == 0)
{
lean_dec(v_a_5171_);
v_a_5155_ = v_a_5170_;
goto v___jp_5154_;
}
else
{
lean_object* v___x_5174_; uint8_t v___x_5175_; 
v___x_5174_ = lean_box(0);
v___x_5175_ = lean_nat_dec_le(v___x_5172_, v___x_5172_);
if (v___x_5175_ == 0)
{
if (v___x_5173_ == 0)
{
lean_dec(v_a_5171_);
v_a_5155_ = v_a_5170_;
goto v___jp_5154_;
}
else
{
size_t v___x_5176_; size_t v___x_5177_; lean_object* v___x_5178_; 
v___x_5176_ = ((size_t)0ULL);
v___x_5177_ = lean_usize_of_nat(v___x_5172_);
v___x_5178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5171_, v___x_5176_, v___x_5177_, v___x_5174_, v___y_5152_);
lean_dec(v_a_5171_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_dec_ref(v___x_5178_);
v_a_5155_ = v_a_5170_;
goto v___jp_5154_;
}
else
{
lean_dec(v_a_5170_);
v___y_5160_ = v___x_5178_;
goto v___jp_5159_;
}
}
}
else
{
size_t v___x_5179_; size_t v___x_5180_; lean_object* v___x_5181_; 
v___x_5179_ = ((size_t)0ULL);
v___x_5180_ = lean_usize_of_nat(v___x_5172_);
v___x_5181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5171_, v___x_5179_, v___x_5180_, v___x_5174_, v___y_5152_);
lean_dec(v_a_5171_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_dec_ref(v___x_5181_);
v_a_5155_ = v_a_5170_;
goto v___jp_5154_;
}
else
{
lean_dec(v_a_5170_);
v___y_5160_ = v___x_5181_;
goto v___jp_5159_;
}
}
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5183_; uint8_t v___x_5184_; 
v_a_5182_ = lean_ctor_get(v___x_5169_, 1);
lean_inc(v_a_5182_);
lean_dec_ref(v___x_5169_);
v___x_5183_ = lean_array_get_size(v_a_5182_);
v___x_5184_ = lean_nat_dec_lt(v___x_5166_, v___x_5183_);
if (v___x_5184_ == 0)
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
lean_dec(v_a_5182_);
lean_dec_ref(v_pkg_5146_);
v___x_5185_ = lean_box(0);
v___x_5186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5185_);
return v___x_5186_;
}
else
{
lean_object* v___x_5187_; uint8_t v___x_5188_; 
v___x_5187_ = lean_box(0);
v___x_5188_ = lean_nat_dec_le(v___x_5183_, v___x_5183_);
if (v___x_5188_ == 0)
{
if (v___x_5184_ == 0)
{
lean_dec(v_a_5182_);
lean_dec_ref(v_pkg_5146_);
goto v___jp_5162_;
}
else
{
size_t v___x_5189_; size_t v___x_5190_; lean_object* v___x_5191_; 
v___x_5189_ = ((size_t)0ULL);
v___x_5190_ = lean_usize_of_nat(v___x_5183_);
v___x_5191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5182_, v___x_5189_, v___x_5190_, v___x_5187_, v___y_5152_);
lean_dec(v_a_5182_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_dec_ref(v___x_5191_);
lean_dec_ref(v_pkg_5146_);
goto v___jp_5162_;
}
else
{
v___y_5160_ = v___x_5191_;
goto v___jp_5159_;
}
}
}
else
{
size_t v___x_5192_; size_t v___x_5193_; lean_object* v___x_5194_; 
v___x_5192_ = ((size_t)0ULL);
v___x_5193_ = lean_usize_of_nat(v___x_5183_);
v___x_5194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5182_, v___x_5192_, v___x_5193_, v___x_5187_, v___y_5152_);
lean_dec(v_a_5182_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_dec_ref(v___x_5194_);
lean_dec_ref(v_pkg_5146_);
goto v___jp_5162_;
}
else
{
v___y_5160_ = v___x_5194_;
goto v___jp_5159_;
}
}
}
}
}
else
{
lean_object* v___x_5195_; 
lean_dec_ref(v_pkg_5146_);
v___x_5195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5195_, 0, v_b_5150_);
return v___x_5195_;
}
v___jp_5154_:
{
size_t v___x_5156_; size_t v___x_5157_; 
v___x_5156_ = ((size_t)1ULL);
v___x_5157_ = lean_usize_add(v_i_5148_, v___x_5156_);
v_i_5148_ = v___x_5157_;
v_b_5150_ = v_a_5155_;
goto _start;
}
v___jp_5159_:
{
if (lean_obj_tag(v___y_5160_) == 0)
{
lean_object* v_a_5161_; 
v_a_5161_ = lean_ctor_get(v___y_5160_, 0);
lean_inc(v_a_5161_);
lean_dec_ref(v___y_5160_);
v_a_5155_ = v_a_5161_;
goto v___jp_5154_;
}
else
{
lean_dec_ref(v_pkg_5146_);
return v___y_5160_;
}
}
v___jp_5162_:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5163_ = lean_box(0);
v___x_5164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5163_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0___boxed(lean_object* v_pkg_5196_, lean_object* v_as_5197_, lean_object* v_i_5198_, lean_object* v_stop_5199_, lean_object* v_b_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
size_t v_i_boxed_5204_; size_t v_stop_boxed_5205_; lean_object* v_res_5206_; 
v_i_boxed_5204_ = lean_unbox_usize(v_i_5198_);
lean_dec(v_i_5198_);
v_stop_boxed_5205_ = lean_unbox_usize(v_stop_5199_);
lean_dec(v_stop_5199_);
v_res_5206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_5196_, v_as_5197_, v_i_boxed_5204_, v_stop_boxed_5205_, v_b_5200_, v___y_5201_, v___y_5202_);
lean_dec_ref(v___y_5202_);
lean_dec(v___y_5201_);
lean_dec_ref(v_as_5197_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(lean_object* v_pkg_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_){
_start:
{
lean_object* v_baseName_5212_; lean_object* v_postUpdateHooks_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; uint8_t v___x_5216_; 
v_baseName_5212_ = lean_ctor_get(v_pkg_5208_, 1);
v_postUpdateHooks_5213_ = lean_ctor_get(v_pkg_5208_, 18);
lean_inc_ref(v_postUpdateHooks_5213_);
v___x_5214_ = lean_array_get_size(v_postUpdateHooks_5213_);
v___x_5215_ = lean_unsigned_to_nat(0u);
v___x_5216_ = lean_nat_dec_eq(v___x_5214_, v___x_5215_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; uint8_t v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; uint8_t v___x_5224_; 
lean_inc(v_baseName_5212_);
v___x_5217_ = l_Lean_Name_toString(v_baseName_5212_, v___x_5216_);
v___x_5218_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___closed__0));
v___x_5219_ = lean_string_append(v___x_5217_, v___x_5218_);
v___x_5220_ = 1;
v___x_5221_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5221_, 0, v___x_5219_);
lean_ctor_set_uint8(v___x_5221_, sizeof(void*)*1, v___x_5220_);
lean_inc_ref(v_a_5210_);
v___x_5222_ = lean_apply_2(v_a_5210_, v___x_5221_, lean_box(0));
v___x_5223_ = lean_box(0);
v___x_5224_ = lean_nat_dec_lt(v___x_5215_, v___x_5214_);
if (v___x_5224_ == 0)
{
lean_object* v___x_5225_; 
lean_dec_ref(v_postUpdateHooks_5213_);
lean_dec_ref(v_pkg_5208_);
v___x_5225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5223_);
return v___x_5225_;
}
else
{
uint8_t v___x_5226_; 
v___x_5226_ = lean_nat_dec_le(v___x_5214_, v___x_5214_);
if (v___x_5226_ == 0)
{
if (v___x_5224_ == 0)
{
lean_object* v___x_5227_; 
lean_dec_ref(v_postUpdateHooks_5213_);
lean_dec_ref(v_pkg_5208_);
v___x_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5223_);
return v___x_5227_;
}
else
{
size_t v___x_5228_; size_t v___x_5229_; lean_object* v___x_5230_; 
v___x_5228_ = ((size_t)0ULL);
v___x_5229_ = lean_usize_of_nat(v___x_5214_);
v___x_5230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_5208_, v_postUpdateHooks_5213_, v___x_5228_, v___x_5229_, v___x_5223_, v_a_5209_, v_a_5210_);
lean_dec_ref(v_postUpdateHooks_5213_);
return v___x_5230_;
}
}
else
{
size_t v___x_5231_; size_t v___x_5232_; lean_object* v___x_5233_; 
v___x_5231_ = ((size_t)0ULL);
v___x_5232_ = lean_usize_of_nat(v___x_5214_);
v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks_spec__0(v_pkg_5208_, v_postUpdateHooks_5213_, v___x_5231_, v___x_5232_, v___x_5223_, v_a_5209_, v_a_5210_);
lean_dec_ref(v_postUpdateHooks_5213_);
return v___x_5233_;
}
}
}
else
{
lean_object* v___x_5234_; lean_object* v___x_5235_; 
lean_dec_ref(v_postUpdateHooks_5213_);
lean_dec_ref(v_pkg_5208_);
v___x_5234_ = lean_box(0);
v___x_5235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5234_);
return v___x_5235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks___boxed(lean_object* v_pkg_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v_pkg_5236_, v_a_5237_, v_a_5238_);
lean_dec_ref(v_a_5238_);
lean_dec(v_a_5237_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(lean_object* v_a_5241_, lean_object* v_ws_5242_, lean_object* v_toUpdate_5243_, lean_object* v_leanOpts_5244_, uint8_t v_updateToolchain_5245_){
_start:
{
lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5247_ = lean_box(1);
lean_inc_ref(v_ws_5242_);
v___x_5248_ = l___private_Lake_Load_Resolve_0__Lake_reuseManifest___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__4(v_a_5241_, v_ws_5242_, v_toUpdate_5243_, v___x_5247_);
if (lean_obj_tag(v___x_5248_) == 0)
{
lean_object* v_a_5249_; lean_object* v_snd_5250_; lean_object* v_root_5251_; lean_object* v___x_5252_; 
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
lean_inc(v_a_5249_);
lean_dec_ref(v___x_5248_);
v_snd_5250_ = lean_ctor_get(v_a_5249_, 1);
lean_inc(v_snd_5250_);
lean_dec(v_a_5249_);
v_root_5251_ = lean_ctor_get(v_ws_5242_, 0);
lean_inc_ref(v_root_5251_);
v___x_5252_ = l_Lake_Workspace_addPackage(v_root_5251_, v_ws_5242_);
if (v_updateToolchain_5245_ == 0)
{
lean_object* v_root_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v_root_5253_ = lean_ctor_get(v___x_5252_, 0);
lean_inc_ref(v_root_5253_);
v___x_5254_ = lean_box(0);
v___x_5255_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6(v_leanOpts_5244_, v___x_5252_, v_root_5253_, v___x_5254_, v_snd_5250_, v_a_5241_);
return v___x_5255_;
}
else
{
lean_object* v_root_5256_; lean_object* v_packages_5257_; lean_object* v___y_5259_; lean_object* v_fst_5260_; lean_object* v_snd_5261_; lean_object* v___y_5274_; lean_object* v_depConfigs_5278_; lean_object* v___x_5279_; size_t v_sz_5280_; size_t v___x_5281_; lean_object* v___x_5282_; 
v_root_5256_ = lean_ctor_get(v___x_5252_, 0);
lean_inc_ref(v_root_5256_);
v_packages_5257_ = lean_ctor_get(v___x_5252_, 5);
lean_inc_ref(v_packages_5257_);
v_depConfigs_5278_ = lean_ctor_get(v_root_5256_, 12);
lean_inc_ref(v_depConfigs_5278_);
v___x_5279_ = l_Array_reverse___redArg(v_depConfigs_5278_);
v_sz_5280_ = lean_array_size(v___x_5279_);
v___x_5281_ = ((size_t)0ULL);
lean_inc_ref(v___x_5279_);
lean_inc_ref(v___x_5252_);
v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__8(v_root_5256_, v_updateToolchain_5245_, v___x_5252_, v_sz_5280_, v___x_5281_, v___x_5279_, v_snd_5250_, v_a_5241_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v_a_5283_; lean_object* v_fst_5284_; lean_object* v_snd_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5324_; 
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
lean_inc(v_a_5283_);
lean_dec_ref(v___x_5282_);
v_fst_5284_ = lean_ctor_get(v_a_5283_, 0);
v_snd_5285_ = lean_ctor_get(v_a_5283_, 1);
v_isSharedCheck_5324_ = !lean_is_exclusive(v_a_5283_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5287_ = v_a_5283_;
v_isShared_5288_ = v_isSharedCheck_5324_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_snd_5285_);
lean_inc(v_fst_5284_);
lean_dec(v_a_5283_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5324_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; 
lean_inc_ref(v___x_5252_);
v___x_5289_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateToolchain___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__11(v_a_5241_, v___x_5252_, v_fst_5284_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5314_; 
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5314_ == 0)
{
lean_object* v_unused_5315_; 
v_unused_5315_ = lean_ctor_get(v___x_5289_, 0);
lean_dec(v_unused_5315_);
v___x_5291_ = v___x_5289_;
v_isShared_5292_ = v_isSharedCheck_5314_;
goto v_resetjp_5290_;
}
else
{
lean_dec(v___x_5289_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5314_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; uint8_t v___x_5296_; 
v___x_5293_ = l_Array_zip___redArg(v___x_5279_, v_fst_5284_);
lean_dec(v_fst_5284_);
lean_dec_ref(v___x_5279_);
v___x_5294_ = lean_unsigned_to_nat(0u);
v___x_5295_ = lean_array_get_size(v___x_5293_);
v___x_5296_ = lean_nat_dec_lt(v___x_5294_, v___x_5295_);
if (v___x_5296_ == 0)
{
lean_object* v___x_5298_; 
lean_dec_ref(v___x_5293_);
lean_inc(v_snd_5285_);
lean_inc_ref(v___x_5252_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5252_);
v___x_5298_ = v___x_5287_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v___x_5252_);
lean_ctor_set(v_reuseFailAlloc_5302_, 1, v_snd_5285_);
v___x_5298_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
lean_object* v___x_5300_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 0, v___x_5298_);
v___x_5300_ = v___x_5291_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5298_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
v___y_5259_ = v___x_5300_;
v_fst_5260_ = v___x_5252_;
v_snd_5261_ = v_snd_5285_;
goto v___jp_5258_;
}
}
}
else
{
uint8_t v___x_5303_; 
v___x_5303_ = lean_nat_dec_le(v___x_5295_, v___x_5295_);
if (v___x_5303_ == 0)
{
if (v___x_5296_ == 0)
{
lean_object* v___x_5305_; 
lean_dec_ref(v___x_5293_);
lean_inc(v_snd_5285_);
lean_inc_ref(v___x_5252_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5252_);
v___x_5305_ = v___x_5287_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v___x_5252_);
lean_ctor_set(v_reuseFailAlloc_5309_, 1, v_snd_5285_);
v___x_5305_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
lean_object* v___x_5307_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 0, v___x_5305_);
v___x_5307_ = v___x_5291_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v___x_5305_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
v___y_5259_ = v___x_5307_;
v_fst_5260_ = v___x_5252_;
v_snd_5261_ = v_snd_5285_;
goto v___jp_5258_;
}
}
}
else
{
size_t v___x_5310_; lean_object* v___x_5311_; 
lean_del_object(v___x_5291_);
lean_del_object(v___x_5287_);
v___x_5310_ = lean_usize_of_nat(v___x_5295_);
lean_inc_ref(v_leanOpts_5244_);
v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13(v_leanOpts_5244_, v_updateToolchain_5245_, v___x_5293_, v___x_5281_, v___x_5310_, v___x_5252_, v_snd_5285_, v_a_5241_);
lean_dec_ref(v___x_5293_);
v___y_5274_ = v___x_5311_;
goto v___jp_5273_;
}
}
else
{
size_t v___x_5312_; lean_object* v___x_5313_; 
lean_del_object(v___x_5291_);
lean_del_object(v___x_5287_);
v___x_5312_ = lean_usize_of_nat(v___x_5295_);
lean_inc_ref(v_leanOpts_5244_);
v___x_5313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__13(v_leanOpts_5244_, v_updateToolchain_5245_, v___x_5293_, v___x_5281_, v___x_5312_, v___x_5252_, v_snd_5285_, v_a_5241_);
lean_dec_ref(v___x_5293_);
v___y_5274_ = v___x_5313_;
goto v___jp_5273_;
}
}
}
}
else
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
lean_del_object(v___x_5287_);
lean_dec(v_snd_5285_);
lean_dec(v_fst_5284_);
lean_dec_ref(v___x_5279_);
lean_dec_ref(v_packages_5257_);
lean_dec_ref(v___x_5252_);
lean_dec_ref(v_leanOpts_5244_);
v_a_5316_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5289_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5289_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec_ref(v___x_5279_);
lean_dec_ref(v_packages_5257_);
lean_dec_ref(v___x_5252_);
lean_dec_ref(v_leanOpts_5244_);
v_a_5325_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5282_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5282_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
v___jp_5258_:
{
lean_object* v_packages_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; uint8_t v___x_5265_; 
v_packages_5262_ = lean_ctor_get(v_fst_5260_, 5);
lean_inc_ref(v_packages_5262_);
v___x_5263_ = lean_array_get_size(v_packages_5257_);
lean_dec_ref(v_packages_5257_);
v___x_5264_ = lean_array_get_size(v_packages_5262_);
v___x_5265_ = lean_nat_dec_lt(v___x_5263_, v___x_5264_);
if (v___x_5265_ == 0)
{
lean_dec_ref(v_packages_5262_);
lean_dec(v_snd_5261_);
lean_dec_ref(v_fst_5260_);
lean_dec_ref(v_leanOpts_5244_);
return v___y_5259_;
}
else
{
uint8_t v___x_5266_; 
v___x_5266_ = lean_nat_dec_le(v___x_5264_, v___x_5264_);
if (v___x_5266_ == 0)
{
if (v___x_5265_ == 0)
{
lean_dec_ref(v_packages_5262_);
lean_dec(v_snd_5261_);
lean_dec_ref(v_fst_5260_);
lean_dec_ref(v_leanOpts_5244_);
return v___y_5259_;
}
else
{
size_t v___x_5267_; size_t v___x_5268_; lean_object* v___x_5269_; 
lean_dec_ref(v___y_5259_);
v___x_5267_ = lean_usize_of_nat(v___x_5263_);
v___x_5268_ = lean_usize_of_nat(v___x_5264_);
v___x_5269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12(v_leanOpts_5244_, v_updateToolchain_5245_, v_packages_5262_, v___x_5267_, v___x_5268_, v_fst_5260_, v_snd_5261_, v_a_5241_);
lean_dec_ref(v_packages_5262_);
return v___x_5269_;
}
}
else
{
size_t v___x_5270_; size_t v___x_5271_; lean_object* v___x_5272_; 
lean_dec_ref(v___y_5259_);
v___x_5270_ = lean_usize_of_nat(v___x_5263_);
v___x_5271_ = lean_usize_of_nat(v___x_5264_);
v___x_5272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__12(v_leanOpts_5244_, v_updateToolchain_5245_, v_packages_5262_, v___x_5270_, v___x_5271_, v_fst_5260_, v_snd_5261_, v_a_5241_);
lean_dec_ref(v_packages_5262_);
return v___x_5272_;
}
}
}
v___jp_5273_:
{
if (lean_obj_tag(v___y_5274_) == 0)
{
lean_object* v_a_5275_; lean_object* v_fst_5276_; lean_object* v_snd_5277_; 
v_a_5275_ = lean_ctor_get(v___y_5274_, 0);
v_fst_5276_ = lean_ctor_get(v_a_5275_, 0);
lean_inc(v_fst_5276_);
v_snd_5277_ = lean_ctor_get(v_a_5275_, 1);
lean_inc(v_snd_5277_);
v___y_5259_ = v___y_5274_;
v_fst_5260_ = v_fst_5276_;
v_snd_5261_ = v_snd_5277_;
goto v___jp_5258_;
}
else
{
lean_dec_ref(v_packages_5257_);
lean_dec_ref(v_leanOpts_5244_);
return v___y_5274_;
}
}
}
}
else
{
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
lean_dec_ref(v_leanOpts_5244_);
lean_dec_ref(v_ws_5242_);
v_a_5333_ = lean_ctor_get(v___x_5248_, 0);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5248_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5335_ = v___x_5248_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5248_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5333_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0___boxed(lean_object* v_a_5341_, lean_object* v_ws_5342_, lean_object* v_toUpdate_5343_, lean_object* v_leanOpts_5344_, lean_object* v_updateToolchain_5345_, lean_object* v_a_5346_){
_start:
{
uint8_t v_updateToolchain_boxed_5347_; lean_object* v_res_5348_; 
v_updateToolchain_boxed_5347_ = lean_unbox(v_updateToolchain_5345_);
v_res_5348_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_5341_, v_ws_5342_, v_toUpdate_5343_, v_leanOpts_5344_, v_updateToolchain_boxed_5347_);
lean_dec(v_toUpdate_5343_);
lean_dec_ref(v_a_5341_);
return v_res_5348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(lean_object* v_as_5349_, size_t v_i_5350_, size_t v_stop_5351_, lean_object* v_b_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
uint8_t v___x_5356_; 
v___x_5356_ = lean_usize_dec_eq(v_i_5350_, v_stop_5351_);
if (v___x_5356_ == 0)
{
lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5357_ = lean_array_uget_borrowed(v_as_5349_, v_i_5350_);
lean_inc(v___x_5357_);
v___x_5358_ = l___private_Lake_Load_Resolve_0__Lake_Package_runPostUpdateHooks(v___x_5357_, v___y_5353_, v___y_5354_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v_a_5359_; size_t v___x_5360_; size_t v___x_5361_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
lean_inc(v_a_5359_);
lean_dec_ref(v___x_5358_);
v___x_5360_ = ((size_t)1ULL);
v___x_5361_ = lean_usize_add(v_i_5350_, v___x_5360_);
v_i_5350_ = v___x_5361_;
v_b_5352_ = v_a_5359_;
goto _start;
}
else
{
return v___x_5358_;
}
}
else
{
lean_object* v___x_5363_; 
v___x_5363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5363_, 0, v_b_5352_);
return v___x_5363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1___boxed(lean_object* v_as_5364_, lean_object* v_i_5365_, lean_object* v_stop_5366_, lean_object* v_b_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_){
_start:
{
size_t v_i_boxed_5371_; size_t v_stop_boxed_5372_; lean_object* v_res_5373_; 
v_i_boxed_5371_ = lean_unbox_usize(v_i_5365_);
lean_dec(v_i_5365_);
v_stop_boxed_5372_ = lean_unbox_usize(v_stop_5366_);
lean_dec(v_stop_5366_);
v_res_5373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_as_5364_, v_i_boxed_5371_, v_stop_boxed_5372_, v_b_5367_, v___y_5368_, v___y_5369_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v_as_5364_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize(lean_object* v_ws_5374_, lean_object* v_toUpdate_5375_, lean_object* v_leanOpts_5376_, uint8_t v_updateToolchain_5377_, lean_object* v_a_5378_){
_start:
{
lean_object* v___x_5380_; 
v___x_5380_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore___at___00Lake_Workspace_updateAndMaterialize_spec__0(v_a_5378_, v_ws_5374_, v_toUpdate_5375_, v_leanOpts_5376_, v_updateToolchain_5377_);
if (lean_obj_tag(v___x_5380_) == 0)
{
lean_object* v_a_5381_; lean_object* v_fst_5382_; lean_object* v_snd_5383_; lean_object* v___y_5385_; lean_object* v___x_5402_; 
v_a_5381_ = lean_ctor_get(v___x_5380_, 0);
lean_inc(v_a_5381_);
lean_dec_ref(v___x_5380_);
v_fst_5382_ = lean_ctor_get(v_a_5381_, 0);
lean_inc(v_fst_5382_);
v_snd_5383_ = lean_ctor_get(v_a_5381_, 1);
lean_inc(v_snd_5383_);
lean_dec(v_a_5381_);
lean_inc(v_fst_5382_);
v___x_5402_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_writeManifest(v_fst_5382_, v_snd_5383_);
lean_dec(v_snd_5383_);
if (lean_obj_tag(v___x_5402_) == 0)
{
lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5424_; 
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5424_ == 0)
{
lean_object* v_unused_5425_; 
v_unused_5425_ = lean_ctor_get(v___x_5402_, 0);
lean_dec(v_unused_5425_);
v___x_5404_ = v___x_5402_;
v_isShared_5405_ = v_isSharedCheck_5424_;
goto v_resetjp_5403_;
}
else
{
lean_dec(v___x_5402_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5424_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v_packages_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; uint8_t v___x_5409_; 
v_packages_5406_ = lean_ctor_get(v_fst_5382_, 5);
v___x_5407_ = lean_unsigned_to_nat(0u);
v___x_5408_ = lean_array_get_size(v_packages_5406_);
v___x_5409_ = lean_nat_dec_lt(v___x_5407_, v___x_5408_);
if (v___x_5409_ == 0)
{
lean_object* v___x_5411_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 0, v_fst_5382_);
v___x_5411_ = v___x_5404_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_fst_5382_);
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
v___x_5413_ = lean_box(0);
v___x_5414_ = lean_nat_dec_le(v___x_5408_, v___x_5408_);
if (v___x_5414_ == 0)
{
if (v___x_5409_ == 0)
{
lean_object* v___x_5416_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 0, v_fst_5382_);
v___x_5416_ = v___x_5404_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_fst_5382_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
else
{
size_t v___x_5418_; size_t v___x_5419_; lean_object* v___x_5420_; 
lean_del_object(v___x_5404_);
v___x_5418_ = ((size_t)0ULL);
v___x_5419_ = lean_usize_of_nat(v___x_5408_);
v___x_5420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_5406_, v___x_5418_, v___x_5419_, v___x_5413_, v_fst_5382_, v_a_5378_);
v___y_5385_ = v___x_5420_;
goto v___jp_5384_;
}
}
else
{
size_t v___x_5421_; size_t v___x_5422_; lean_object* v___x_5423_; 
lean_del_object(v___x_5404_);
v___x_5421_ = ((size_t)0ULL);
v___x_5422_ = lean_usize_of_nat(v___x_5408_);
v___x_5423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_updateAndMaterialize_spec__1(v_packages_5406_, v___x_5421_, v___x_5422_, v___x_5413_, v_fst_5382_, v_a_5378_);
v___y_5385_ = v___x_5423_;
goto v___jp_5384_;
}
}
}
}
else
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5438_; 
lean_dec(v_fst_5382_);
v_a_5426_ = lean_ctor_get(v___x_5402_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5402_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5428_ = v___x_5402_;
v_isShared_5429_ = v_isSharedCheck_5438_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5402_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5438_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5430_; uint8_t v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5436_; 
v___x_5430_ = lean_io_error_to_string(v_a_5426_);
v___x_5431_ = 3;
v___x_5432_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5432_, 0, v___x_5430_);
lean_ctor_set_uint8(v___x_5432_, sizeof(void*)*1, v___x_5431_);
lean_inc_ref(v_a_5378_);
v___x_5433_ = lean_apply_2(v_a_5378_, v___x_5432_, lean_box(0));
v___x_5434_ = lean_box(0);
if (v_isShared_5429_ == 0)
{
lean_ctor_set(v___x_5428_, 0, v___x_5434_);
v___x_5436_ = v___x_5428_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
v___jp_5384_:
{
if (lean_obj_tag(v___y_5385_) == 0)
{
lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
v_isSharedCheck_5392_ = !lean_is_exclusive(v___y_5385_);
if (v_isSharedCheck_5392_ == 0)
{
lean_object* v_unused_5393_; 
v_unused_5393_ = lean_ctor_get(v___y_5385_, 0);
lean_dec(v_unused_5393_);
v___x_5387_ = v___y_5385_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_dec(v___y_5385_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 0, v_fst_5382_);
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_fst_5382_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
lean_dec(v_fst_5382_);
v_a_5394_ = lean_ctor_get(v___y_5385_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___y_5385_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___y_5385_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___y_5385_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
v_a_5439_ = lean_ctor_get(v___x_5380_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5380_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5380_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5380_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_updateAndMaterialize___boxed(lean_object* v_ws_5447_, lean_object* v_toUpdate_5448_, lean_object* v_leanOpts_5449_, lean_object* v_updateToolchain_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_){
_start:
{
uint8_t v_updateToolchain_boxed_5453_; lean_object* v_res_5454_; 
v_updateToolchain_boxed_5453_ = lean_unbox(v_updateToolchain_5450_);
v_res_5454_ = l_Lake_Workspace_updateAndMaterialize(v_ws_5447_, v_toUpdate_5448_, v_leanOpts_5449_, v_updateToolchain_boxed_5453_, v_a_5451_);
lean_dec_ref(v_a_5451_);
lean_dec(v_toUpdate_5448_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(lean_object* v___x_5459_, lean_object* v_what_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_name_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; uint8_t v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; uint8_t v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; 
v_name_5463_ = lean_ctor_get(v___x_5459_, 0);
lean_inc(v_name_5463_);
lean_dec_ref(v___x_5459_);
v___x_5464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__0));
v___x_5465_ = lean_string_append(v___x_5464_, v_what_5460_);
v___x_5466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__1));
v___x_5467_ = lean_string_append(v___x_5465_, v___x_5466_);
v___x_5468_ = 1;
v___x_5469_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5463_, v___x_5468_);
v___x_5470_ = lean_string_append(v___x_5467_, v___x_5469_);
v___x_5471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__2));
v___x_5472_ = lean_string_append(v___x_5470_, v___x_5471_);
v___x_5473_ = lean_string_append(v___x_5472_, v___x_5469_);
lean_dec_ref(v___x_5469_);
v___x_5474_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___closed__3));
v___x_5475_ = lean_string_append(v___x_5473_, v___x_5474_);
v___x_5476_ = 2;
v___x_5477_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5477_, 0, v___x_5475_);
lean_ctor_set_uint8(v___x_5477_, sizeof(void*)*1, v___x_5476_);
lean_inc_ref(v___y_5461_);
v___x_5478_ = lean_apply_2(v___y_5461_, v___x_5477_, lean_box(0));
v___x_5479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5478_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0___boxed(lean_object* v___x_5480_, lean_object* v_what_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_){
_start:
{
lean_object* v_res_5484_; 
v_res_5484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5480_, v_what_5481_, v___y_5482_);
lean_dec_ref(v___y_5482_);
lean_dec_ref(v_what_5481_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(lean_object* v_pkgEntries_5488_, lean_object* v_as_5489_, size_t v_i_5490_, size_t v_stop_5491_, lean_object* v_b_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v_a_5496_; lean_object* v___y_5501_; uint8_t v___x_5503_; 
v___x_5503_ = lean_usize_dec_eq(v_i_5490_, v_stop_5491_);
if (v___x_5503_ == 0)
{
lean_object* v___x_5504_; lean_object* v_src_x3f_5505_; 
v___x_5504_ = lean_array_uget_borrowed(v_as_5489_, v_i_5490_);
v_src_x3f_5505_ = lean_ctor_get(v___x_5504_, 3);
if (lean_obj_tag(v_src_x3f_5505_) == 1)
{
lean_object* v_name_5506_; lean_object* v_val_5507_; lean_object* v___x_5508_; 
v_name_5506_ = lean_ctor_get(v___x_5504_, 0);
v_val_5507_ = lean_ctor_get(v_src_x3f_5505_, 0);
v___x_5508_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_pkgEntries_5488_, v_name_5506_);
if (lean_obj_tag(v___x_5508_) == 1)
{
lean_object* v_val_5509_; lean_object* v___y_5511_; lean_object* v___y_5515_; 
v_val_5509_ = lean_ctor_get(v___x_5508_, 0);
lean_inc(v_val_5509_);
lean_dec_ref(v___x_5508_);
if (lean_obj_tag(v_val_5507_) == 0)
{
lean_object* v_src_5518_; 
v_src_5518_ = lean_ctor_get(v_val_5509_, 4);
lean_inc_ref(v_src_5518_);
lean_dec(v_val_5509_);
if (lean_obj_tag(v_src_5518_) == 0)
{
lean_object* v___x_5519_; 
lean_dec_ref(v_src_5518_);
v___x_5519_ = lean_box(0);
v_a_5496_ = v___x_5519_;
goto v___jp_5495_;
}
else
{
lean_dec_ref(v_src_5518_);
v___y_5515_ = v___y_5493_;
goto v___jp_5514_;
}
}
else
{
lean_object* v_src_5520_; 
v_src_5520_ = lean_ctor_get(v_val_5509_, 4);
lean_inc_ref(v_src_5520_);
lean_dec(v_val_5509_);
if (lean_obj_tag(v_src_5520_) == 1)
{
lean_object* v_url_5521_; lean_object* v_rev_5522_; lean_object* v_url_5523_; lean_object* v_inputRev_x3f_5524_; lean_object* v___y_5526_; uint8_t v___x_5533_; 
v_url_5521_ = lean_ctor_get(v_val_5507_, 0);
v_rev_5522_ = lean_ctor_get(v_val_5507_, 1);
v_url_5523_ = lean_ctor_get(v_src_5520_, 0);
lean_inc_ref(v_url_5523_);
v_inputRev_x3f_5524_ = lean_ctor_get(v_src_5520_, 2);
lean_inc(v_inputRev_x3f_5524_);
lean_dec_ref(v_src_5520_);
v___x_5533_ = lean_string_dec_eq(v_url_5521_, v_url_5523_);
lean_dec_ref(v_url_5523_);
if (v___x_5533_ == 0)
{
goto v___jp_5530_;
}
else
{
if (v___x_5503_ == 0)
{
v___y_5526_ = v___y_5493_;
goto v___jp_5525_;
}
else
{
goto v___jp_5530_;
}
}
v___jp_5525_:
{
lean_object* v___x_5527_; uint8_t v___x_5528_; 
v___x_5527_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
lean_inc(v_rev_5522_);
v___x_5528_ = l_Option_instDecidableEq___redArg(v___x_5527_, v_rev_5522_, v_inputRev_x3f_5524_);
if (v___x_5528_ == 0)
{
v___y_5511_ = v___y_5526_;
goto v___jp_5510_;
}
else
{
if (v___x_5503_ == 0)
{
lean_object* v___x_5529_; 
v___x_5529_ = lean_box(0);
v_a_5496_ = v___x_5529_;
goto v___jp_5495_;
}
else
{
v___y_5511_ = v___y_5526_;
goto v___jp_5510_;
}
}
}
v___jp_5530_:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__2));
lean_inc(v___x_5504_);
v___x_5532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5504_, v___x_5531_, v___y_5493_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_dec_ref(v___x_5532_);
v___y_5526_ = v___y_5493_;
goto v___jp_5525_;
}
else
{
lean_dec(v_inputRev_x3f_5524_);
return v___x_5532_;
}
}
}
else
{
lean_dec_ref(v_src_5520_);
v___y_5515_ = v___y_5493_;
goto v___jp_5514_;
}
}
v___jp_5510_:
{
lean_object* v___x_5512_; lean_object* v___x_5513_; 
v___x_5512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__0));
lean_inc(v___x_5504_);
v___x_5513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5504_, v___x_5512_, v___y_5511_);
v___y_5501_ = v___x_5513_;
goto v___jp_5500_;
}
v___jp_5514_:
{
lean_object* v___x_5516_; lean_object* v___x_5517_; 
v___x_5516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___closed__1));
lean_inc(v___x_5504_);
v___x_5517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___lam__0(v___x_5504_, v___x_5516_, v___y_5515_);
v___y_5501_ = v___x_5517_;
goto v___jp_5500_;
}
}
else
{
lean_object* v___x_5534_; 
lean_dec(v___x_5508_);
v___x_5534_ = lean_box(0);
v_a_5496_ = v___x_5534_;
goto v___jp_5495_;
}
}
else
{
lean_object* v___x_5535_; 
v___x_5535_ = lean_box(0);
v_a_5496_ = v___x_5535_;
goto v___jp_5495_;
}
}
else
{
lean_object* v___x_5536_; 
v___x_5536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5536_, 0, v_b_5492_);
return v___x_5536_;
}
v___jp_5495_:
{
size_t v___x_5497_; size_t v___x_5498_; 
v___x_5497_ = ((size_t)1ULL);
v___x_5498_ = lean_usize_add(v_i_5490_, v___x_5497_);
v_i_5490_ = v___x_5498_;
v_b_5492_ = v_a_5496_;
goto _start;
}
v___jp_5500_:
{
if (lean_obj_tag(v___y_5501_) == 0)
{
lean_object* v_a_5502_; 
v_a_5502_ = lean_ctor_get(v___y_5501_, 0);
lean_inc(v_a_5502_);
lean_dec_ref(v___y_5501_);
v_a_5496_ = v_a_5502_;
goto v___jp_5495_;
}
else
{
return v___y_5501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0___boxed(lean_object* v_pkgEntries_5537_, lean_object* v_as_5538_, lean_object* v_i_5539_, lean_object* v_stop_5540_, lean_object* v_b_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_){
_start:
{
size_t v_i_boxed_5544_; size_t v_stop_boxed_5545_; lean_object* v_res_5546_; 
v_i_boxed_5544_ = lean_unbox_usize(v_i_5539_);
lean_dec(v_i_5539_);
v_stop_boxed_5545_ = lean_unbox_usize(v_stop_5540_);
lean_dec(v_stop_5540_);
v_res_5546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5537_, v_as_5538_, v_i_boxed_5544_, v_stop_boxed_5545_, v_b_5541_, v___y_5542_);
lean_dec_ref(v___y_5542_);
lean_dec_ref(v_as_5538_);
lean_dec(v_pkgEntries_5537_);
return v_res_5546_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest(lean_object* v_pkgEntries_5547_, lean_object* v_deps_5548_, lean_object* v_a_5549_){
_start:
{
lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; uint8_t v___x_5554_; 
v___x_5551_ = lean_unsigned_to_nat(0u);
v___x_5552_ = lean_array_get_size(v_deps_5548_);
v___x_5553_ = lean_box(0);
v___x_5554_ = lean_nat_dec_lt(v___x_5551_, v___x_5552_);
if (v___x_5554_ == 0)
{
lean_object* v___x_5555_; 
v___x_5555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5553_);
return v___x_5555_;
}
else
{
uint8_t v___x_5556_; 
v___x_5556_ = lean_nat_dec_le(v___x_5552_, v___x_5552_);
if (v___x_5556_ == 0)
{
if (v___x_5554_ == 0)
{
lean_object* v___x_5557_; 
v___x_5557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5553_);
return v___x_5557_;
}
else
{
size_t v___x_5558_; size_t v___x_5559_; lean_object* v___x_5560_; 
v___x_5558_ = ((size_t)0ULL);
v___x_5559_ = lean_usize_of_nat(v___x_5552_);
v___x_5560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5547_, v_deps_5548_, v___x_5558_, v___x_5559_, v___x_5553_, v_a_5549_);
return v___x_5560_;
}
}
else
{
size_t v___x_5561_; size_t v___x_5562_; lean_object* v___x_5563_; 
v___x_5561_ = ((size_t)0ULL);
v___x_5562_ = lean_usize_of_nat(v___x_5552_);
v___x_5563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_validateManifest_spec__0(v_pkgEntries_5547_, v_deps_5548_, v___x_5561_, v___x_5562_, v___x_5553_, v_a_5549_);
return v___x_5563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_validateManifest___boxed(lean_object* v_pkgEntries_5564_, lean_object* v_deps_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_){
_start:
{
lean_object* v_res_5568_; 
v_res_5568_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v_pkgEntries_5564_, v_deps_5565_, v_a_5566_);
lean_dec_ref(v_a_5566_);
lean_dec_ref(v_deps_5565_);
lean_dec(v_pkgEntries_5564_);
return v_res_5568_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3(lean_object* v_x_5569_, lean_object* v_x_5570_){
_start:
{
if (lean_obj_tag(v_x_5569_) == 0)
{
if (lean_obj_tag(v_x_5570_) == 0)
{
uint8_t v___x_5571_; 
v___x_5571_ = 1;
return v___x_5571_;
}
else
{
uint8_t v___x_5572_; 
v___x_5572_ = 0;
return v___x_5572_;
}
}
else
{
if (lean_obj_tag(v_x_5570_) == 0)
{
uint8_t v___x_5573_; 
v___x_5573_ = 0;
return v___x_5573_;
}
else
{
lean_object* v_val_5574_; lean_object* v_val_5575_; uint8_t v___x_5576_; 
v_val_5574_ = lean_ctor_get(v_x_5569_, 0);
v_val_5575_ = lean_ctor_get(v_x_5570_, 0);
v___x_5576_ = lean_string_dec_eq(v_val_5574_, v_val_5575_);
return v___x_5576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3___boxed(lean_object* v_x_5577_, lean_object* v_x_5578_){
_start:
{
uint8_t v_res_5579_; lean_object* v_r_5580_; 
v_res_5579_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3(v_x_5577_, v_x_5578_);
lean_dec(v_x_5578_);
lean_dec(v_x_5577_);
v_r_5580_ = lean_box(v_res_5579_);
return v_r_5580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(lean_object* v_cycle_5581_, lean_object* v___y_5582_){
_start:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; uint8_t v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v___x_5584_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_depCycleError___redArg___closed__1));
v___x_5585_ = l_Lake_formatCycle___at___00__private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__14_spec__22(v_cycle_5581_);
v___x_5586_ = lean_string_append(v___x_5584_, v___x_5585_);
lean_dec_ref(v___x_5585_);
v___x_5587_ = 3;
v___x_5588_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5588_, 0, v___x_5586_);
lean_ctor_set_uint8(v___x_5588_, sizeof(void*)*1, v___x_5587_);
lean_inc_ref(v___y_5582_);
v___x_5589_ = lean_apply_2(v___y_5582_, v___x_5588_, lean_box(0));
v___x_5590_ = lean_box(0);
v___x_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5590_);
return v___x_5591_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_cycle_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(v_cycle_5592_, v___y_5593_);
lean_dec_ref(v___y_5593_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(lean_object* v_pkg_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v_leanOpts_5604_, uint8_t v_reconfigure_5605_, lean_object* v_as_5606_, size_t v_i_5607_, size_t v_stop_5608_, lean_object* v_b_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
uint8_t v___x_5616_; 
v___x_5616_ = lean_usize_dec_eq(v_i_5607_, v_stop_5608_);
if (v___x_5616_ == 0)
{
lean_object* v_root_5617_; lean_object* v_lakeEnv_5618_; lean_object* v_packages_5619_; size_t v___x_5620_; size_t v___x_5621_; lean_object* v_a_5623_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; uint8_t v___y_5633_; uint8_t v___x_5754_; 
v_root_5617_ = lean_ctor_get(v___y_5610_, 0);
v_lakeEnv_5618_ = lean_ctor_get(v___y_5610_, 1);
v_packages_5619_ = lean_ctor_get(v___y_5610_, 5);
v___x_5620_ = ((size_t)1ULL);
v___x_5621_ = lean_usize_sub(v_i_5607_, v___x_5620_);
v___x_5629_ = lean_array_uget_borrowed(v_as_5606_, v___x_5621_);
v___x_5630_ = lean_unsigned_to_nat(0u);
v___x_5631_ = lean_array_get_size(v_packages_5619_);
v___x_5754_ = lean_nat_dec_lt(v___x_5630_, v___x_5631_);
if (v___x_5754_ == 0)
{
v___y_5633_ = v___x_5616_;
goto v___jp_5632_;
}
else
{
if (v___x_5754_ == 0)
{
v___y_5633_ = v___x_5616_;
goto v___jp_5632_;
}
else
{
size_t v___x_5755_; size_t v___x_5756_; uint8_t v___x_5757_; 
v___x_5755_ = ((size_t)0ULL);
v___x_5756_ = lean_usize_of_nat(v___x_5631_);
v___x_5757_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__5_spec__5(v___x_5629_, v_packages_5619_, v___x_5755_, v___x_5756_);
if (v___x_5757_ == 0)
{
v___y_5633_ = v___x_5757_;
goto v___jp_5632_;
}
else
{
lean_object* v___x_5758_; 
v___x_5758_ = lean_box(0);
v_i_5607_ = v___x_5621_;
v_b_5609_ = v___x_5758_;
goto _start;
}
}
}
v___jp_5622_:
{
lean_object* v_fst_5624_; lean_object* v_snd_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v_fst_5624_ = lean_ctor_get(v_a_5623_, 0);
lean_inc(v_fst_5624_);
v_snd_5625_ = lean_ctor_get(v_a_5623_, 1);
lean_inc(v_snd_5625_);
lean_dec_ref(v_a_5623_);
v___x_5626_ = lean_box(0);
v___x_5627_ = l_Lake_Workspace_addPackage(v_fst_5624_, v_snd_5625_);
v_i_5607_ = v___x_5621_;
v_b_5609_ = v___x_5626_;
v___y_5610_ = v___x_5627_;
goto _start;
}
v___jp_5632_:
{
lean_object* v_wsIdx_5634_; lean_object* v_baseName_5635_; lean_object* v_name_5636_; lean_object* v_opts_5637_; uint8_t v___x_5638_; 
v_wsIdx_5634_ = lean_ctor_get(v_pkg_5601_, 0);
v_baseName_5635_ = lean_ctor_get(v_pkg_5601_, 1);
v_name_5636_ = lean_ctor_get(v___x_5629_, 0);
v_opts_5637_ = lean_ctor_get(v___x_5629_, 4);
v___x_5638_ = lean_name_eq(v_baseName_5635_, v_name_5636_);
if (v___x_5638_ == 0)
{
lean_object* v___x_5639_; 
v___x_5639_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_5602_, v_name_5636_);
if (lean_obj_tag(v___x_5639_) == 1)
{
lean_object* v_val_5640_; lean_object* v_dir_5641_; lean_object* v___x_5642_; 
v_val_5640_ = lean_ctor_get(v___x_5639_, 0);
lean_inc(v_val_5640_);
lean_dec_ref(v___x_5639_);
v_dir_5641_ = lean_ctor_get(v_root_5617_, 4);
lean_inc_ref(v___y_5603_);
lean_inc_ref(v_dir_5641_);
v___x_5642_ = l_Lake_PackageEntry_materialize(v_val_5640_, v_lakeEnv_5618_, v_dir_5641_, v___y_5603_, v___y_5611_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5708_; 
v_a_5643_ = lean_ctor_get(v___x_5642_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5645_ = v___x_5642_;
v_isShared_5646_ = v_isSharedCheck_5708_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5642_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5708_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5647_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_reuseManifest___closed__4));
lean_inc_ref(v_leanOpts_5604_);
lean_inc(v_opts_5637_);
v___x_5648_ = l___private_Lake_Load_Resolve_0__Lake_loadDepPackage(v___x_5631_, v_a_5643_, v_opts_5637_, v_leanOpts_5604_, v_reconfigure_5605_, v___y_5610_, v___x_5647_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v_a_5650_; lean_object* v___x_5651_; uint8_t v___x_5652_; 
lean_del_object(v___x_5645_);
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
lean_inc(v_a_5649_);
v_a_5650_ = lean_ctor_get(v___x_5648_, 1);
lean_inc(v_a_5650_);
lean_dec_ref(v___x_5648_);
v___x_5651_ = lean_array_get_size(v_a_5650_);
v___x_5652_ = lean_nat_dec_lt(v___x_5630_, v___x_5651_);
if (v___x_5652_ == 0)
{
lean_dec(v_a_5650_);
v_a_5623_ = v_a_5649_;
goto v___jp_5622_;
}
else
{
lean_object* v___x_5653_; uint8_t v___x_5654_; 
v___x_5653_ = lean_box(0);
v___x_5654_ = lean_nat_dec_le(v___x_5651_, v___x_5651_);
if (v___x_5654_ == 0)
{
if (v___x_5652_ == 0)
{
lean_dec(v_a_5650_);
v_a_5623_ = v_a_5649_;
goto v___jp_5622_;
}
else
{
size_t v___x_5655_; size_t v___x_5656_; lean_object* v___x_5657_; 
v___x_5655_ = ((size_t)0ULL);
v___x_5656_ = lean_usize_of_nat(v___x_5651_);
v___x_5657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5650_, v___x_5655_, v___x_5656_, v___x_5653_, v___y_5611_);
lean_dec(v_a_5650_);
if (lean_obj_tag(v___x_5657_) == 0)
{
lean_dec_ref(v___x_5657_);
v_a_5623_ = v_a_5649_;
goto v___jp_5622_;
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec(v_a_5649_);
lean_dec_ref(v_leanOpts_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_pkg_5601_);
v_a_5658_ = lean_ctor_get(v___x_5657_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5657_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5657_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5657_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
}
else
{
size_t v___x_5666_; size_t v___x_5667_; lean_object* v___x_5668_; 
v___x_5666_ = ((size_t)0ULL);
v___x_5667_ = lean_usize_of_nat(v___x_5651_);
v___x_5668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5650_, v___x_5666_, v___x_5667_, v___x_5653_, v___y_5611_);
lean_dec(v_a_5650_);
if (lean_obj_tag(v___x_5668_) == 0)
{
lean_dec_ref(v___x_5668_);
v_a_5623_ = v_a_5649_;
goto v___jp_5622_;
}
else
{
lean_object* v_a_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
lean_dec(v_a_5649_);
lean_dec_ref(v_leanOpts_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_pkg_5601_);
v_a_5669_ = lean_ctor_get(v___x_5668_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v___x_5668_);
if (v_isSharedCheck_5676_ == 0)
{
v___x_5671_ = v___x_5668_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_a_5669_);
lean_dec(v___x_5668_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v___x_5674_; 
if (v_isShared_5672_ == 0)
{
v___x_5674_ = v___x_5671_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
}
}
else
{
lean_object* v_a_5677_; lean_object* v___x_5678_; uint8_t v___x_5679_; 
lean_dec_ref(v_leanOpts_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_pkg_5601_);
v_a_5677_ = lean_ctor_get(v___x_5648_, 1);
lean_inc(v_a_5677_);
lean_dec_ref(v___x_5648_);
v___x_5678_ = lean_array_get_size(v_a_5677_);
v___x_5679_ = lean_nat_dec_lt(v___x_5630_, v___x_5678_);
if (v___x_5679_ == 0)
{
lean_object* v___x_5680_; lean_object* v___x_5682_; 
lean_dec(v_a_5677_);
v___x_5680_ = lean_box(0);
if (v_isShared_5646_ == 0)
{
lean_ctor_set_tag(v___x_5645_, 1);
lean_ctor_set(v___x_5645_, 0, v___x_5680_);
v___x_5682_ = v___x_5645_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v___x_5680_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
else
{
lean_object* v___x_5684_; uint8_t v___x_5685_; 
lean_del_object(v___x_5645_);
v___x_5684_ = lean_box(0);
v___x_5685_ = lean_nat_dec_le(v___x_5678_, v___x_5678_);
if (v___x_5685_ == 0)
{
if (v___x_5679_ == 0)
{
lean_dec(v_a_5677_);
goto v___jp_5613_;
}
else
{
size_t v___x_5686_; size_t v___x_5687_; lean_object* v___x_5688_; 
v___x_5686_ = ((size_t)0ULL);
v___x_5687_ = lean_usize_of_nat(v___x_5678_);
v___x_5688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5677_, v___x_5686_, v___x_5687_, v___x_5684_, v___y_5611_);
lean_dec(v_a_5677_);
if (lean_obj_tag(v___x_5688_) == 0)
{
lean_dec_ref(v___x_5688_);
goto v___jp_5613_;
}
else
{
lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5696_; 
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5696_ == 0)
{
v___x_5691_ = v___x_5688_;
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5688_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5694_; 
if (v_isShared_5692_ == 0)
{
v___x_5694_ = v___x_5691_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_a_5689_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
}
else
{
size_t v___x_5697_; size_t v___x_5698_; lean_object* v___x_5699_; 
v___x_5697_ = ((size_t)0ULL);
v___x_5698_ = lean_usize_of_nat(v___x_5678_);
v___x_5699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_reuseManifest_spec__0(v_a_5677_, v___x_5697_, v___x_5698_, v___x_5684_, v___y_5611_);
lean_dec(v_a_5677_);
if (lean_obj_tag(v___x_5699_) == 0)
{
lean_dec_ref(v___x_5699_);
goto v___jp_5613_;
}
else
{
lean_object* v_a_5700_; lean_object* v___x_5702_; uint8_t v_isShared_5703_; uint8_t v_isSharedCheck_5707_; 
v_a_5700_ = lean_ctor_get(v___x_5699_, 0);
v_isSharedCheck_5707_ = !lean_is_exclusive(v___x_5699_);
if (v_isSharedCheck_5707_ == 0)
{
v___x_5702_ = v___x_5699_;
v_isShared_5703_ = v_isSharedCheck_5707_;
goto v_resetjp_5701_;
}
else
{
lean_inc(v_a_5700_);
lean_dec(v___x_5699_);
v___x_5702_ = lean_box(0);
v_isShared_5703_ = v_isSharedCheck_5707_;
goto v_resetjp_5701_;
}
v_resetjp_5701_:
{
lean_object* v___x_5705_; 
if (v_isShared_5703_ == 0)
{
v___x_5705_ = v___x_5702_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5706_; 
v_reuseFailAlloc_5706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_a_5700_);
v___x_5705_ = v_reuseFailAlloc_5706_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
return v___x_5705_;
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
lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5716_; 
lean_dec_ref(v___y_5610_);
lean_dec_ref(v_leanOpts_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_pkg_5601_);
v_a_5709_ = lean_ctor_get(v___x_5642_, 0);
v_isSharedCheck_5716_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5711_ = v___x_5642_;
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_dec(v___x_5642_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5714_; 
if (v_isShared_5712_ == 0)
{
v___x_5714_ = v___x_5711_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
}
}
else
{
uint8_t v___x_5717_; 
lean_inc(v_baseName_5635_);
lean_inc(v_wsIdx_5634_);
lean_dec(v___x_5639_);
lean_dec_ref(v___y_5610_);
lean_dec_ref(v_leanOpts_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_pkg_5601_);
v___x_5717_ = lean_nat_dec_eq(v_wsIdx_5634_, v___x_5630_);
lean_dec(v_wsIdx_5634_);
if (v___x_5717_ == 0)
{
lean_object* v___x_5718_; uint8_t v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; uint8_t v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; 
v___x_5718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__0));
v___x_5719_ = 1;
lean_inc(v_name_5636_);
v___x_5720_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5636_, v___x_5719_);
v___x_5721_ = lean_string_append(v___x_5718_, v___x_5720_);
lean_dec_ref(v___x_5720_);
v___x_5722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__1));
v___x_5723_ = lean_string_append(v___x_5721_, v___x_5722_);
v___x_5724_ = l_Lean_Name_toString(v_baseName_5635_, v___x_5717_);
v___x_5725_ = lean_string_append(v___x_5723_, v___x_5724_);
lean_dec_ref(v___x_5724_);
v___x_5726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__2));
v___x_5727_ = lean_string_append(v___x_5725_, v___x_5726_);
v___x_5728_ = 3;
v___x_5729_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5729_, 0, v___x_5727_);
lean_ctor_set_uint8(v___x_5729_, sizeof(void*)*1, v___x_5728_);
lean_inc_ref(v___y_5611_);
v___x_5730_ = lean_apply_2(v___y_5611_, v___x_5729_, lean_box(0));
v___x_5731_ = lean_box(0);
v___x_5732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5731_);
return v___x_5732_;
}
else
{
lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; uint8_t v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
lean_dec(v_baseName_5635_);
v___x_5733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__0));
lean_inc(v_name_5636_);
v___x_5734_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_5636_, v___x_5717_);
v___x_5735_ = lean_string_append(v___x_5733_, v___x_5734_);
v___x_5736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__3));
v___x_5737_ = lean_string_append(v___x_5735_, v___x_5736_);
v___x_5738_ = lean_string_append(v___x_5737_, v___x_5734_);
lean_dec_ref(v___x_5734_);
v___x_5739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___closed__4));
v___x_5740_ = lean_string_append(v___x_5738_, v___x_5739_);
v___x_5741_ = 3;
v___x_5742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5742_, 0, v___x_5740_);
lean_ctor_set_uint8(v___x_5742_, sizeof(void*)*1, v___x_5741_);
lean_inc_ref(v___y_5611_);
v___x_5743_ = lean_apply_2(v___y_5611_, v___x_5742_, lean_box(0));
v___x_5744_ = lean_box(0);
v___x_5745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5744_);
return v___x_5745_;
}
}
}
else
{
lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; uint8_t v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; 
lean_inc(v_baseName_5635_);
lean_dec_ref(v___y_5610_);
lean_dec_ref(v_leanOpts_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_pkg_5601_);
v___x_5746_ = l_Lean_Name_toString(v_baseName_5635_, v___y_5633_);
v___x_5747_ = ((lean_object*)(l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___redArg___lam__5___closed__0));
v___x_5748_ = lean_string_append(v___x_5746_, v___x_5747_);
v___x_5749_ = 3;
v___x_5750_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5750_, 0, v___x_5748_);
lean_ctor_set_uint8(v___x_5750_, sizeof(void*)*1, v___x_5749_);
lean_inc_ref(v___y_5611_);
v___x_5751_ = lean_apply_2(v___y_5611_, v___x_5750_, lean_box(0));
v___x_5752_ = lean_box(0);
v___x_5753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5752_);
return v___x_5753_;
}
}
}
else
{
lean_object* v___x_5760_; lean_object* v___x_5761_; 
lean_dec_ref(v_leanOpts_5604_);
lean_dec_ref(v___y_5603_);
lean_dec_ref(v_pkg_5601_);
v___x_5760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5760_, 0, v_b_5609_);
lean_ctor_set(v___x_5760_, 1, v___y_5610_);
v___x_5761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5761_, 0, v___x_5760_);
return v___x_5761_;
}
v___jp_5613_:
{
lean_object* v___x_5614_; lean_object* v___x_5615_; 
v___x_5614_ = lean_box(0);
v___x_5615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5614_);
return v___x_5615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg___boxed(lean_object* v_pkg_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v_leanOpts_5765_, lean_object* v_reconfigure_5766_, lean_object* v_as_5767_, lean_object* v_i_5768_, lean_object* v_stop_5769_, lean_object* v_b_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_){
_start:
{
uint8_t v_reconfigure_boxed_5774_; size_t v_i_boxed_5775_; size_t v_stop_boxed_5776_; lean_object* v_res_5777_; 
v_reconfigure_boxed_5774_ = lean_unbox(v_reconfigure_5766_);
v_i_boxed_5775_ = lean_unbox_usize(v_i_5768_);
lean_dec(v_i_5768_);
v_stop_boxed_5776_ = lean_unbox_usize(v_stop_5769_);
lean_dec(v_stop_5769_);
v_res_5777_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5762_, v___y_5763_, v___y_5764_, v_leanOpts_5765_, v_reconfigure_boxed_5774_, v_as_5767_, v_i_boxed_5775_, v_stop_boxed_5776_, v_b_5770_, v___y_5771_, v___y_5772_);
lean_dec_ref(v___y_5772_);
lean_dec_ref(v_as_5767_);
lean_dec(v___y_5763_);
return v_res_5777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v_leanOpts_5780_, uint8_t v_reconfigure_5781_, lean_object* v___x_5782_, lean_object* v_as_5783_, size_t v_i_5784_, size_t v_stop_5785_, lean_object* v_b_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_){
_start:
{
uint8_t v___x_5790_; 
v___x_5790_ = lean_usize_dec_eq(v_i_5784_, v_stop_5785_);
if (v___x_5790_ == 0)
{
lean_object* v___x_5791_; lean_object* v___x_5792_; 
v___x_5791_ = lean_array_uget_borrowed(v_as_5783_, v_i_5784_);
lean_inc(v___x_5791_);
lean_inc_ref(v_leanOpts_5780_);
lean_inc_ref(v___y_5779_);
v___x_5792_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_5778_, v___y_5779_, v_leanOpts_5780_, v_reconfigure_5781_, v___x_5791_, v___x_5782_, v___y_5787_, v___y_5788_);
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v_fst_5794_; lean_object* v_snd_5795_; size_t v___x_5796_; size_t v___x_5797_; 
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_a_5793_);
lean_dec_ref(v___x_5792_);
v_fst_5794_ = lean_ctor_get(v_a_5793_, 0);
lean_inc(v_fst_5794_);
v_snd_5795_ = lean_ctor_get(v_a_5793_, 1);
lean_inc(v_snd_5795_);
lean_dec(v_a_5793_);
v___x_5796_ = ((size_t)1ULL);
v___x_5797_ = lean_usize_add(v_i_5784_, v___x_5796_);
v_i_5784_ = v___x_5797_;
v_b_5786_ = v_fst_5794_;
v___y_5787_ = v_snd_5795_;
goto _start;
}
else
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5806_; 
lean_dec_ref(v_leanOpts_5780_);
lean_dec_ref(v___y_5779_);
v_a_5799_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5806_ == 0)
{
v___x_5801_ = v___x_5792_;
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5792_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5804_; 
if (v_isShared_5802_ == 0)
{
v___x_5804_ = v___x_5801_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_a_5799_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
else
{
lean_object* v___x_5807_; lean_object* v___x_5808_; 
lean_dec_ref(v_leanOpts_5780_);
lean_dec_ref(v___y_5779_);
v___x_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5807_, 0, v_b_5786_);
lean_ctor_set(v___x_5807_, 1, v___y_5787_);
v___x_5808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5808_, 0, v___x_5807_);
return v___x_5808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12(lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v_leanOpts_5811_, uint8_t v_reconfigure_5812_, lean_object* v___x_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v_leanOpts_5816_, uint8_t v_reconfigure_5817_, lean_object* v_pkg_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_, lean_object* v___y_5821_){
_start:
{
lean_object* v_packages_5823_; lean_object* v_depConfigs_5824_; lean_object* v___x_5825_; lean_object* v_snd_5827_; lean_object* v_packages_5828_; lean_object* v___y_5829_; lean_object* v_____x_5845_; lean_object* v___y_5846_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; uint8_t v___x_5852_; 
v_packages_5823_ = lean_ctor_get(v_a_5820_, 5);
v_depConfigs_5824_ = lean_ctor_get(v_pkg_5818_, 12);
lean_inc_ref(v_depConfigs_5824_);
v___x_5825_ = lean_array_get_size(v_packages_5823_);
v___x_5849_ = lean_array_get_size(v_depConfigs_5824_);
v___x_5850_ = lean_unsigned_to_nat(0u);
v___x_5851_ = lean_box(0);
v___x_5852_ = lean_nat_dec_le(v___x_5849_, v___x_5849_);
if (v___x_5852_ == 0)
{
uint8_t v___x_5853_; 
v___x_5853_ = lean_nat_dec_lt(v___x_5850_, v___x_5849_);
if (v___x_5853_ == 0)
{
uint8_t v___x_5854_; 
lean_dec_ref(v_depConfigs_5824_);
lean_dec_ref(v_pkg_5818_);
lean_dec_ref(v_leanOpts_5816_);
lean_dec_ref(v___y_5815_);
v___x_5854_ = lean_nat_dec_lt(v___x_5825_, v___x_5825_);
if (v___x_5854_ == 0)
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
lean_dec_ref(v_leanOpts_5811_);
lean_dec_ref(v___y_5810_);
v___x_5855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5855_, 0, v___x_5851_);
lean_ctor_set(v___x_5855_, 1, v_a_5820_);
v___x_5856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5855_);
return v___x_5856_;
}
else
{
uint8_t v___x_5857_; 
v___x_5857_ = lean_nat_dec_le(v___x_5825_, v___x_5825_);
if (v___x_5857_ == 0)
{
if (v___x_5854_ == 0)
{
lean_object* v___x_5858_; lean_object* v___x_5859_; 
lean_dec_ref(v_leanOpts_5811_);
lean_dec_ref(v___y_5810_);
v___x_5858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5851_);
lean_ctor_set(v___x_5858_, 1, v_a_5820_);
v___x_5859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5858_);
return v___x_5859_;
}
else
{
size_t v___x_5860_; lean_object* v___x_5861_; 
lean_inc_ref(v_packages_5823_);
v___x_5860_ = lean_usize_of_nat(v___x_5825_);
v___x_5861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5809_, v___y_5810_, v_leanOpts_5811_, v_reconfigure_5812_, v___x_5813_, v_packages_5823_, v___x_5860_, v___x_5860_, v___x_5851_, v_a_5820_, v___y_5821_);
lean_dec_ref(v_packages_5823_);
return v___x_5861_;
}
}
else
{
size_t v___x_5862_; lean_object* v___x_5863_; 
lean_inc_ref(v_packages_5823_);
v___x_5862_ = lean_usize_of_nat(v___x_5825_);
v___x_5863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5809_, v___y_5810_, v_leanOpts_5811_, v_reconfigure_5812_, v___x_5813_, v_packages_5823_, v___x_5862_, v___x_5862_, v___x_5851_, v_a_5820_, v___y_5821_);
lean_dec_ref(v_packages_5823_);
return v___x_5863_;
}
}
}
else
{
size_t v___x_5864_; size_t v___x_5865_; lean_object* v___x_5866_; 
v___x_5864_ = lean_usize_of_nat(v___x_5849_);
v___x_5865_ = ((size_t)0ULL);
v___x_5866_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5818_, v___y_5814_, v___y_5815_, v_leanOpts_5816_, v_reconfigure_5817_, v_depConfigs_5824_, v___x_5864_, v___x_5865_, v___x_5851_, v_a_5820_, v___y_5821_);
lean_dec_ref(v_depConfigs_5824_);
if (lean_obj_tag(v___x_5866_) == 0)
{
lean_object* v_a_5867_; 
v_a_5867_ = lean_ctor_get(v___x_5866_, 0);
lean_inc(v_a_5867_);
lean_dec_ref(v___x_5866_);
v_____x_5845_ = v_a_5867_;
v___y_5846_ = v___y_5821_;
goto v___jp_5844_;
}
else
{
lean_dec_ref(v_leanOpts_5811_);
lean_dec_ref(v___y_5810_);
return v___x_5866_;
}
}
}
else
{
uint8_t v___x_5868_; 
v___x_5868_ = lean_nat_dec_lt(v___x_5850_, v___x_5849_);
if (v___x_5868_ == 0)
{
lean_inc_ref(v_packages_5823_);
lean_dec_ref(v_depConfigs_5824_);
lean_dec_ref(v_pkg_5818_);
lean_dec_ref(v_leanOpts_5816_);
lean_dec_ref(v___y_5815_);
v_snd_5827_ = v_a_5820_;
v_packages_5828_ = v_packages_5823_;
v___y_5829_ = v___y_5821_;
goto v___jp_5826_;
}
else
{
size_t v___x_5869_; size_t v___x_5870_; lean_object* v___x_5871_; 
v___x_5869_ = lean_usize_of_nat(v___x_5849_);
v___x_5870_ = ((size_t)0ULL);
v___x_5871_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_5818_, v___y_5814_, v___y_5815_, v_leanOpts_5816_, v_reconfigure_5817_, v_depConfigs_5824_, v___x_5869_, v___x_5870_, v___x_5851_, v_a_5820_, v___y_5821_);
lean_dec_ref(v_depConfigs_5824_);
if (lean_obj_tag(v___x_5871_) == 0)
{
lean_object* v_a_5872_; 
v_a_5872_ = lean_ctor_get(v___x_5871_, 0);
lean_inc(v_a_5872_);
lean_dec_ref(v___x_5871_);
v_____x_5845_ = v_a_5872_;
v___y_5846_ = v___y_5821_;
goto v___jp_5844_;
}
else
{
lean_dec_ref(v_leanOpts_5811_);
lean_dec_ref(v___y_5810_);
return v___x_5871_;
}
}
}
v___jp_5826_:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; uint8_t v___x_5832_; 
v___x_5830_ = lean_array_get_size(v_packages_5828_);
v___x_5831_ = lean_box(0);
v___x_5832_ = lean_nat_dec_lt(v___x_5825_, v___x_5830_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
lean_dec_ref(v_packages_5828_);
lean_dec_ref(v_leanOpts_5811_);
lean_dec_ref(v___y_5810_);
v___x_5833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5833_, 0, v___x_5831_);
lean_ctor_set(v___x_5833_, 1, v_snd_5827_);
v___x_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5833_);
return v___x_5834_;
}
else
{
uint8_t v___x_5835_; 
v___x_5835_ = lean_nat_dec_le(v___x_5830_, v___x_5830_);
if (v___x_5835_ == 0)
{
if (v___x_5832_ == 0)
{
lean_object* v___x_5836_; lean_object* v___x_5837_; 
lean_dec_ref(v_packages_5828_);
lean_dec_ref(v_leanOpts_5811_);
lean_dec_ref(v___y_5810_);
v___x_5836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5831_);
lean_ctor_set(v___x_5836_, 1, v_snd_5827_);
v___x_5837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5837_, 0, v___x_5836_);
return v___x_5837_;
}
else
{
size_t v___x_5838_; size_t v___x_5839_; lean_object* v___x_5840_; 
v___x_5838_ = lean_usize_of_nat(v___x_5825_);
v___x_5839_ = lean_usize_of_nat(v___x_5830_);
v___x_5840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5809_, v___y_5810_, v_leanOpts_5811_, v_reconfigure_5812_, v___x_5813_, v_packages_5828_, v___x_5838_, v___x_5839_, v___x_5831_, v_snd_5827_, v___y_5829_);
lean_dec_ref(v_packages_5828_);
return v___x_5840_;
}
}
else
{
size_t v___x_5841_; size_t v___x_5842_; lean_object* v___x_5843_; 
v___x_5841_ = lean_usize_of_nat(v___x_5825_);
v___x_5842_ = lean_usize_of_nat(v___x_5830_);
v___x_5843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5809_, v___y_5810_, v_leanOpts_5811_, v_reconfigure_5812_, v___x_5813_, v_packages_5828_, v___x_5841_, v___x_5842_, v___x_5831_, v_snd_5827_, v___y_5829_);
lean_dec_ref(v_packages_5828_);
return v___x_5843_;
}
}
}
v___jp_5844_:
{
lean_object* v_snd_5847_; lean_object* v_packages_5848_; 
v_snd_5847_ = lean_ctor_get(v_____x_5845_, 1);
lean_inc(v_snd_5847_);
lean_dec_ref(v_____x_5845_);
v_packages_5848_ = lean_ctor_get(v_snd_5847_, 5);
lean_inc_ref(v_packages_5848_);
v_snd_5827_ = v_snd_5847_;
v_packages_5828_ = v_packages_5848_;
v___y_5829_ = v___y_5846_;
goto v___jp_5826_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v_leanOpts_5875_, uint8_t v_reconfigure_5876_, lean_object* v_a_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_){
_start:
{
lean_object* v_baseName_5882_; uint8_t v___x_5883_; 
v_baseName_5882_ = lean_ctor_get(v_a_5877_, 1);
v___x_5883_ = l_List_elem___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__11(v_baseName_5882_, v___y_5878_);
if (v___x_5883_ == 0)
{
lean_object* v___x_5884_; lean_object* v___x_5885_; 
lean_inc(v___y_5878_);
lean_inc(v_baseName_5882_);
v___x_5884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5884_, 0, v_baseName_5882_);
lean_ctor_set(v___x_5884_, 1, v___y_5878_);
lean_inc_ref(v_leanOpts_5875_);
lean_inc_ref(v___y_5874_);
v___x_5885_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12(v___y_5873_, v___y_5874_, v_leanOpts_5875_, v_reconfigure_5876_, v___x_5884_, v___y_5873_, v___y_5874_, v_leanOpts_5875_, v_reconfigure_5876_, v_a_5877_, v___x_5884_, v___y_5879_, v___y_5880_);
lean_dec_ref(v___x_5884_);
return v___x_5885_;
}
else
{
lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v_fst_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5899_; 
lean_inc(v_baseName_5882_);
lean_dec_ref(v___y_5879_);
lean_dec_ref(v_a_5877_);
lean_dec_ref(v_leanOpts_5875_);
lean_dec_ref(v___y_5874_);
v___x_5886_ = lean_box(0);
v___x_5887_ = ((lean_object*)(l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__10_spec__17_spec__27___redArg___closed__0));
lean_inc(v___y_5878_);
v___x_5888_ = l_List_partition_loop___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_updateAndMaterializeCore_spec__6_spec__9_spec__13(v_baseName_5882_, v___x_5883_, v___y_5878_, v___x_5887_);
v_fst_5889_ = lean_ctor_get(v___x_5888_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5888_);
if (v_isSharedCheck_5899_ == 0)
{
lean_object* v_unused_5900_; 
v_unused_5900_ = lean_ctor_get(v___x_5888_, 1);
lean_dec(v_unused_5900_);
v___x_5891_ = v___x_5888_;
v_isShared_5892_ = v_isSharedCheck_5899_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_fst_5889_);
lean_dec(v___x_5888_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5899_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5894_; 
lean_inc(v_baseName_5882_);
if (v_isShared_5892_ == 0)
{
lean_ctor_set_tag(v___x_5891_, 1);
lean_ctor_set(v___x_5891_, 1, v_fst_5889_);
lean_ctor_set(v___x_5891_, 0, v_baseName_5882_);
v___x_5894_ = v___x_5891_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_baseName_5882_);
lean_ctor_set(v_reuseFailAlloc_5898_, 1, v_fst_5889_);
v___x_5894_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5895_, 0, v_baseName_5882_);
lean_ctor_set(v___x_5895_, 1, v___x_5886_);
v___x_5896_ = l_List_appendTR___redArg(v___x_5894_, v___x_5895_);
v___x_5897_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(v___x_5896_, v___y_5880_);
return v___x_5897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v_leanOpts_5903_, lean_object* v_reconfigure_5904_, lean_object* v_a_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_){
_start:
{
uint8_t v_reconfigure_boxed_5910_; lean_object* v_res_5911_; 
v_reconfigure_boxed_5910_ = lean_unbox(v_reconfigure_5904_);
v_res_5911_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_5901_, v___y_5902_, v_leanOpts_5903_, v_reconfigure_boxed_5910_, v_a_5905_, v___y_5906_, v___y_5907_, v___y_5908_);
lean_dec_ref(v___y_5908_);
lean_dec(v___y_5906_);
lean_dec(v___y_5901_);
return v_res_5911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg___boxed(lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v_leanOpts_5914_, lean_object* v_reconfigure_5915_, lean_object* v___x_5916_, lean_object* v_as_5917_, lean_object* v_i_5918_, lean_object* v_stop_5919_, lean_object* v_b_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_){
_start:
{
uint8_t v_reconfigure_boxed_5924_; size_t v_i_boxed_5925_; size_t v_stop_boxed_5926_; lean_object* v_res_5927_; 
v_reconfigure_boxed_5924_ = lean_unbox(v_reconfigure_5915_);
v_i_boxed_5925_ = lean_unbox_usize(v_i_5918_);
lean_dec(v_i_5918_);
v_stop_boxed_5926_ = lean_unbox_usize(v_stop_5919_);
lean_dec(v_stop_5919_);
v_res_5927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_5912_, v___y_5913_, v_leanOpts_5914_, v_reconfigure_boxed_5924_, v___x_5916_, v_as_5917_, v_i_boxed_5925_, v_stop_boxed_5926_, v_b_5920_, v___y_5921_, v___y_5922_);
lean_dec_ref(v___y_5922_);
lean_dec_ref(v_as_5917_);
lean_dec(v___x_5916_);
lean_dec(v___y_5912_);
return v_res_5927_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12___boxed(lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v_leanOpts_5930_, lean_object* v_reconfigure_5931_, lean_object* v___x_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v_leanOpts_5935_, lean_object* v_reconfigure_5936_, lean_object* v_pkg_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_){
_start:
{
uint8_t v_reconfigure_boxed_5942_; uint8_t v_reconfigure_boxed_5943_; lean_object* v_res_5944_; 
v_reconfigure_boxed_5942_ = lean_unbox(v_reconfigure_5931_);
v_reconfigure_boxed_5943_ = lean_unbox(v_reconfigure_5936_);
v_res_5944_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12(v___y_5928_, v___y_5929_, v_leanOpts_5930_, v_reconfigure_boxed_5942_, v___x_5932_, v___y_5933_, v___y_5934_, v_leanOpts_5935_, v_reconfigure_boxed_5943_, v_pkg_5937_, v_a_5938_, v_a_5939_, v___y_5940_);
lean_dec_ref(v___y_5940_);
lean_dec(v_a_5938_);
lean_dec(v___y_5933_);
lean_dec(v___x_5932_);
lean_dec(v___y_5928_);
return v_res_5944_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1(lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v_leanOpts_5947_, uint8_t v_reconfigure_5948_, lean_object* v_ws_5949_, lean_object* v_root_5950_, lean_object* v_stack_5951_, lean_object* v___y_5952_){
_start:
{
lean_object* v___x_5954_; 
v___x_5954_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_5945_, v___y_5946_, v_leanOpts_5947_, v_reconfigure_5948_, v_root_5950_, v_stack_5951_, v_ws_5949_, v___y_5952_);
if (lean_obj_tag(v___x_5954_) == 0)
{
lean_object* v_a_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_5963_; 
v_a_5955_ = lean_ctor_get(v___x_5954_, 0);
v_isSharedCheck_5963_ = !lean_is_exclusive(v___x_5954_);
if (v_isSharedCheck_5963_ == 0)
{
v___x_5957_ = v___x_5954_;
v_isShared_5958_ = v_isSharedCheck_5963_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_a_5955_);
lean_dec(v___x_5954_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_5963_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
lean_object* v_snd_5959_; lean_object* v___x_5961_; 
v_snd_5959_ = lean_ctor_get(v_a_5955_, 1);
lean_inc(v_snd_5959_);
lean_dec(v_a_5955_);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 0, v_snd_5959_);
v___x_5961_ = v___x_5957_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_snd_5959_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
}
else
{
lean_object* v_a_5964_; lean_object* v___x_5966_; uint8_t v_isShared_5967_; uint8_t v_isSharedCheck_5971_; 
v_a_5964_ = lean_ctor_get(v___x_5954_, 0);
v_isSharedCheck_5971_ = !lean_is_exclusive(v___x_5954_);
if (v_isSharedCheck_5971_ == 0)
{
v___x_5966_ = v___x_5954_;
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
else
{
lean_inc(v_a_5964_);
lean_dec(v___x_5954_);
v___x_5966_ = lean_box(0);
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
v_resetjp_5965_:
{
lean_object* v___x_5969_; 
if (v_isShared_5967_ == 0)
{
v___x_5969_ = v___x_5966_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_a_5964_);
v___x_5969_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
return v___x_5969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1___boxed(lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v_leanOpts_5974_, lean_object* v_reconfigure_5975_, lean_object* v_ws_5976_, lean_object* v_root_5977_, lean_object* v_stack_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_){
_start:
{
uint8_t v_reconfigure_boxed_5981_; lean_object* v_res_5982_; 
v_reconfigure_boxed_5981_ = lean_unbox(v_reconfigure_5975_);
v_res_5982_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1(v___y_5972_, v___y_5973_, v_leanOpts_5974_, v_reconfigure_boxed_5981_, v_ws_5976_, v_root_5977_, v_stack_5978_, v___y_5979_);
lean_dec_ref(v___y_5979_);
lean_dec(v_stack_5978_);
lean_dec(v___y_5972_);
return v_res_5982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5(lean_object* v_as_5983_, size_t v_i_5984_, size_t v_stop_5985_, lean_object* v_b_5986_){
_start:
{
uint8_t v___x_5987_; 
v___x_5987_ = lean_usize_dec_eq(v_i_5984_, v_stop_5985_);
if (v___x_5987_ == 0)
{
lean_object* v___x_5988_; lean_object* v_name_5989_; lean_object* v___x_5990_; size_t v___x_5991_; size_t v___x_5992_; 
v___x_5988_ = lean_array_uget_borrowed(v_as_5983_, v_i_5984_);
v_name_5989_ = lean_ctor_get(v___x_5988_, 0);
lean_inc(v___x_5988_);
lean_inc(v_name_5989_);
v___x_5990_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_5989_, v___x_5988_, v_b_5986_);
v___x_5991_ = ((size_t)1ULL);
v___x_5992_ = lean_usize_add(v_i_5984_, v___x_5991_);
v_i_5984_ = v___x_5992_;
v_b_5986_ = v___x_5990_;
goto _start;
}
else
{
return v_b_5986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5___boxed(lean_object* v_as_5994_, lean_object* v_i_5995_, lean_object* v_stop_5996_, lean_object* v_b_5997_){
_start:
{
size_t v_i_boxed_5998_; size_t v_stop_boxed_5999_; lean_object* v_res_6000_; 
v_i_boxed_5998_ = lean_unbox_usize(v_i_5995_);
lean_dec(v_i_5995_);
v_stop_boxed_5999_ = lean_unbox_usize(v_stop_5996_);
lean_dec(v_stop_5996_);
v_res_6000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5(v_as_5994_, v_i_boxed_5998_, v_stop_boxed_5999_, v_b_5997_);
lean_dec_ref(v_as_5994_);
return v_res_6000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(lean_object* v_as_6001_, size_t v_i_6002_, size_t v_stop_6003_, lean_object* v_b_6004_){
_start:
{
uint8_t v___x_6005_; 
v___x_6005_ = lean_usize_dec_eq(v_i_6002_, v_stop_6003_);
if (v___x_6005_ == 0)
{
lean_object* v___x_6006_; lean_object* v_name_6007_; lean_object* v___x_6008_; size_t v___x_6009_; size_t v___x_6010_; lean_object* v___x_6011_; 
v___x_6006_ = lean_array_uget_borrowed(v_as_6001_, v_i_6002_);
v_name_6007_ = lean_ctor_get(v___x_6006_, 0);
lean_inc(v___x_6006_);
lean_inc(v_name_6007_);
v___x_6008_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_6007_, v___x_6006_, v_b_6004_);
v___x_6009_ = ((size_t)1ULL);
v___x_6010_ = lean_usize_add(v_i_6002_, v___x_6009_);
v___x_6011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2_spec__5(v_as_6001_, v___x_6010_, v_stop_6003_, v___x_6008_);
return v___x_6011_;
}
else
{
return v_b_6004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2___boxed(lean_object* v_as_6012_, lean_object* v_i_6013_, lean_object* v_stop_6014_, lean_object* v_b_6015_){
_start:
{
size_t v_i_boxed_6016_; size_t v_stop_boxed_6017_; lean_object* v_res_6018_; 
v_i_boxed_6016_ = lean_unbox_usize(v_i_6013_);
lean_dec(v_i_6013_);
v_stop_boxed_6017_ = lean_unbox_usize(v_stop_6014_);
lean_dec(v_stop_6014_);
v_res_6018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_as_6012_, v_i_boxed_6016_, v_stop_boxed_6017_, v_b_6015_);
lean_dec_ref(v_as_6012_);
return v_res_6018_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps(lean_object* v_ws_6028_, lean_object* v_manifest_6029_, lean_object* v_leanOpts_6030_, uint8_t v_reconfigure_6031_, lean_object* v_overrides_6032_, lean_object* v_a_6033_){
_start:
{
lean_object* v___y_6036_; lean_object* v___y_6037_; lean_object* v___y_6038_; lean_object* v___y_6039_; lean_object* v___y_6045_; lean_object* v___y_6046_; lean_object* v___y_6047_; lean_object* v___y_6048_; lean_object* v___y_6049_; lean_object* v___y_6050_; lean_object* v___y_6058_; lean_object* v___y_6059_; lean_object* v___y_6060_; lean_object* v___y_6061_; lean_object* v___y_6062_; lean_object* v___y_6063_; lean_object* v___y_6074_; lean_object* v___y_6075_; lean_object* v___y_6076_; lean_object* v___y_6077_; lean_object* v_packagesDir_x3f_6118_; lean_object* v_packages_6119_; lean_object* v___y_6121_; lean_object* v___y_6122_; lean_object* v___y_6135_; lean_object* v___x_6141_; lean_object* v___x_6142_; uint8_t v___x_6143_; 
v_packagesDir_x3f_6118_ = lean_ctor_get(v_manifest_6029_, 2);
lean_inc(v_packagesDir_x3f_6118_);
v_packages_6119_ = lean_ctor_get(v_manifest_6029_, 3);
lean_inc_ref(v_packages_6119_);
lean_dec_ref(v_manifest_6029_);
v___x_6141_ = lean_array_get_size(v_packages_6119_);
v___x_6142_ = lean_unsigned_to_nat(0u);
v___x_6143_ = lean_nat_dec_eq(v___x_6141_, v___x_6142_);
if (v___x_6143_ == 0)
{
lean_object* v_root_6144_; lean_object* v_config_6145_; lean_object* v_toWorkspaceConfig_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; uint8_t v___x_6150_; 
v_root_6144_ = lean_ctor_get(v_ws_6028_, 0);
v_config_6145_ = lean_ctor_get(v_root_6144_, 6);
v_toWorkspaceConfig_6146_ = lean_ctor_get(v_config_6145_, 0);
lean_inc_ref(v_toWorkspaceConfig_6146_);
v___x_6147_ = l_System_FilePath_normalize(v_toWorkspaceConfig_6146_);
v___x_6148_ = l_Lake_mkRelPathString(v___x_6147_);
v___x_6149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6149_, 0, v___x_6148_);
v___x_6150_ = l_Option_instBEq_beq___at___00Lake_Workspace_materializeDeps_spec__3(v_packagesDir_x3f_6118_, v___x_6149_);
lean_dec_ref(v___x_6149_);
if (v___x_6150_ == 0)
{
lean_object* v___x_6151_; lean_object* v___x_6152_; 
v___x_6151_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__4));
lean_inc_ref(v_a_6033_);
v___x_6152_ = lean_apply_2(v_a_6033_, v___x_6151_, lean_box(0));
v___y_6135_ = v_a_6033_;
goto v___jp_6134_;
}
else
{
v___y_6135_ = v_a_6033_;
goto v___jp_6134_;
}
}
else
{
v___y_6135_ = v_a_6033_;
goto v___jp_6134_;
}
v___jp_6035_:
{
lean_object* v___x_6040_; lean_object* v_root_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; 
v___x_6040_ = l_Lake_Workspace_addPackage(v___y_6038_, v_ws_6028_);
v_root_6041_ = lean_ctor_get(v___x_6040_, 0);
lean_inc_ref(v_root_6041_);
v___x_6042_ = lean_box(0);
v___x_6043_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1(v___y_6037_, v___y_6036_, v_leanOpts_6030_, v_reconfigure_6031_, v___x_6040_, v_root_6041_, v___x_6042_, v___y_6039_);
lean_dec(v___y_6037_);
return v___x_6043_;
}
v___jp_6044_:
{
if (lean_obj_tag(v___y_6050_) == 0)
{
lean_dec_ref(v___y_6045_);
v___y_6036_ = v___y_6047_;
v___y_6037_ = v___y_6050_;
v___y_6038_ = v___y_6048_;
v___y_6039_ = v___y_6049_;
goto v___jp_6035_;
}
else
{
lean_object* v___x_6051_; uint8_t v___x_6052_; 
v___x_6051_ = lean_array_get_size(v___y_6045_);
lean_dec_ref(v___y_6045_);
v___x_6052_ = lean_nat_dec_eq(v___x_6051_, v___y_6046_);
if (v___x_6052_ == 0)
{
lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; 
lean_dec_ref(v___y_6048_);
lean_dec_ref(v___y_6047_);
lean_dec_ref(v_leanOpts_6030_);
lean_dec_ref(v_ws_6028_);
v___x_6053_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__1));
lean_inc_ref(v___y_6049_);
v___x_6054_ = lean_apply_2(v___y_6049_, v___x_6053_, lean_box(0));
v___x_6055_ = lean_box(0);
v___x_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6056_, 0, v___x_6055_);
return v___x_6056_;
}
else
{
v___y_6036_ = v___y_6047_;
v___y_6037_ = v___y_6050_;
v___y_6038_ = v___y_6048_;
v___y_6039_ = v___y_6049_;
goto v___jp_6035_;
}
}
}
v___jp_6057_:
{
lean_object* v___x_6064_; uint8_t v___x_6065_; 
v___x_6064_ = lean_array_get_size(v_overrides_6032_);
v___x_6065_ = lean_nat_dec_lt(v___y_6059_, v___x_6064_);
if (v___x_6065_ == 0)
{
v___y_6045_ = v___y_6058_;
v___y_6046_ = v___y_6059_;
v___y_6047_ = v___y_6060_;
v___y_6048_ = v___y_6061_;
v___y_6049_ = v___y_6062_;
v___y_6050_ = v___y_6063_;
goto v___jp_6044_;
}
else
{
uint8_t v___x_6066_; 
v___x_6066_ = lean_nat_dec_le(v___x_6064_, v___x_6064_);
if (v___x_6066_ == 0)
{
if (v___x_6065_ == 0)
{
v___y_6045_ = v___y_6058_;
v___y_6046_ = v___y_6059_;
v___y_6047_ = v___y_6060_;
v___y_6048_ = v___y_6061_;
v___y_6049_ = v___y_6062_;
v___y_6050_ = v___y_6063_;
goto v___jp_6044_;
}
else
{
size_t v___x_6067_; size_t v___x_6068_; lean_object* v___x_6069_; 
v___x_6067_ = ((size_t)0ULL);
v___x_6068_ = lean_usize_of_nat(v___x_6064_);
v___x_6069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_overrides_6032_, v___x_6067_, v___x_6068_, v___y_6063_);
v___y_6045_ = v___y_6058_;
v___y_6046_ = v___y_6059_;
v___y_6047_ = v___y_6060_;
v___y_6048_ = v___y_6061_;
v___y_6049_ = v___y_6062_;
v___y_6050_ = v___x_6069_;
goto v___jp_6044_;
}
}
else
{
size_t v___x_6070_; size_t v___x_6071_; lean_object* v___x_6072_; 
v___x_6070_ = ((size_t)0ULL);
v___x_6071_ = lean_usize_of_nat(v___x_6064_);
v___x_6072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_overrides_6032_, v___x_6070_, v___x_6071_, v___y_6063_);
v___y_6045_ = v___y_6058_;
v___y_6046_ = v___y_6059_;
v___y_6047_ = v___y_6060_;
v___y_6048_ = v___y_6061_;
v___y_6049_ = v___y_6062_;
v___y_6050_ = v___x_6072_;
goto v___jp_6044_;
}
}
}
v___jp_6073_:
{
lean_object* v_root_6078_; lean_object* v_dir_6079_; lean_object* v_depConfigs_6080_; lean_object* v___x_6081_; 
v_root_6078_ = lean_ctor_get(v_ws_6028_, 0);
v_dir_6079_ = lean_ctor_get(v_root_6078_, 4);
v_depConfigs_6080_ = lean_ctor_get(v_root_6078_, 12);
v___x_6081_ = l___private_Lake_Load_Resolve_0__Lake_validateManifest(v___y_6077_, v_depConfigs_6080_, v___y_6076_);
if (lean_obj_tag(v___x_6081_) == 0)
{
lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
lean_dec_ref(v___x_6081_);
v___x_6082_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_6079_);
v___x_6083_ = l_Lake_joinRelative(v_dir_6079_, v___x_6082_);
v___x_6084_ = ((lean_object*)(l_Lake_Workspace_materializeDeps___closed__2));
v___x_6085_ = l_Lake_joinRelative(v___x_6083_, v___x_6084_);
v___x_6086_ = l_Lake_Manifest_tryLoadEntries(v___x_6085_);
if (lean_obj_tag(v___x_6086_) == 0)
{
lean_object* v_a_6087_; lean_object* v___x_6088_; uint8_t v___x_6089_; 
v_a_6087_ = lean_ctor_get(v___x_6086_, 0);
lean_inc(v_a_6087_);
lean_dec_ref(v___x_6086_);
v___x_6088_ = lean_array_get_size(v_a_6087_);
v___x_6089_ = lean_nat_dec_lt(v___y_6074_, v___x_6088_);
if (v___x_6089_ == 0)
{
lean_dec(v_a_6087_);
lean_inc_ref(v_root_6078_);
lean_inc_ref(v_depConfigs_6080_);
v___y_6058_ = v_depConfigs_6080_;
v___y_6059_ = v___y_6074_;
v___y_6060_ = v___y_6075_;
v___y_6061_ = v_root_6078_;
v___y_6062_ = v___y_6076_;
v___y_6063_ = v___y_6077_;
goto v___jp_6057_;
}
else
{
uint8_t v___x_6090_; 
v___x_6090_ = lean_nat_dec_le(v___x_6088_, v___x_6088_);
if (v___x_6090_ == 0)
{
if (v___x_6089_ == 0)
{
lean_dec(v_a_6087_);
lean_inc_ref(v_root_6078_);
lean_inc_ref(v_depConfigs_6080_);
v___y_6058_ = v_depConfigs_6080_;
v___y_6059_ = v___y_6074_;
v___y_6060_ = v___y_6075_;
v___y_6061_ = v_root_6078_;
v___y_6062_ = v___y_6076_;
v___y_6063_ = v___y_6077_;
goto v___jp_6057_;
}
else
{
size_t v___x_6091_; size_t v___x_6092_; lean_object* v___x_6093_; 
v___x_6091_ = ((size_t)0ULL);
v___x_6092_ = lean_usize_of_nat(v___x_6088_);
v___x_6093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_a_6087_, v___x_6091_, v___x_6092_, v___y_6077_);
lean_dec(v_a_6087_);
lean_inc_ref(v_root_6078_);
lean_inc_ref(v_depConfigs_6080_);
v___y_6058_ = v_depConfigs_6080_;
v___y_6059_ = v___y_6074_;
v___y_6060_ = v___y_6075_;
v___y_6061_ = v_root_6078_;
v___y_6062_ = v___y_6076_;
v___y_6063_ = v___x_6093_;
goto v___jp_6057_;
}
}
else
{
size_t v___x_6094_; size_t v___x_6095_; lean_object* v___x_6096_; 
v___x_6094_ = ((size_t)0ULL);
v___x_6095_ = lean_usize_of_nat(v___x_6088_);
v___x_6096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_a_6087_, v___x_6094_, v___x_6095_, v___y_6077_);
lean_dec(v_a_6087_);
lean_inc_ref(v_root_6078_);
lean_inc_ref(v_depConfigs_6080_);
v___y_6058_ = v_depConfigs_6080_;
v___y_6059_ = v___y_6074_;
v___y_6060_ = v___y_6075_;
v___y_6061_ = v_root_6078_;
v___y_6062_ = v___y_6076_;
v___y_6063_ = v___x_6096_;
goto v___jp_6057_;
}
}
}
else
{
lean_object* v_a_6097_; lean_object* v___x_6099_; uint8_t v_isShared_6100_; uint8_t v_isSharedCheck_6109_; 
lean_dec(v___y_6077_);
lean_dec_ref(v___y_6075_);
lean_dec_ref(v_leanOpts_6030_);
lean_dec_ref(v_ws_6028_);
v_a_6097_ = lean_ctor_get(v___x_6086_, 0);
v_isSharedCheck_6109_ = !lean_is_exclusive(v___x_6086_);
if (v_isSharedCheck_6109_ == 0)
{
v___x_6099_ = v___x_6086_;
v_isShared_6100_ = v_isSharedCheck_6109_;
goto v_resetjp_6098_;
}
else
{
lean_inc(v_a_6097_);
lean_dec(v___x_6086_);
v___x_6099_ = lean_box(0);
v_isShared_6100_ = v_isSharedCheck_6109_;
goto v_resetjp_6098_;
}
v_resetjp_6098_:
{
lean_object* v___x_6101_; uint8_t v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6107_; 
v___x_6101_ = lean_io_error_to_string(v_a_6097_);
v___x_6102_ = 3;
v___x_6103_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_6103_, 0, v___x_6101_);
lean_ctor_set_uint8(v___x_6103_, sizeof(void*)*1, v___x_6102_);
lean_inc_ref(v___y_6076_);
v___x_6104_ = lean_apply_2(v___y_6076_, v___x_6103_, lean_box(0));
v___x_6105_ = lean_box(0);
if (v_isShared_6100_ == 0)
{
lean_ctor_set(v___x_6099_, 0, v___x_6105_);
v___x_6107_ = v___x_6099_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v___x_6105_);
v___x_6107_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
return v___x_6107_;
}
}
}
}
else
{
lean_object* v_a_6110_; lean_object* v___x_6112_; uint8_t v_isShared_6113_; uint8_t v_isSharedCheck_6117_; 
lean_dec(v___y_6077_);
lean_dec_ref(v___y_6075_);
lean_dec_ref(v_leanOpts_6030_);
lean_dec_ref(v_ws_6028_);
v_a_6110_ = lean_ctor_get(v___x_6081_, 0);
v_isSharedCheck_6117_ = !lean_is_exclusive(v___x_6081_);
if (v_isSharedCheck_6117_ == 0)
{
v___x_6112_ = v___x_6081_;
v_isShared_6113_ = v_isSharedCheck_6117_;
goto v_resetjp_6111_;
}
else
{
lean_inc(v_a_6110_);
lean_dec(v___x_6081_);
v___x_6112_ = lean_box(0);
v_isShared_6113_ = v_isSharedCheck_6117_;
goto v_resetjp_6111_;
}
v_resetjp_6111_:
{
lean_object* v___x_6115_; 
if (v_isShared_6113_ == 0)
{
v___x_6115_ = v___x_6112_;
goto v_reusejp_6114_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6110_);
v___x_6115_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6114_;
}
v_reusejp_6114_:
{
return v___x_6115_;
}
}
}
}
v___jp_6120_:
{
lean_object* v_pkgEntries_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; uint8_t v___x_6126_; 
v_pkgEntries_6123_ = lean_box(1);
v___x_6124_ = lean_unsigned_to_nat(0u);
v___x_6125_ = lean_array_get_size(v_packages_6119_);
v___x_6126_ = lean_nat_dec_lt(v___x_6124_, v___x_6125_);
if (v___x_6126_ == 0)
{
lean_dec_ref(v_packages_6119_);
v___y_6074_ = v___x_6124_;
v___y_6075_ = v___y_6122_;
v___y_6076_ = v___y_6121_;
v___y_6077_ = v_pkgEntries_6123_;
goto v___jp_6073_;
}
else
{
uint8_t v___x_6127_; 
v___x_6127_ = lean_nat_dec_le(v___x_6125_, v___x_6125_);
if (v___x_6127_ == 0)
{
if (v___x_6126_ == 0)
{
lean_dec_ref(v_packages_6119_);
v___y_6074_ = v___x_6124_;
v___y_6075_ = v___y_6122_;
v___y_6076_ = v___y_6121_;
v___y_6077_ = v_pkgEntries_6123_;
goto v___jp_6073_;
}
else
{
size_t v___x_6128_; size_t v___x_6129_; lean_object* v___x_6130_; 
v___x_6128_ = ((size_t)0ULL);
v___x_6129_ = lean_usize_of_nat(v___x_6125_);
v___x_6130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_packages_6119_, v___x_6128_, v___x_6129_, v_pkgEntries_6123_);
lean_dec_ref(v_packages_6119_);
v___y_6074_ = v___x_6124_;
v___y_6075_ = v___y_6122_;
v___y_6076_ = v___y_6121_;
v___y_6077_ = v___x_6130_;
goto v___jp_6073_;
}
}
else
{
size_t v___x_6131_; size_t v___x_6132_; lean_object* v___x_6133_; 
v___x_6131_ = ((size_t)0ULL);
v___x_6132_ = lean_usize_of_nat(v___x_6125_);
v___x_6133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_materializeDeps_spec__2(v_packages_6119_, v___x_6131_, v___x_6132_, v_pkgEntries_6123_);
lean_dec_ref(v_packages_6119_);
v___y_6074_ = v___x_6124_;
v___y_6075_ = v___y_6122_;
v___y_6076_ = v___y_6121_;
v___y_6077_ = v___x_6133_;
goto v___jp_6073_;
}
}
}
v___jp_6134_:
{
if (lean_obj_tag(v_packagesDir_x3f_6118_) == 0)
{
lean_object* v_root_6136_; lean_object* v_config_6137_; lean_object* v_toWorkspaceConfig_6138_; lean_object* v___x_6139_; 
v_root_6136_ = lean_ctor_get(v_ws_6028_, 0);
v_config_6137_ = lean_ctor_get(v_root_6136_, 6);
v_toWorkspaceConfig_6138_ = lean_ctor_get(v_config_6137_, 0);
lean_inc_ref(v_toWorkspaceConfig_6138_);
v___x_6139_ = l_System_FilePath_normalize(v_toWorkspaceConfig_6138_);
v___y_6121_ = v___y_6135_;
v___y_6122_ = v___x_6139_;
goto v___jp_6120_;
}
else
{
lean_object* v_val_6140_; 
v_val_6140_ = lean_ctor_get(v_packagesDir_x3f_6118_, 0);
lean_inc(v_val_6140_);
lean_dec_ref(v_packagesDir_x3f_6118_);
v___y_6121_ = v___y_6135_;
v___y_6122_ = v_val_6140_;
goto v___jp_6120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_materializeDeps___boxed(lean_object* v_ws_6153_, lean_object* v_manifest_6154_, lean_object* v_leanOpts_6155_, lean_object* v_reconfigure_6156_, lean_object* v_overrides_6157_, lean_object* v_a_6158_, lean_object* v_a_6159_){
_start:
{
uint8_t v_reconfigure_boxed_6160_; lean_object* v_res_6161_; 
v_reconfigure_boxed_6160_ = lean_unbox(v_reconfigure_6156_);
v_res_6161_ = l_Lake_Workspace_materializeDeps(v_ws_6153_, v_manifest_6154_, v_leanOpts_6155_, v_reconfigure_boxed_6160_, v_overrides_6157_, v_a_6158_);
lean_dec_ref(v_a_6158_);
lean_dec_ref(v_overrides_6157_);
return v_res_6161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(lean_object* v___y_6162_, lean_object* v_as_6163_, size_t v_i_6164_, size_t v_stop_6165_, lean_object* v_b_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_){
_start:
{
uint8_t v___x_6171_; 
v___x_6171_ = lean_usize_dec_eq(v_i_6164_, v_stop_6165_);
if (v___x_6171_ == 0)
{
lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6172_ = lean_array_uget_borrowed(v_as_6163_, v_i_6164_);
lean_inc_ref(v___y_6162_);
lean_inc_ref(v___y_6169_);
lean_inc(v___y_6167_);
lean_inc(v___x_6172_);
v___x_6173_ = lean_apply_5(v___y_6162_, v___x_6172_, v___y_6167_, v___y_6168_, v___y_6169_, lean_box(0));
if (lean_obj_tag(v___x_6173_) == 0)
{
lean_object* v_a_6174_; lean_object* v_fst_6175_; lean_object* v_snd_6176_; size_t v___x_6177_; size_t v___x_6178_; 
v_a_6174_ = lean_ctor_get(v___x_6173_, 0);
lean_inc(v_a_6174_);
lean_dec_ref(v___x_6173_);
v_fst_6175_ = lean_ctor_get(v_a_6174_, 0);
lean_inc(v_fst_6175_);
v_snd_6176_ = lean_ctor_get(v_a_6174_, 1);
lean_inc(v_snd_6176_);
lean_dec(v_a_6174_);
v___x_6177_ = ((size_t)1ULL);
v___x_6178_ = lean_usize_add(v_i_6164_, v___x_6177_);
v_i_6164_ = v___x_6178_;
v_b_6166_ = v_fst_6175_;
v___y_6168_ = v_snd_6176_;
goto _start;
}
else
{
lean_dec_ref(v___y_6162_);
return v___x_6173_;
}
}
else
{
lean_object* v___x_6180_; lean_object* v___x_6181_; 
lean_dec_ref(v___y_6162_);
v___x_6180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6180_, 0, v_b_6166_);
lean_ctor_set(v___x_6180_, 1, v___y_6168_);
v___x_6181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6181_, 0, v___x_6180_);
return v___x_6181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0___boxed(lean_object* v___y_6182_, lean_object* v_as_6183_, lean_object* v_i_6184_, lean_object* v_stop_6185_, lean_object* v_b_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_){
_start:
{
size_t v_i_boxed_6191_; size_t v_stop_boxed_6192_; lean_object* v_res_6193_; 
v_i_boxed_6191_ = lean_unbox_usize(v_i_6184_);
lean_dec(v_i_6184_);
v_stop_boxed_6192_ = lean_unbox_usize(v_stop_6185_);
lean_dec(v_stop_6185_);
v_res_6193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_6182_, v_as_6183_, v_i_boxed_6191_, v_stop_boxed_6192_, v_b_6186_, v___y_6187_, v___y_6188_, v___y_6189_);
lean_dec_ref(v___y_6189_);
lean_dec(v___y_6187_);
lean_dec_ref(v_as_6183_);
return v_res_6193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v_leanOpts_6196_, uint8_t v_reconfigure_6197_, lean_object* v___y_6198_, lean_object* v_pkg_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_, lean_object* v___y_6202_){
_start:
{
lean_object* v_packages_6204_; lean_object* v_depConfigs_6205_; lean_object* v___x_6206_; lean_object* v_snd_6208_; lean_object* v_packages_6209_; lean_object* v___y_6210_; lean_object* v_____x_6226_; lean_object* v___y_6227_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; uint8_t v___x_6233_; 
v_packages_6204_ = lean_ctor_get(v_a_6201_, 5);
v_depConfigs_6205_ = lean_ctor_get(v_pkg_6199_, 12);
lean_inc_ref(v_depConfigs_6205_);
v___x_6206_ = lean_array_get_size(v_packages_6204_);
v___x_6230_ = lean_array_get_size(v_depConfigs_6205_);
v___x_6231_ = lean_unsigned_to_nat(0u);
v___x_6232_ = lean_box(0);
v___x_6233_ = lean_nat_dec_le(v___x_6230_, v___x_6230_);
if (v___x_6233_ == 0)
{
uint8_t v___x_6234_; 
v___x_6234_ = lean_nat_dec_lt(v___x_6231_, v___x_6230_);
if (v___x_6234_ == 0)
{
uint8_t v___x_6235_; 
lean_dec_ref(v_depConfigs_6205_);
lean_dec_ref(v_pkg_6199_);
lean_dec_ref(v_leanOpts_6196_);
lean_dec_ref(v___y_6195_);
v___x_6235_ = lean_nat_dec_lt(v___x_6206_, v___x_6206_);
if (v___x_6235_ == 0)
{
lean_object* v___x_6236_; lean_object* v___x_6237_; 
lean_dec_ref(v___y_6198_);
v___x_6236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6236_, 0, v___x_6232_);
lean_ctor_set(v___x_6236_, 1, v_a_6201_);
v___x_6237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6237_, 0, v___x_6236_);
return v___x_6237_;
}
else
{
uint8_t v___x_6238_; 
v___x_6238_ = lean_nat_dec_le(v___x_6206_, v___x_6206_);
if (v___x_6238_ == 0)
{
if (v___x_6235_ == 0)
{
lean_object* v___x_6239_; lean_object* v___x_6240_; 
lean_dec_ref(v___y_6198_);
v___x_6239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6239_, 0, v___x_6232_);
lean_ctor_set(v___x_6239_, 1, v_a_6201_);
v___x_6240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6240_, 0, v___x_6239_);
return v___x_6240_;
}
else
{
size_t v___x_6241_; lean_object* v___x_6242_; 
lean_inc_ref(v_packages_6204_);
v___x_6241_ = lean_usize_of_nat(v___x_6206_);
v___x_6242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_6198_, v_packages_6204_, v___x_6241_, v___x_6241_, v___x_6232_, v_a_6200_, v_a_6201_, v___y_6202_);
lean_dec_ref(v_packages_6204_);
return v___x_6242_;
}
}
else
{
size_t v___x_6243_; lean_object* v___x_6244_; 
lean_inc_ref(v_packages_6204_);
v___x_6243_ = lean_usize_of_nat(v___x_6206_);
v___x_6244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_6198_, v_packages_6204_, v___x_6243_, v___x_6243_, v___x_6232_, v_a_6200_, v_a_6201_, v___y_6202_);
lean_dec_ref(v_packages_6204_);
return v___x_6244_;
}
}
}
else
{
size_t v___x_6245_; size_t v___x_6246_; lean_object* v___x_6247_; 
v___x_6245_ = lean_usize_of_nat(v___x_6230_);
v___x_6246_ = ((size_t)0ULL);
v___x_6247_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_6199_, v___y_6194_, v___y_6195_, v_leanOpts_6196_, v_reconfigure_6197_, v_depConfigs_6205_, v___x_6245_, v___x_6246_, v___x_6232_, v_a_6201_, v___y_6202_);
lean_dec_ref(v_depConfigs_6205_);
if (lean_obj_tag(v___x_6247_) == 0)
{
lean_object* v_a_6248_; 
v_a_6248_ = lean_ctor_get(v___x_6247_, 0);
lean_inc(v_a_6248_);
lean_dec_ref(v___x_6247_);
v_____x_6226_ = v_a_6248_;
v___y_6227_ = v___y_6202_;
goto v___jp_6225_;
}
else
{
lean_dec_ref(v___y_6198_);
return v___x_6247_;
}
}
}
else
{
uint8_t v___x_6249_; 
v___x_6249_ = lean_nat_dec_lt(v___x_6231_, v___x_6230_);
if (v___x_6249_ == 0)
{
lean_inc_ref(v_packages_6204_);
lean_dec_ref(v_depConfigs_6205_);
lean_dec_ref(v_pkg_6199_);
lean_dec_ref(v_leanOpts_6196_);
lean_dec_ref(v___y_6195_);
v_snd_6208_ = v_a_6201_;
v_packages_6209_ = v_packages_6204_;
v___y_6210_ = v___y_6202_;
goto v___jp_6207_;
}
else
{
size_t v___x_6250_; size_t v___x_6251_; lean_object* v___x_6252_; 
v___x_6250_ = lean_usize_of_nat(v___x_6230_);
v___x_6251_ = ((size_t)0ULL);
v___x_6252_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_6199_, v___y_6194_, v___y_6195_, v_leanOpts_6196_, v_reconfigure_6197_, v_depConfigs_6205_, v___x_6250_, v___x_6251_, v___x_6232_, v_a_6201_, v___y_6202_);
lean_dec_ref(v_depConfigs_6205_);
if (lean_obj_tag(v___x_6252_) == 0)
{
lean_object* v_a_6253_; 
v_a_6253_ = lean_ctor_get(v___x_6252_, 0);
lean_inc(v_a_6253_);
lean_dec_ref(v___x_6252_);
v_____x_6226_ = v_a_6253_;
v___y_6227_ = v___y_6202_;
goto v___jp_6225_;
}
else
{
lean_dec_ref(v___y_6198_);
return v___x_6252_;
}
}
}
v___jp_6207_:
{
lean_object* v___x_6211_; lean_object* v___x_6212_; uint8_t v___x_6213_; 
v___x_6211_ = lean_array_get_size(v_packages_6209_);
v___x_6212_ = lean_box(0);
v___x_6213_ = lean_nat_dec_lt(v___x_6206_, v___x_6211_);
if (v___x_6213_ == 0)
{
lean_object* v___x_6214_; lean_object* v___x_6215_; 
lean_dec_ref(v_packages_6209_);
lean_dec_ref(v___y_6198_);
v___x_6214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6212_);
lean_ctor_set(v___x_6214_, 1, v_snd_6208_);
v___x_6215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6215_, 0, v___x_6214_);
return v___x_6215_;
}
else
{
uint8_t v___x_6216_; 
v___x_6216_ = lean_nat_dec_le(v___x_6211_, v___x_6211_);
if (v___x_6216_ == 0)
{
if (v___x_6213_ == 0)
{
lean_object* v___x_6217_; lean_object* v___x_6218_; 
lean_dec_ref(v_packages_6209_);
lean_dec_ref(v___y_6198_);
v___x_6217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6212_);
lean_ctor_set(v___x_6217_, 1, v_snd_6208_);
v___x_6218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6218_, 0, v___x_6217_);
return v___x_6218_;
}
else
{
size_t v___x_6219_; size_t v___x_6220_; lean_object* v___x_6221_; 
v___x_6219_ = lean_usize_of_nat(v___x_6206_);
v___x_6220_ = lean_usize_of_nat(v___x_6211_);
v___x_6221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_6198_, v_packages_6209_, v___x_6219_, v___x_6220_, v___x_6212_, v_a_6200_, v_snd_6208_, v___y_6210_);
lean_dec_ref(v_packages_6209_);
return v___x_6221_;
}
}
else
{
size_t v___x_6222_; size_t v___x_6223_; lean_object* v___x_6224_; 
v___x_6222_ = lean_usize_of_nat(v___x_6206_);
v___x_6223_ = lean_usize_of_nat(v___x_6211_);
v___x_6224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__0(v___y_6198_, v_packages_6209_, v___x_6222_, v___x_6223_, v___x_6212_, v_a_6200_, v_snd_6208_, v___y_6210_);
lean_dec_ref(v_packages_6209_);
return v___x_6224_;
}
}
}
v___jp_6225_:
{
lean_object* v_snd_6228_; lean_object* v_packages_6229_; 
v_snd_6228_ = lean_ctor_get(v_____x_6226_, 1);
lean_inc(v_snd_6228_);
lean_dec_ref(v_____x_6226_);
v_packages_6229_ = lean_ctor_get(v_snd_6228_, 5);
lean_inc_ref(v_packages_6229_);
v_snd_6208_ = v_snd_6228_;
v_packages_6209_ = v_packages_6229_;
v___y_6210_ = v___y_6227_;
goto v___jp_6207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___boxed(lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v_leanOpts_6256_, lean_object* v_reconfigure_6257_, lean_object* v___y_6258_, lean_object* v_pkg_6259_, lean_object* v_a_6260_, lean_object* v_a_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_){
_start:
{
uint8_t v_reconfigure_boxed_6264_; lean_object* v_res_6265_; 
v_reconfigure_boxed_6264_ = lean_unbox(v_reconfigure_6257_);
v_res_6265_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0(v___y_6254_, v___y_6255_, v_leanOpts_6256_, v_reconfigure_boxed_6264_, v___y_6258_, v_pkg_6259_, v_a_6260_, v_a_6261_, v___y_6262_);
lean_dec_ref(v___y_6262_);
lean_dec(v_a_6260_);
lean_dec(v___y_6254_);
return v_res_6265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(lean_object* v_pkg_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v_leanOpts_6269_, uint8_t v_reconfigure_6270_, lean_object* v_as_6271_, size_t v_i_6272_, size_t v_stop_6273_, lean_object* v_b_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_){
_start:
{
lean_object* v___x_6279_; 
v___x_6279_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_6266_, v___y_6267_, v___y_6268_, v_leanOpts_6269_, v_reconfigure_6270_, v_as_6271_, v_i_6272_, v_stop_6273_, v_b_6274_, v___y_6276_, v___y_6277_);
return v___x_6279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___boxed(lean_object* v_pkg_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v_leanOpts_6283_, lean_object* v_reconfigure_6284_, lean_object* v_as_6285_, lean_object* v_i_6286_, lean_object* v_stop_6287_, lean_object* v_b_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_){
_start:
{
uint8_t v_reconfigure_boxed_6293_; size_t v_i_boxed_6294_; size_t v_stop_boxed_6295_; lean_object* v_res_6296_; 
v_reconfigure_boxed_6293_ = lean_unbox(v_reconfigure_6284_);
v_i_boxed_6294_ = lean_unbox_usize(v_i_6286_);
lean_dec(v_i_6286_);
v_stop_boxed_6295_ = lean_unbox_usize(v_stop_6287_);
lean_dec(v_stop_6287_);
v_res_6296_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1(v_pkg_6280_, v___y_6281_, v___y_6282_, v_leanOpts_6283_, v_reconfigure_boxed_6293_, v_as_6285_, v_i_boxed_6294_, v_stop_boxed_6295_, v_b_6288_, v___y_6289_, v___y_6290_, v___y_6291_);
lean_dec_ref(v___y_6291_);
lean_dec(v___y_6289_);
lean_dec_ref(v_as_6285_);
lean_dec(v___y_6281_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v_leanOpts_6299_, uint8_t v_reconfigure_6300_, lean_object* v_a_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_){
_start:
{
lean_object* v___x_6306_; 
v___x_6306_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_6297_, v___y_6298_, v_leanOpts_6299_, v_reconfigure_6300_, v_a_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
return v___x_6306_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3___boxed(lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v_leanOpts_6309_, lean_object* v_reconfigure_6310_, lean_object* v_a_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_){
_start:
{
uint8_t v_reconfigure_boxed_6316_; lean_object* v_res_6317_; 
v_reconfigure_boxed_6316_ = lean_unbox(v_reconfigure_6310_);
v_res_6317_ = l_Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3(v___y_6307_, v___y_6308_, v_leanOpts_6309_, v_reconfigure_boxed_6316_, v_a_6311_, v___y_6312_, v___y_6313_, v___y_6314_);
lean_dec_ref(v___y_6314_);
lean_dec(v___y_6312_);
lean_dec(v___y_6307_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v___y_6318_, lean_object* v___x_6319_, lean_object* v_as_6320_, size_t v_i_6321_, size_t v_stop_6322_, lean_object* v_b_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_){
_start:
{
uint8_t v___x_6327_; 
v___x_6327_ = lean_usize_dec_eq(v_i_6321_, v_stop_6322_);
if (v___x_6327_ == 0)
{
lean_object* v___x_6328_; lean_object* v___x_6329_; 
v___x_6328_ = lean_array_uget_borrowed(v_as_6320_, v_i_6321_);
lean_inc_ref(v___y_6318_);
lean_inc_ref(v___y_6325_);
lean_inc(v___x_6319_);
lean_inc(v___x_6328_);
v___x_6329_ = lean_apply_5(v___y_6318_, v___x_6328_, v___x_6319_, v___y_6324_, v___y_6325_, lean_box(0));
if (lean_obj_tag(v___x_6329_) == 0)
{
lean_object* v_a_6330_; lean_object* v_fst_6331_; lean_object* v_snd_6332_; size_t v___x_6333_; size_t v___x_6334_; 
v_a_6330_ = lean_ctor_get(v___x_6329_, 0);
lean_inc(v_a_6330_);
lean_dec_ref(v___x_6329_);
v_fst_6331_ = lean_ctor_get(v_a_6330_, 0);
lean_inc(v_fst_6331_);
v_snd_6332_ = lean_ctor_get(v_a_6330_, 1);
lean_inc(v_snd_6332_);
lean_dec(v_a_6330_);
v___x_6333_ = ((size_t)1ULL);
v___x_6334_ = lean_usize_add(v_i_6321_, v___x_6333_);
v_i_6321_ = v___x_6334_;
v_b_6323_ = v_fst_6331_;
v___y_6324_ = v_snd_6332_;
goto _start;
}
else
{
lean_dec(v___x_6319_);
lean_dec_ref(v___y_6318_);
return v___x_6329_;
}
}
else
{
lean_object* v___x_6336_; lean_object* v___x_6337_; 
lean_dec(v___x_6319_);
lean_dec_ref(v___y_6318_);
v___x_6336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6336_, 0, v_b_6323_);
lean_ctor_set(v___x_6336_, 1, v___y_6324_);
v___x_6337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6337_, 0, v___x_6336_);
return v___x_6337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v___y_6338_, lean_object* v___x_6339_, lean_object* v_as_6340_, lean_object* v_i_6341_, lean_object* v_stop_6342_, lean_object* v_b_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_){
_start:
{
size_t v_i_boxed_6347_; size_t v_stop_boxed_6348_; lean_object* v_res_6349_; 
v_i_boxed_6347_ = lean_unbox_usize(v_i_6341_);
lean_dec(v_i_6341_);
v_stop_boxed_6348_ = lean_unbox_usize(v_stop_6342_);
lean_dec(v_stop_6342_);
v_res_6349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6338_, v___x_6339_, v_as_6340_, v_i_boxed_6347_, v_stop_boxed_6348_, v_b_6343_, v___y_6344_, v___y_6345_);
lean_dec_ref(v___y_6345_);
lean_dec_ref(v_as_6340_);
return v_res_6349_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5(lean_object* v___y_6350_, lean_object* v___x_6351_, lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v_leanOpts_6354_, uint8_t v_reconfigure_6355_, lean_object* v_pkg_6356_, lean_object* v_a_6357_, lean_object* v_a_6358_, lean_object* v___y_6359_){
_start:
{
lean_object* v_packages_6361_; lean_object* v_depConfigs_6362_; lean_object* v___x_6363_; lean_object* v_snd_6365_; lean_object* v_packages_6366_; lean_object* v___y_6367_; lean_object* v_____x_6383_; lean_object* v___y_6384_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; uint8_t v___x_6390_; 
v_packages_6361_ = lean_ctor_get(v_a_6358_, 5);
v_depConfigs_6362_ = lean_ctor_get(v_pkg_6356_, 12);
lean_inc_ref(v_depConfigs_6362_);
v___x_6363_ = lean_array_get_size(v_packages_6361_);
v___x_6387_ = lean_array_get_size(v_depConfigs_6362_);
v___x_6388_ = lean_unsigned_to_nat(0u);
v___x_6389_ = lean_box(0);
v___x_6390_ = lean_nat_dec_le(v___x_6387_, v___x_6387_);
if (v___x_6390_ == 0)
{
uint8_t v___x_6391_; 
v___x_6391_ = lean_nat_dec_lt(v___x_6388_, v___x_6387_);
if (v___x_6391_ == 0)
{
uint8_t v___x_6392_; 
lean_dec_ref(v_depConfigs_6362_);
lean_dec_ref(v_pkg_6356_);
lean_dec_ref(v_leanOpts_6354_);
lean_dec_ref(v___y_6353_);
v___x_6392_ = lean_nat_dec_lt(v___x_6363_, v___x_6363_);
if (v___x_6392_ == 0)
{
lean_object* v___x_6393_; lean_object* v___x_6394_; 
lean_dec(v___x_6351_);
lean_dec_ref(v___y_6350_);
v___x_6393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6393_, 0, v___x_6389_);
lean_ctor_set(v___x_6393_, 1, v_a_6358_);
v___x_6394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6394_, 0, v___x_6393_);
return v___x_6394_;
}
else
{
uint8_t v___x_6395_; 
v___x_6395_ = lean_nat_dec_le(v___x_6363_, v___x_6363_);
if (v___x_6395_ == 0)
{
if (v___x_6392_ == 0)
{
lean_object* v___x_6396_; lean_object* v___x_6397_; 
lean_dec(v___x_6351_);
lean_dec_ref(v___y_6350_);
v___x_6396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6396_, 0, v___x_6389_);
lean_ctor_set(v___x_6396_, 1, v_a_6358_);
v___x_6397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6397_, 0, v___x_6396_);
return v___x_6397_;
}
else
{
size_t v___x_6398_; lean_object* v___x_6399_; 
lean_inc_ref(v_packages_6361_);
v___x_6398_ = lean_usize_of_nat(v___x_6363_);
v___x_6399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6350_, v___x_6351_, v_packages_6361_, v___x_6398_, v___x_6398_, v___x_6389_, v_a_6358_, v___y_6359_);
lean_dec_ref(v_packages_6361_);
return v___x_6399_;
}
}
else
{
size_t v___x_6400_; lean_object* v___x_6401_; 
lean_inc_ref(v_packages_6361_);
v___x_6400_ = lean_usize_of_nat(v___x_6363_);
v___x_6401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6350_, v___x_6351_, v_packages_6361_, v___x_6400_, v___x_6400_, v___x_6389_, v_a_6358_, v___y_6359_);
lean_dec_ref(v_packages_6361_);
return v___x_6401_;
}
}
}
else
{
size_t v___x_6402_; size_t v___x_6403_; lean_object* v___x_6404_; 
v___x_6402_ = lean_usize_of_nat(v___x_6387_);
v___x_6403_ = ((size_t)0ULL);
v___x_6404_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_6356_, v___y_6352_, v___y_6353_, v_leanOpts_6354_, v_reconfigure_6355_, v_depConfigs_6362_, v___x_6402_, v___x_6403_, v___x_6389_, v_a_6358_, v___y_6359_);
lean_dec_ref(v_depConfigs_6362_);
if (lean_obj_tag(v___x_6404_) == 0)
{
lean_object* v_a_6405_; 
v_a_6405_ = lean_ctor_get(v___x_6404_, 0);
lean_inc(v_a_6405_);
lean_dec_ref(v___x_6404_);
v_____x_6383_ = v_a_6405_;
v___y_6384_ = v___y_6359_;
goto v___jp_6382_;
}
else
{
lean_dec(v___x_6351_);
lean_dec_ref(v___y_6350_);
return v___x_6404_;
}
}
}
else
{
uint8_t v___x_6406_; 
v___x_6406_ = lean_nat_dec_lt(v___x_6388_, v___x_6387_);
if (v___x_6406_ == 0)
{
lean_inc_ref(v_packages_6361_);
lean_dec_ref(v_depConfigs_6362_);
lean_dec_ref(v_pkg_6356_);
lean_dec_ref(v_leanOpts_6354_);
lean_dec_ref(v___y_6353_);
v_snd_6365_ = v_a_6358_;
v_packages_6366_ = v_packages_6361_;
v___y_6367_ = v___y_6359_;
goto v___jp_6364_;
}
else
{
size_t v___x_6407_; size_t v___x_6408_; lean_object* v___x_6409_; 
v___x_6407_ = lean_usize_of_nat(v___x_6387_);
v___x_6408_ = ((size_t)0ULL);
v___x_6409_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0_spec__1___redArg(v_pkg_6356_, v___y_6352_, v___y_6353_, v_leanOpts_6354_, v_reconfigure_6355_, v_depConfigs_6362_, v___x_6407_, v___x_6408_, v___x_6389_, v_a_6358_, v___y_6359_);
lean_dec_ref(v_depConfigs_6362_);
if (lean_obj_tag(v___x_6409_) == 0)
{
lean_object* v_a_6410_; 
v_a_6410_ = lean_ctor_get(v___x_6409_, 0);
lean_inc(v_a_6410_);
lean_dec_ref(v___x_6409_);
v_____x_6383_ = v_a_6410_;
v___y_6384_ = v___y_6359_;
goto v___jp_6382_;
}
else
{
lean_dec(v___x_6351_);
lean_dec_ref(v___y_6350_);
return v___x_6409_;
}
}
}
v___jp_6364_:
{
lean_object* v___x_6368_; lean_object* v___x_6369_; uint8_t v___x_6370_; 
v___x_6368_ = lean_array_get_size(v_packages_6366_);
v___x_6369_ = lean_box(0);
v___x_6370_ = lean_nat_dec_lt(v___x_6363_, v___x_6368_);
if (v___x_6370_ == 0)
{
lean_object* v___x_6371_; lean_object* v___x_6372_; 
lean_dec_ref(v_packages_6366_);
lean_dec(v___x_6351_);
lean_dec_ref(v___y_6350_);
v___x_6371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6371_, 0, v___x_6369_);
lean_ctor_set(v___x_6371_, 1, v_snd_6365_);
v___x_6372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6372_, 0, v___x_6371_);
return v___x_6372_;
}
else
{
uint8_t v___x_6373_; 
v___x_6373_ = lean_nat_dec_le(v___x_6368_, v___x_6368_);
if (v___x_6373_ == 0)
{
if (v___x_6370_ == 0)
{
lean_object* v___x_6374_; lean_object* v___x_6375_; 
lean_dec_ref(v_packages_6366_);
lean_dec(v___x_6351_);
lean_dec_ref(v___y_6350_);
v___x_6374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6374_, 0, v___x_6369_);
lean_ctor_set(v___x_6374_, 1, v_snd_6365_);
v___x_6375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6375_, 0, v___x_6374_);
return v___x_6375_;
}
else
{
size_t v___x_6376_; size_t v___x_6377_; lean_object* v___x_6378_; 
v___x_6376_ = lean_usize_of_nat(v___x_6363_);
v___x_6377_ = lean_usize_of_nat(v___x_6368_);
v___x_6378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6350_, v___x_6351_, v_packages_6366_, v___x_6376_, v___x_6377_, v___x_6369_, v_snd_6365_, v___y_6367_);
lean_dec_ref(v_packages_6366_);
return v___x_6378_;
}
}
else
{
size_t v___x_6379_; size_t v___x_6380_; lean_object* v___x_6381_; 
v___x_6379_ = lean_usize_of_nat(v___x_6363_);
v___x_6380_ = lean_usize_of_nat(v___x_6368_);
v___x_6381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6350_, v___x_6351_, v_packages_6366_, v___x_6379_, v___x_6380_, v___x_6369_, v_snd_6365_, v___y_6367_);
lean_dec_ref(v_packages_6366_);
return v___x_6381_;
}
}
}
v___jp_6382_:
{
lean_object* v_snd_6385_; lean_object* v_packages_6386_; 
v_snd_6385_ = lean_ctor_get(v_____x_6383_, 1);
lean_inc(v_snd_6385_);
lean_dec_ref(v_____x_6383_);
v_packages_6386_ = lean_ctor_get(v_snd_6385_, 5);
lean_inc_ref(v_packages_6386_);
v_snd_6365_ = v_snd_6385_;
v_packages_6366_ = v_packages_6386_;
v___y_6367_ = v___y_6384_;
goto v___jp_6364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___boxed(lean_object* v___y_6411_, lean_object* v___x_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v_leanOpts_6415_, lean_object* v_reconfigure_6416_, lean_object* v_pkg_6417_, lean_object* v_a_6418_, lean_object* v_a_6419_, lean_object* v___y_6420_, lean_object* v___y_6421_){
_start:
{
uint8_t v_reconfigure_boxed_6422_; lean_object* v_res_6423_; 
v_reconfigure_boxed_6422_ = lean_unbox(v_reconfigure_6416_);
v_res_6423_ = l___private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5(v___y_6411_, v___x_6412_, v___y_6413_, v___y_6414_, v_leanOpts_6415_, v_reconfigure_boxed_6422_, v_pkg_6417_, v_a_6418_, v_a_6419_, v___y_6420_);
lean_dec_ref(v___y_6420_);
lean_dec(v_a_6418_);
lean_dec(v___y_6413_);
return v_res_6423_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6(lean_object* v_00_u03b1_6424_, lean_object* v_cycle_6425_, lean_object* v___y_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_){
_start:
{
lean_object* v___x_6430_; 
v___x_6430_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___redArg(v_cycle_6425_, v___y_6428_);
return v___x_6430_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b1_6431_, lean_object* v_cycle_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_){
_start:
{
lean_object* v_res_6437_; 
v_res_6437_ = l___private_Lake_Load_Resolve_0__Lake_depCycleError___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__6(v_00_u03b1_6431_, v_cycle_6432_, v___y_6433_, v___y_6434_, v___y_6435_);
lean_dec_ref(v___y_6435_);
lean_dec_ref(v___y_6434_);
lean_dec(v___y_6433_);
return v_res_6437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7(lean_object* v___y_6438_, lean_object* v___x_6439_, lean_object* v_as_6440_, size_t v_i_6441_, size_t v_stop_6442_, lean_object* v_b_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_){
_start:
{
lean_object* v___x_6448_; 
v___x_6448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___redArg(v___y_6438_, v___x_6439_, v_as_6440_, v_i_6441_, v_stop_6442_, v_b_6443_, v___y_6445_, v___y_6446_);
return v___x_6448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v___y_6449_, lean_object* v___x_6450_, lean_object* v_as_6451_, lean_object* v_i_6452_, lean_object* v_stop_6453_, lean_object* v_b_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_){
_start:
{
size_t v_i_boxed_6459_; size_t v_stop_boxed_6460_; lean_object* v_res_6461_; 
v_i_boxed_6459_ = lean_unbox_usize(v_i_6452_);
lean_dec(v_i_6452_);
v_stop_boxed_6460_ = lean_unbox_usize(v_stop_6453_);
lean_dec(v_stop_6453_);
v_res_6461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5_spec__7(v___y_6449_, v___x_6450_, v_as_6451_, v_i_boxed_6459_, v_stop_boxed_6460_, v_b_6454_, v___y_6455_, v___y_6456_, v___y_6457_);
lean_dec_ref(v___y_6457_);
lean_dec(v___y_6455_);
lean_dec_ref(v_as_6451_);
return v_res_6461_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7(lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v_leanOpts_6464_, uint8_t v_reconfigure_6465_, lean_object* v_inst_6466_, lean_object* v_a_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_){
_start:
{
lean_object* v___x_6472_; 
v___x_6472_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___redArg(v___y_6462_, v___y_6463_, v_leanOpts_6464_, v_reconfigure_6465_, v_a_6467_, v___y_6468_, v___y_6469_, v___y_6470_);
return v___x_6472_;
}
}
LEAN_EXPORT lean_object* l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7___boxed(lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v_leanOpts_6475_, lean_object* v_reconfigure_6476_, lean_object* v_inst_6477_, lean_object* v_a_6478_, lean_object* v___y_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_){
_start:
{
uint8_t v_reconfigure_boxed_6483_; lean_object* v_res_6484_; 
v_reconfigure_boxed_6483_ = lean_unbox(v_reconfigure_6476_);
v_res_6484_ = l_Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7(v___y_6473_, v___y_6474_, v_leanOpts_6475_, v_reconfigure_boxed_6483_, v_inst_6477_, v_a_6478_, v___y_6479_, v___y_6480_, v___y_6481_);
lean_dec_ref(v___y_6481_);
lean_dec(v___y_6479_);
lean_dec(v___y_6473_);
return v_res_6484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12(lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v_leanOpts_6487_, uint8_t v_reconfigure_6488_, lean_object* v___x_6489_, lean_object* v_as_6490_, size_t v_i_6491_, size_t v_stop_6492_, lean_object* v_b_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_){
_start:
{
lean_object* v___x_6498_; 
v___x_6498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___redArg(v___y_6485_, v___y_6486_, v_leanOpts_6487_, v_reconfigure_6488_, v___x_6489_, v_as_6490_, v_i_6491_, v_stop_6492_, v_b_6493_, v___y_6495_, v___y_6496_);
return v___x_6498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12___boxed(lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v_leanOpts_6501_, lean_object* v_reconfigure_6502_, lean_object* v___x_6503_, lean_object* v_as_6504_, lean_object* v_i_6505_, lean_object* v_stop_6506_, lean_object* v_b_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_){
_start:
{
uint8_t v_reconfigure_boxed_6512_; size_t v_i_boxed_6513_; size_t v_stop_boxed_6514_; lean_object* v_res_6515_; 
v_reconfigure_boxed_6512_ = lean_unbox(v_reconfigure_6502_);
v_i_boxed_6513_ = lean_unbox_usize(v_i_6505_);
lean_dec(v_i_6505_);
v_stop_boxed_6514_ = lean_unbox_usize(v_stop_6506_);
lean_dec(v_stop_6506_);
v_res_6515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_resolveDepsCore_go___at___00Lake_Workspace_materializeDeps_spec__0___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__5___at___00Lake_recFetch___at___00Lake_recFetchAcyclic___at___00__private_Lake_Load_Resolve_0__Lake_Workspace_runResolveT___at___00Lake_Workspace_materializeDeps_spec__1_spec__3_spec__7_spec__12_spec__12(v___y_6499_, v___y_6500_, v_leanOpts_6501_, v_reconfigure_boxed_6512_, v___x_6503_, v_as_6504_, v_i_boxed_6513_, v_stop_boxed_6514_, v_b_6507_, v___y_6508_, v___y_6509_, v___y_6510_);
lean_dec_ref(v___y_6510_);
lean_dec(v___y_6508_);
lean_dec_ref(v_as_6504_);
lean_dec(v___x_6503_);
lean_dec(v___y_6499_);
return v_res_6515_;
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

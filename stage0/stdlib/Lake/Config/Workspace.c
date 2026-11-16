// Lean compiler output
// Module: Lake.Config.Workspace
// Imports: public import Lake.Config.Env public import Lake.Config.LeanExe public import Lake.Config.ExternLib public import Lake.Config.FacetConfig public import Lake.Config.TargetConfig public import Lake.Config.LakeConfig meta import Lake.Util.OpaqueType import Lean.DocString.Syntax import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Lemmas
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lake_Package_findModuleBySrc_x3f(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lake_Package_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetConfig_x3f(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Package_clean(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t l_Lake_Package_isLocalModule(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_get_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lake_Package_isBuildableModule(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Env_leanPath(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSrcPath(lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* l_Lake_Env_path(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_string_object l_Lake_computeLakeCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_computeLakeCache___closed__0 = (const lean_object*)&l_Lake_computeLakeCache___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_computeLakeCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeLakeCache___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk___boxed(lean_object*);
static const lean_closure_object l_Lake_OpaqueWorkspace_instCoeMk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OpaqueWorkspace_instCoeMk___closed__0 = (const lean_object*)&l_Lake_OpaqueWorkspace_instCoeMk___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_OpaqueWorkspace_instCoeMk = (const lean_object*)&l_Lake_OpaqueWorkspace_instCoeMk___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet___boxed(lean_object*);
static const lean_closure_object l_Lake_OpaqueWorkspace_instCoeGet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_OpaqueWorkspace_instCoeGet___closed__0 = (const lean_object*)&l_Lake_OpaqueWorkspace_instCoeGet___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_OpaqueWorkspace_instCoeGet = (const lean_object*)&l_Lake_OpaqueWorkspace_instCoeGet___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace___boxed(lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Package_defaultTargetRoots___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_defaultTargetRoots___closed__0 = (const lean_object*)&l_Lake_Package_defaultTargetRoots___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_root(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_root___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___redArg();
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_enableArtifactCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheWritable___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheEnabled___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Workspace_findCacheService_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__0 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__0_value;
static const lean_closure_object l_Lake_Workspace_findCacheService_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__1 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__1_value;
static const lean_closure_object l_Lake_Workspace_findCacheService_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__2 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__2_value;
static const lean_closure_object l_Lake_Workspace_findCacheService_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__3 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__3_value;
static const lean_closure_object l_Lake_Workspace_findCacheService_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__4 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__4_value;
static const lean_closure_object l_Lake_Workspace_findCacheService_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__5 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__5_value;
static const lean_closure_object l_Lake_Workspace_findCacheService_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__6 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__6_value;
static const lean_ctor_object l_Lake_Workspace_findCacheService_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__0_value),((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__1_value)}};
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__7 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__7_value;
static const lean_ctor_object l_Lake_Workspace_findCacheService_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__7_value),((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__2_value),((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__3_value),((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__4_value),((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__5_value)}};
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__8 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__8_value;
static const lean_ctor_object l_Lake_Workspace_findCacheService_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__8_value),((lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__6_value)}};
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__9 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__9_value;
static const lean_ctor_object l_Lake_Workspace_findCacheService_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Workspace_findCacheService_x3f___closed__10 = (const lean_object*)&l_Lake_Workspace_findCacheService_x3f___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile___boxed(lean_object*);
static const lean_string_object l_Lake_Workspace_packageOverridesFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "package-overrides.json"};
static const lean_object* l_Lake_Workspace_packageOverridesFile___closed__0 = (const lean_object*)&l_Lake_Workspace_packageOverridesFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile___boxed(lean_object*);
static const lean_closure_object l_Lake_Workspace_addPackage_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_addPackage_x27___redArg___closed__0 = (const lean_object*)&l_Lake_Workspace_addPackage_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Workspace_addPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Workspace_addPackage___closed__0 = (const lean_object*)&l_Lake_Workspace_addPackage___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Workspace_findPackageByName_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__0 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object*);
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0___closed__0 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__0___closed__0_value;
static const lean_ctor_object l_Lake_Workspace_augmentedEnvVars___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__0___closed__0_value)}};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0___closed__1 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0___boxed(lean_object*);
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___closed__0 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__1___closed__0_value;
static const lean_ctor_object l_Lake_Workspace_augmentedEnvVars___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__1___closed__0_value)}};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___closed__1 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__1___closed__1_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___closed__2 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__1___closed__2_value;
static const lean_ctor_object l_Lake_Workspace_augmentedEnvVars___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__1___closed__2_value)}};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___closed__3 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___boxed(lean_object*);
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LAKE_CACHE_DIR"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__0 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__0_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__1 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__1_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__2 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__2_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LEAN_SRC_PATH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__3 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__3_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_GITHASH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__4 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__4_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LAKE_ARTIFACT_CACHE"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__5 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__5_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LAKE_RESTORE_ARTIFACTS"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__6 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeLakeCache(lean_object* v_pkg_2_, lean_object* v_lakeEnv_3_){
_start:
{
lean_object* v_config_4_; uint8_t v_bootstrap_5_; 
v_config_4_ = lean_ctor_get(v_pkg_2_, 6);
v_bootstrap_5_ = lean_ctor_get_uint8(v_config_4_, sizeof(void*)*28);
if (v_bootstrap_5_ == 0)
{
lean_object* v_lakeCache_x3f_6_; 
v_lakeCache_x3f_6_ = lean_ctor_get(v_lakeEnv_3_, 8);
if (lean_obj_tag(v_lakeCache_x3f_6_) == 0)
{
lean_object* v_dir_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_dir_7_ = lean_ctor_get(v_pkg_2_, 4);
lean_inc_ref(v_dir_7_);
lean_dec_ref(v_pkg_2_);
v___x_8_ = l_Lake_defaultLakeDir;
v___x_9_ = l_Lake_joinRelative(v_dir_7_, v___x_8_);
v___x_10_ = ((lean_object*)(l_Lake_computeLakeCache___closed__0));
v___x_11_ = l_Lake_joinRelative(v___x_9_, v___x_10_);
return v___x_11_;
}
else
{
lean_object* v_val_12_; 
lean_dec_ref(v_pkg_2_);
v_val_12_ = lean_ctor_get(v_lakeCache_x3f_6_, 0);
lean_inc(v_val_12_);
return v_val_12_;
}
}
else
{
lean_object* v_lakeSystemCache_x3f_13_; 
v_lakeSystemCache_x3f_13_ = lean_ctor_get(v_lakeEnv_3_, 9);
if (lean_obj_tag(v_lakeSystemCache_x3f_13_) == 0)
{
lean_object* v_dir_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_dir_14_ = lean_ctor_get(v_pkg_2_, 4);
lean_inc_ref(v_dir_14_);
lean_dec_ref(v_pkg_2_);
v___x_15_ = l_Lake_defaultLakeDir;
v___x_16_ = l_Lake_joinRelative(v_dir_14_, v___x_15_);
v___x_17_ = ((lean_object*)(l_Lake_computeLakeCache___closed__0));
v___x_18_ = l_Lake_joinRelative(v___x_16_, v___x_17_);
return v___x_18_;
}
else
{
lean_object* v_val_19_; 
lean_dec_ref(v_pkg_2_);
v_val_19_ = lean_ctor_get(v_lakeSystemCache_x3f_13_, 0);
lean_inc(v_val_19_);
return v_val_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeLakeCache___boxed(lean_object* v_pkg_20_, lean_object* v_lakeEnv_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lake_computeLakeCache(v_pkg_20_, v_lakeEnv_21_);
lean_dec_ref(v_lakeEnv_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(lean_object* v_a_23_){
_start:
{
lean_inc_ref(v_a_23_);
return v_a_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk___boxed(lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(v_a_24_);
lean_dec_ref(v_a_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(lean_object* v_a_28_){
_start:
{
lean_inc(v_a_28_);
return v_a_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet___boxed(lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(v_a_29_);
lean_dec(v_a_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(lean_object* v_inst_33_){
_start:
{
lean_inc_ref(v_inst_33_);
return v_inst_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace___boxed(lean_object* v_inst_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(v_inst_34_);
lean_dec_ref(v_inst_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(lean_object* v_self_41_, lean_object* v_as_42_, size_t v_i_43_, size_t v_stop_44_, lean_object* v_b_45_){
_start:
{
lean_object* v___y_47_; uint8_t v___x_54_; 
v___x_54_ = lean_usize_dec_eq(v_i_43_, v_stop_44_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_68_; 
v___x_55_ = lean_array_uget_borrowed(v_as_42_, v_i_43_);
v___x_68_ = l_Lake_Package_findTargetDecl_x3f(v___x_55_, v_self_41_);
if (lean_obj_tag(v___x_68_) == 0)
{
goto v___jp_56_;
}
else
{
lean_object* v_val_69_; lean_object* v_kind_70_; lean_object* v_config_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_val_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_val_69_);
lean_dec_ref_known(v___x_68_, 1);
v_kind_70_ = lean_ctor_get(v_val_69_, 2);
lean_inc(v_kind_70_);
v_config_71_ = lean_ctor_get(v_val_69_, 3);
lean_inc(v_config_71_);
lean_dec(v_val_69_);
v___x_72_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_73_ = lean_name_eq(v_kind_70_, v___x_72_);
lean_dec(v_kind_70_);
if (v___x_73_ == 0)
{
lean_dec(v_config_71_);
goto v___jp_56_;
}
else
{
lean_object* v_roots_74_; lean_object* v___x_75_; 
v_roots_74_ = lean_ctor_get(v_config_71_, 2);
lean_inc_ref(v_roots_74_);
lean_dec(v_config_71_);
v___x_75_ = l_Array_append___redArg(v_b_45_, v_roots_74_);
lean_dec_ref(v_roots_74_);
v___y_47_ = v___x_75_;
goto v___jp_46_;
}
}
v___jp_56_:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lake_Package_findTargetDecl_x3f(v___x_55_, v_self_41_);
if (lean_obj_tag(v___x_57_) == 0)
{
goto v___jp_51_;
}
else
{
lean_object* v_val_58_; lean_object* v_kind_59_; lean_object* v_config_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_val_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_val_58_);
lean_dec_ref_known(v___x_57_, 1);
v_kind_59_ = lean_ctor_get(v_val_58_, 2);
lean_inc(v_kind_59_);
v_config_60_ = lean_ctor_get(v_val_58_, 3);
lean_inc(v_config_60_);
lean_dec(v_val_58_);
v___x_61_ = l_Lake_LeanExe_keyword;
v___x_62_ = lean_name_eq(v_kind_59_, v___x_61_);
lean_dec(v_kind_59_);
if (v___x_62_ == 0)
{
lean_dec(v_config_60_);
goto v___jp_51_;
}
else
{
lean_object* v_root_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_root_63_ = lean_ctor_get(v_config_60_, 2);
lean_inc(v_root_63_);
lean_dec(v_config_60_);
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_mk_empty_array_with_capacity(v___x_64_);
v___x_66_ = lean_array_push(v___x_65_, v_root_63_);
v___x_67_ = l_Array_append___redArg(v_b_45_, v___x_66_);
lean_dec_ref(v___x_66_);
v___y_47_ = v___x_67_;
goto v___jp_46_;
}
}
}
}
else
{
return v_b_45_;
}
v___jp_46_:
{
size_t v___x_48_; size_t v___x_49_; 
v___x_48_ = ((size_t)1ULL);
v___x_49_ = lean_usize_add(v_i_43_, v___x_48_);
v_i_43_ = v___x_49_;
v_b_45_ = v___y_47_;
goto _start;
}
v___jp_51_:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0));
v___x_53_ = l_Array_append___redArg(v_b_45_, v___x_52_);
v___y_47_ = v___x_53_;
goto v___jp_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___boxed(lean_object* v_self_76_, lean_object* v_as_77_, lean_object* v_i_78_, lean_object* v_stop_79_, lean_object* v_b_80_){
_start:
{
size_t v_i_boxed_81_; size_t v_stop_boxed_82_; lean_object* v_res_83_; 
v_i_boxed_81_ = lean_unbox_usize(v_i_78_);
lean_dec(v_i_78_);
v_stop_boxed_82_ = lean_unbox_usize(v_stop_79_);
lean_dec(v_stop_79_);
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_76_, v_as_77_, v_i_boxed_81_, v_stop_boxed_82_, v_b_80_);
lean_dec_ref(v_as_77_);
lean_dec_ref(v_self_76_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots(lean_object* v_self_86_){
_start:
{
lean_object* v_defaultTargets_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_defaultTargets_87_ = lean_ctor_get(v_self_86_, 17);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = ((lean_object*)(l_Lake_Package_defaultTargetRoots___closed__0));
v___x_90_ = lean_array_get_size(v_defaultTargets_87_);
v___x_91_ = lean_nat_dec_lt(v___x_88_, v___x_90_);
if (v___x_91_ == 0)
{
return v___x_89_;
}
else
{
size_t v___x_92_; size_t v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_90_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_86_, v_defaultTargets_87_, v___x_92_, v___x_93_, v___x_89_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots___boxed(lean_object* v_self_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lake_Package_defaultTargetRoots(v_self_95_);
lean_dec_ref(v_self_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_root(lean_object* v_self_97_){
_start:
{
lean_object* v_packages_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_packages_98_ = lean_ctor_get(v_self_97_, 4);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_array_fget_borrowed(v_packages_98_, v___x_99_);
lean_inc(v___x_100_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_root___boxed(lean_object* v_self_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lake_Workspace_root(v_self_101_);
lean_dec_ref(v_self_101_);
return v_res_102_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(lean_object* v_self_103_){
_start:
{
lean_object* v_packages_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_config_107_; uint8_t v_bootstrap_108_; 
v_packages_104_ = lean_ctor_get(v_self_103_, 4);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_array_fget_borrowed(v_packages_104_, v___x_105_);
v_config_107_ = lean_ctor_get(v___x_106_, 6);
v_bootstrap_108_ = lean_ctor_get_uint8(v_config_107_, sizeof(void*)*28);
return v_bootstrap_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(lean_object* v_self_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(v_self_109_);
lean_dec_ref(v_self_109_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object* v_self_112_){
_start:
{
lean_object* v_packages_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_dir_116_; 
v_packages_113_ = lean_ctor_get(v_self_112_, 4);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_array_fget_borrowed(v_packages_113_, v___x_114_);
v_dir_116_ = lean_ctor_get(v___x_115_, 4);
lean_inc_ref(v_dir_116_);
return v_dir_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object* v_self_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lake_Workspace_dir(v_self_117_);
lean_dec_ref(v_self_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object* v_self_119_){
_start:
{
lean_object* v_packages_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_config_123_; lean_object* v_toWorkspaceConfig_124_; 
v_packages_120_ = lean_ctor_get(v_self_119_, 4);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_array_fget_borrowed(v_packages_120_, v___x_121_);
v_config_123_ = lean_ctor_get(v___x_122_, 6);
v_toWorkspaceConfig_124_ = lean_ctor_get(v_config_123_, 0);
lean_inc_ref(v_toWorkspaceConfig_124_);
return v_toWorkspaceConfig_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object* v_self_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lake_Workspace_config(v_self_125_);
lean_dec_ref(v_self_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___redArg(){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lake_defaultLakeDir;
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___redArg___boxed(lean_object* v___dummy_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lake_Workspace_relLakeDir___redArg();
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object* v_self_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lake_defaultLakeDir;
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object* v_self_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lake_Workspace_relLakeDir(v_self_133_);
lean_dec_ref(v_self_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object* v_self_135_){
_start:
{
lean_object* v_packages_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_dir_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_packages_136_ = lean_ctor_get(v_self_135_, 4);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_fget_borrowed(v_packages_136_, v___x_137_);
v_dir_139_ = lean_ctor_get(v___x_138_, 4);
v___x_140_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_139_);
v___x_141_ = l_Lake_joinRelative(v_dir_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir___boxed(lean_object* v_self_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lake_Workspace_lakeDir(v_self_142_);
lean_dec_ref(v_self_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f(lean_object* v_ws_144_){
_start:
{
lean_object* v_lakeEnv_145_; lean_object* v_enableArtifactCache_x3f_146_; 
v_lakeEnv_145_ = lean_ctor_get(v_ws_144_, 0);
v_enableArtifactCache_x3f_146_ = lean_ctor_get(v_lakeEnv_145_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_146_) == 0)
{
lean_object* v_packages_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_config_150_; lean_object* v_enableArtifactCache_x3f_151_; 
v_packages_147_ = lean_ctor_get(v_ws_144_, 4);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_array_fget_borrowed(v_packages_147_, v___x_148_);
v_config_150_ = lean_ctor_get(v___x_149_, 6);
v_enableArtifactCache_x3f_151_ = lean_ctor_get(v_config_150_, 24);
lean_inc(v_enableArtifactCache_x3f_151_);
return v_enableArtifactCache_x3f_151_;
}
else
{
lean_inc_ref(v_enableArtifactCache_x3f_146_);
return v_enableArtifactCache_x3f_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f___boxed(lean_object* v_ws_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lake_Workspace_enableArtifactCache_x3f(v_ws_152_);
lean_dec_ref(v_ws_152_);
return v_res_153_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_enableArtifactCache(lean_object* v_ws_154_){
_start:
{
lean_object* v_lakeEnv_155_; lean_object* v_enableArtifactCache_x3f_156_; 
v_lakeEnv_155_ = lean_ctor_get(v_ws_154_, 0);
v_enableArtifactCache_x3f_156_ = lean_ctor_get(v_lakeEnv_155_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_156_) == 0)
{
lean_object* v_packages_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_config_160_; lean_object* v_enableArtifactCache_x3f_161_; 
v_packages_157_ = lean_ctor_get(v_ws_154_, 4);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_array_fget_borrowed(v_packages_157_, v___x_158_);
v_config_160_ = lean_ctor_get(v___x_159_, 6);
v_enableArtifactCache_x3f_161_ = lean_ctor_get(v_config_160_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_161_) == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
else
{
lean_object* v_val_163_; uint8_t v___x_164_; 
v_val_163_ = lean_ctor_get(v_enableArtifactCache_x3f_161_, 0);
v___x_164_ = lean_unbox(v_val_163_);
return v___x_164_;
}
}
else
{
lean_object* v_val_165_; uint8_t v___x_166_; 
v_val_165_ = lean_ctor_get(v_enableArtifactCache_x3f_156_, 0);
v___x_166_ = lean_unbox(v_val_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache___boxed(lean_object* v_ws_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lake_Workspace_enableArtifactCache(v_ws_167_);
lean_dec_ref(v_ws_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object* v_ws_170_){
_start:
{
lean_object* v_lakeEnv_171_; lean_object* v_enableArtifactCache_x3f_172_; 
v_lakeEnv_171_ = lean_ctor_get(v_ws_170_, 0);
v_enableArtifactCache_x3f_172_ = lean_ctor_get(v_lakeEnv_171_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_172_) == 0)
{
lean_object* v_packages_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_config_176_; lean_object* v_enableArtifactCache_x3f_177_; 
v_packages_173_ = lean_ctor_get(v_ws_170_, 4);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_array_fget_borrowed(v_packages_173_, v___x_174_);
v_config_176_ = lean_ctor_get(v___x_175_, 6);
v_enableArtifactCache_x3f_177_ = lean_ctor_get(v_config_176_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_177_) == 0)
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
else
{
lean_object* v_val_179_; uint8_t v___x_180_; 
v_val_179_ = lean_ctor_get(v_enableArtifactCache_x3f_177_, 0);
v___x_180_ = lean_unbox(v_val_179_);
return v___x_180_;
}
}
else
{
lean_object* v_val_181_; uint8_t v___x_182_; 
v_val_181_ = lean_ctor_get(v_enableArtifactCache_x3f_172_, 0);
v___x_182_ = lean_unbox(v_val_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheWritable___boxed(lean_object* v_ws_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_183_);
lean_dec_ref(v_ws_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheEnabled(lean_object* v_ws_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheEnabled___boxed(lean_object* v_ws_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lake_Workspace_isRootArtifactCacheEnabled(v_ws_188_);
lean_dec_ref(v_ws_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f(lean_object* v_ws_191_){
_start:
{
lean_object* v_lakeEnv_192_; lean_object* v_restoreAllArtifacts_x3f_193_; 
v_lakeEnv_192_ = lean_ctor_get(v_ws_191_, 0);
v_restoreAllArtifacts_x3f_193_ = lean_ctor_get(v_lakeEnv_192_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_193_) == 0)
{
lean_object* v_packages_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_config_197_; lean_object* v_restoreAllArtifacts_x3f_198_; 
v_packages_194_ = lean_ctor_get(v_ws_191_, 4);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_array_fget_borrowed(v_packages_194_, v___x_195_);
v_config_197_ = lean_ctor_get(v___x_196_, 6);
v_restoreAllArtifacts_x3f_198_ = lean_ctor_get(v_config_197_, 25);
lean_inc(v_restoreAllArtifacts_x3f_198_);
return v_restoreAllArtifacts_x3f_198_;
}
else
{
lean_inc_ref(v_restoreAllArtifacts_x3f_193_);
return v_restoreAllArtifacts_x3f_193_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(lean_object* v_ws_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_Workspace_restoreAllArtifacts_x3f(v_ws_199_);
lean_dec_ref(v_ws_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain(lean_object* v_ws_201_){
_start:
{
lean_object* v_lakeEnv_202_; lean_object* v_toolchain_203_; 
v_lakeEnv_202_ = lean_ctor_get(v_ws_201_, 0);
v_toolchain_203_ = lean_ctor_get(v_lakeEnv_202_, 19);
lean_inc_ref(v_toolchain_203_);
return v_toolchain_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain___boxed(lean_object* v_ws_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lake_Workspace_cacheToolchain(v_ws_204_);
lean_dec_ref(v_ws_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService(lean_object* v_ws_206_){
_start:
{
lean_object* v_lakeConfig_207_; lean_object* v_defaultCacheService_208_; 
v_lakeConfig_207_ = lean_ctor_get(v_ws_206_, 1);
v_defaultCacheService_208_ = lean_ctor_get(v_lakeConfig_207_, 1);
lean_inc_ref(v_defaultCacheService_208_);
return v_defaultCacheService_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService___boxed(lean_object* v_ws_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_Workspace_defaultCacheService(v_ws_209_);
lean_dec_ref(v_ws_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f(lean_object* v_ws_211_){
_start:
{
lean_object* v_lakeConfig_212_; lean_object* v_defaultCacheUploadService_x3f_213_; 
v_lakeConfig_212_ = lean_ctor_get(v_ws_211_, 1);
v_defaultCacheUploadService_x3f_213_ = lean_ctor_get(v_lakeConfig_212_, 2);
lean_inc(v_defaultCacheUploadService_x3f_213_);
return v_defaultCacheUploadService_x3f_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(lean_object* v_ws_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lake_Workspace_defaultCacheUploadService_x3f(v_ws_214_);
lean_dec_ref(v_ws_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___lam__0(lean_object* v___x_216_, lean_object* v___x_217_, lean_object* v___x_218_, lean_object* v_a_219_, lean_object* v_x_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_cacheServices_222_; lean_object* v___x_223_; 
v_cacheServices_222_ = lean_ctor_get(v_a_219_, 18);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_222_, v___x_216_);
if (lean_obj_tag(v___x_223_) == 1)
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v___x_218_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_217_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; 
lean_dec(v___x_223_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_218_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___lam__0___boxed(lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v___x_230_, lean_object* v_a_231_, lean_object* v_x_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lake_Workspace_findCacheService_x3f___lam__0(v___x_228_, v___x_229_, v___x_230_, v_a_231_, v_x_232_, v___y_233_);
lean_dec_ref(v___y_233_);
lean_dec_ref(v_a_231_);
lean_dec(v___x_228_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object* v_ws_257_, lean_object* v_service_258_){
_start:
{
lean_object* v_lakeConfig_259_; lean_object* v_packages_260_; lean_object* v_cacheServices_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_lakeConfig_259_ = lean_ctor_get(v_ws_257_, 1);
lean_inc_ref(v_lakeConfig_259_);
v_packages_260_ = lean_ctor_get(v_ws_257_, 4);
lean_inc_ref(v_packages_260_);
lean_dec_ref(v_ws_257_);
v_cacheServices_261_ = lean_ctor_get(v_lakeConfig_259_, 3);
lean_inc(v_cacheServices_261_);
lean_dec_ref(v_lakeConfig_259_);
v___x_262_ = lean_box(0);
v___x_263_ = l_Lean_Name_str___override(v___x_262_, v_service_258_);
v___x_264_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_261_, v___x_263_);
lean_dec(v_cacheServices_261_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___f_268_; size_t v_sz_269_; size_t v___x_270_; lean_object* v___x_271_; lean_object* v_fst_272_; 
v___x_265_ = ((lean_object*)(l_Lake_Workspace_findCacheService_x3f___closed__9));
v___x_266_ = lean_box(0);
v___x_267_ = ((lean_object*)(l_Lake_Workspace_findCacheService_x3f___closed__10));
v___f_268_ = lean_alloc_closure((void*)(l_Lake_Workspace_findCacheService_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_268_, 0, v___x_263_);
lean_closure_set(v___f_268_, 1, v___x_266_);
lean_closure_set(v___f_268_, 2, v___x_267_);
v_sz_269_ = lean_array_size(v_packages_260_);
v___x_270_ = ((size_t)0ULL);
v___x_271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_265_, v_packages_260_, v___f_268_, v_sz_269_, v___x_270_, v___x_267_);
v_fst_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_fst_272_);
lean_dec(v___x_271_);
if (lean_obj_tag(v_fst_272_) == 0)
{
return v___x_264_;
}
else
{
lean_object* v_val_273_; 
v_val_273_ = lean_ctor_get(v_fst_272_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v_fst_272_, 1);
return v_val_273_;
}
}
else
{
lean_dec(v___x_263_);
lean_dec_ref(v_packages_260_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* v_self_274_){
_start:
{
lean_object* v_packages_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_config_278_; lean_object* v_toWorkspaceConfig_279_; lean_object* v___x_280_; 
v_packages_275_ = lean_ctor_get(v_self_274_, 4);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_array_fget_borrowed(v_packages_275_, v___x_276_);
v_config_278_ = lean_ctor_get(v___x_277_, 6);
v_toWorkspaceConfig_279_ = lean_ctor_get(v_config_278_, 0);
lean_inc_ref(v_toWorkspaceConfig_279_);
v___x_280_ = l_System_FilePath_normalize(v_toWorkspaceConfig_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir___boxed(lean_object* v_self_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lake_Workspace_relPkgsDir(v_self_281_);
lean_dec_ref(v_self_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* v_self_283_){
_start:
{
lean_object* v_packages_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_config_287_; lean_object* v_dir_288_; lean_object* v_toWorkspaceConfig_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_packages_284_ = lean_ctor_get(v_self_283_, 4);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_array_fget_borrowed(v_packages_284_, v___x_285_);
v_config_287_ = lean_ctor_get(v___x_286_, 6);
v_dir_288_ = lean_ctor_get(v___x_286_, 4);
v_toWorkspaceConfig_289_ = lean_ctor_get(v_config_287_, 0);
lean_inc_ref(v_toWorkspaceConfig_289_);
v___x_290_ = l_System_FilePath_normalize(v_toWorkspaceConfig_289_);
lean_inc_ref(v_dir_288_);
v___x_291_ = l_Lake_joinRelative(v_dir_288_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir___boxed(lean_object* v_self_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lake_Workspace_pkgsDir(v_self_292_);
lean_dec_ref(v_self_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object* v_self_294_){
_start:
{
lean_object* v_packages_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_config_298_; lean_object* v_toLeanConfig_299_; lean_object* v_moreLeanArgs_300_; 
v_packages_295_ = lean_ctor_get(v_self_294_, 4);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_array_fget_borrowed(v_packages_295_, v___x_296_);
v_config_298_ = lean_ctor_get(v___x_297_, 6);
v_toLeanConfig_299_ = lean_ctor_get(v_config_298_, 1);
v_moreLeanArgs_300_ = lean_ctor_get(v_toLeanConfig_299_, 1);
lean_inc_ref(v_moreLeanArgs_300_);
return v_moreLeanArgs_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object* v_self_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lake_Workspace_leanArgs(v_self_301_);
lean_dec_ref(v_self_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* v_self_303_){
_start:
{
lean_object* v_packages_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_config_307_; lean_object* v_toLeanConfig_308_; lean_object* v_leanOptions_309_; lean_object* v___x_310_; 
v_packages_304_ = lean_ctor_get(v_self_303_, 4);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_array_fget_borrowed(v_packages_304_, v___x_305_);
v_config_307_ = lean_ctor_get(v___x_306_, 6);
v_toLeanConfig_308_ = lean_ctor_get(v_config_307_, 1);
v_leanOptions_309_ = lean_ctor_get(v_toLeanConfig_308_, 0);
v___x_310_ = l_Lean_LeanOptions_ofArray(v_leanOptions_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* v_self_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lake_Workspace_leanOptions(v_self_311_);
lean_dec_ref(v_self_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* v_self_313_){
_start:
{
lean_object* v_packages_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_config_317_; lean_object* v_toLeanConfig_318_; lean_object* v_leanOptions_319_; lean_object* v_moreServerOptions_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_packages_314_ = lean_ctor_get(v_self_313_, 4);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_array_fget_borrowed(v_packages_314_, v___x_315_);
v_config_317_ = lean_ctor_get(v___x_316_, 6);
v_toLeanConfig_318_ = lean_ctor_get(v_config_317_, 1);
v_leanOptions_319_ = lean_ctor_get(v_toLeanConfig_318_, 0);
v_moreServerOptions_320_ = lean_ctor_get(v_toLeanConfig_318_, 4);
v___x_321_ = l_Lean_LeanOptions_ofArray(v_leanOptions_319_);
v___x_322_ = l_Lean_LeanOptions_appendArray(v___x_321_, v_moreServerOptions_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* v_self_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lake_Workspace_serverOptions(v_self_323_);
lean_dec_ref(v_self_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object* v_self_325_){
_start:
{
lean_object* v_packages_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_packages_326_ = lean_ctor_get(v_self_325_, 4);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_fget_borrowed(v_packages_326_, v___x_327_);
v___x_329_ = l_Lake_Package_defaultTargetRoots(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object* v_self_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lake_Workspace_defaultTargetRoots(v_self_330_);
lean_dec_ref(v_self_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* v_self_332_){
_start:
{
lean_object* v_packages_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v_dir_336_; lean_object* v_relManifestFile_337_; lean_object* v___x_338_; 
v_packages_333_ = lean_ctor_get(v_self_332_, 4);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_array_fget_borrowed(v_packages_333_, v___x_334_);
v_dir_336_ = lean_ctor_get(v___x_335_, 4);
v_relManifestFile_337_ = lean_ctor_get(v___x_335_, 9);
lean_inc_ref(v_relManifestFile_337_);
lean_inc_ref(v_dir_336_);
v___x_338_ = l_Lake_joinRelative(v_dir_336_, v_relManifestFile_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile___boxed(lean_object* v_self_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lake_Workspace_manifestFile(v_self_339_);
lean_dec_ref(v_self_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* v_self_342_){
_start:
{
lean_object* v_packages_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_dir_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_packages_343_ = lean_ctor_get(v_self_342_, 4);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_array_fget_borrowed(v_packages_343_, v___x_344_);
v_dir_346_ = lean_ctor_get(v___x_345_, 4);
v___x_347_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_346_);
v___x_348_ = l_Lake_joinRelative(v_dir_346_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lake_Workspace_packageOverridesFile___closed__0));
v___x_350_ = l_Lake_joinRelative(v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile___boxed(lean_object* v_self_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lake_Workspace_packageOverridesFile(v_self_351_);
lean_dec_ref(v_self_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object* v_pkg_354_, lean_object* v_self_355_){
_start:
{
lean_object* v_lakeEnv_356_; lean_object* v_lakeConfig_357_; lean_object* v_lakeCache_358_; lean_object* v_lakeArgs_x3f_359_; lean_object* v_packages_360_; lean_object* v_packageMap_361_; lean_object* v_facetConfigs_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_373_; 
v_lakeEnv_356_ = lean_ctor_get(v_self_355_, 0);
v_lakeConfig_357_ = lean_ctor_get(v_self_355_, 1);
v_lakeCache_358_ = lean_ctor_get(v_self_355_, 2);
v_lakeArgs_x3f_359_ = lean_ctor_get(v_self_355_, 3);
v_packages_360_ = lean_ctor_get(v_self_355_, 4);
v_packageMap_361_ = lean_ctor_get(v_self_355_, 5);
v_facetConfigs_362_ = lean_ctor_get(v_self_355_, 6);
v_isSharedCheck_373_ = !lean_is_exclusive(v_self_355_);
if (v_isSharedCheck_373_ == 0)
{
v___x_364_ = v_self_355_;
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_facetConfigs_362_);
lean_inc(v_packageMap_361_);
lean_inc(v_packages_360_);
lean_inc(v_lakeArgs_x3f_359_);
lean_inc(v_lakeCache_358_);
lean_inc(v_lakeConfig_357_);
lean_inc(v_lakeEnv_356_);
lean_dec(v_self_355_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_373_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_keyName_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v_keyName_366_ = lean_ctor_get(v_pkg_354_, 2);
lean_inc(v_keyName_366_);
lean_inc_ref(v_pkg_354_);
v___x_367_ = lean_array_push(v_packages_360_, v_pkg_354_);
v___x_368_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_369_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_368_, v_keyName_366_, v_pkg_354_, v_packageMap_361_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 5, v___x_369_);
lean_ctor_set(v___x_364_, 4, v___x_367_);
v___x_371_ = v___x_364_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_lakeEnv_356_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_lakeConfig_357_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_lakeCache_358_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_lakeArgs_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_facetConfigs_362_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object* v_pkg_374_, lean_object* v_self_375_, lean_object* v_h__wsIdx_376_, lean_object* v_h__depIdxs_377_){
_start:
{
lean_object* v_lakeEnv_378_; lean_object* v_lakeConfig_379_; lean_object* v_lakeCache_380_; lean_object* v_lakeArgs_x3f_381_; lean_object* v_packages_382_; lean_object* v_packageMap_383_; lean_object* v_facetConfigs_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_395_; 
v_lakeEnv_378_ = lean_ctor_get(v_self_375_, 0);
v_lakeConfig_379_ = lean_ctor_get(v_self_375_, 1);
v_lakeCache_380_ = lean_ctor_get(v_self_375_, 2);
v_lakeArgs_x3f_381_ = lean_ctor_get(v_self_375_, 3);
v_packages_382_ = lean_ctor_get(v_self_375_, 4);
v_packageMap_383_ = lean_ctor_get(v_self_375_, 5);
v_facetConfigs_384_ = lean_ctor_get(v_self_375_, 6);
v_isSharedCheck_395_ = !lean_is_exclusive(v_self_375_);
if (v_isSharedCheck_395_ == 0)
{
v___x_386_ = v_self_375_;
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_facetConfigs_384_);
lean_inc(v_packageMap_383_);
lean_inc(v_packages_382_);
lean_inc(v_lakeArgs_x3f_381_);
lean_inc(v_lakeCache_380_);
lean_inc(v_lakeConfig_379_);
lean_inc(v_lakeEnv_378_);
lean_dec(v_self_375_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_395_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_keyName_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v_keyName_388_ = lean_ctor_get(v_pkg_374_, 2);
lean_inc(v_keyName_388_);
lean_inc_ref(v_pkg_374_);
v___x_389_ = lean_array_push(v_packages_382_, v_pkg_374_);
v___x_390_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_391_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_390_, v_keyName_388_, v_pkg_374_, v_packageMap_383_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 5, v___x_391_);
lean_ctor_set(v___x_386_, 4, v___x_389_);
v___x_393_ = v___x_386_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_lakeEnv_378_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_lakeConfig_379_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_lakeCache_380_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_lakeArgs_x3f_381_);
lean_ctor_set(v_reuseFailAlloc_394_, 4, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_394_, 5, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 6, v_facetConfigs_384_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_398_, lean_object* v_self_399_){
_start:
{
lean_object* v_lakeEnv_400_; lean_object* v_lakeConfig_401_; lean_object* v_lakeCache_402_; lean_object* v_lakeArgs_x3f_403_; lean_object* v_packages_404_; lean_object* v_packageMap_405_; lean_object* v_facetConfigs_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_450_; 
v_lakeEnv_400_ = lean_ctor_get(v_self_399_, 0);
v_lakeConfig_401_ = lean_ctor_get(v_self_399_, 1);
v_lakeCache_402_ = lean_ctor_get(v_self_399_, 2);
v_lakeArgs_x3f_403_ = lean_ctor_get(v_self_399_, 3);
v_packages_404_ = lean_ctor_get(v_self_399_, 4);
v_packageMap_405_ = lean_ctor_get(v_self_399_, 5);
v_facetConfigs_406_ = lean_ctor_get(v_self_399_, 6);
v_isSharedCheck_450_ = !lean_is_exclusive(v_self_399_);
if (v_isSharedCheck_450_ == 0)
{
v___x_408_ = v_self_399_;
v_isShared_409_ = v_isSharedCheck_450_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_facetConfigs_406_);
lean_inc(v_packageMap_405_);
lean_inc(v_packages_404_);
lean_inc(v_lakeArgs_x3f_403_);
lean_inc(v_lakeCache_402_);
lean_inc(v_lakeConfig_401_);
lean_inc(v_lakeEnv_400_);
lean_dec(v_self_399_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_450_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_baseName_410_; lean_object* v_keyName_411_; lean_object* v_origName_412_; lean_object* v_dir_413_; lean_object* v_relDir_414_; lean_object* v_config_415_; lean_object* v_configFile_416_; lean_object* v_relConfigFile_417_; lean_object* v_relManifestFile_418_; lean_object* v_scope_419_; lean_object* v_remoteUrl_420_; lean_object* v_depConfigs_421_; lean_object* v_depPkgs_422_; lean_object* v_targetDecls_423_; lean_object* v_targetDeclMap_424_; lean_object* v_defaultTargets_425_; lean_object* v_cacheServices_426_; lean_object* v_scripts_427_; lean_object* v_defaultScripts_428_; lean_object* v_postUpdateHooks_429_; lean_object* v_buildArchive_430_; lean_object* v_testDriver_431_; lean_object* v_lintDriver_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_447_; 
v_baseName_410_ = lean_ctor_get(v_pkg_398_, 1);
v_keyName_411_ = lean_ctor_get(v_pkg_398_, 2);
v_origName_412_ = lean_ctor_get(v_pkg_398_, 3);
v_dir_413_ = lean_ctor_get(v_pkg_398_, 4);
v_relDir_414_ = lean_ctor_get(v_pkg_398_, 5);
v_config_415_ = lean_ctor_get(v_pkg_398_, 6);
v_configFile_416_ = lean_ctor_get(v_pkg_398_, 7);
v_relConfigFile_417_ = lean_ctor_get(v_pkg_398_, 8);
v_relManifestFile_418_ = lean_ctor_get(v_pkg_398_, 9);
v_scope_419_ = lean_ctor_get(v_pkg_398_, 10);
v_remoteUrl_420_ = lean_ctor_get(v_pkg_398_, 11);
v_depConfigs_421_ = lean_ctor_get(v_pkg_398_, 12);
v_depPkgs_422_ = lean_ctor_get(v_pkg_398_, 14);
v_targetDecls_423_ = lean_ctor_get(v_pkg_398_, 15);
v_targetDeclMap_424_ = lean_ctor_get(v_pkg_398_, 16);
v_defaultTargets_425_ = lean_ctor_get(v_pkg_398_, 17);
v_cacheServices_426_ = lean_ctor_get(v_pkg_398_, 18);
v_scripts_427_ = lean_ctor_get(v_pkg_398_, 19);
v_defaultScripts_428_ = lean_ctor_get(v_pkg_398_, 20);
v_postUpdateHooks_429_ = lean_ctor_get(v_pkg_398_, 21);
v_buildArchive_430_ = lean_ctor_get(v_pkg_398_, 22);
v_testDriver_431_ = lean_ctor_get(v_pkg_398_, 23);
v_lintDriver_432_ = lean_ctor_get(v_pkg_398_, 24);
v_isSharedCheck_447_ = !lean_is_exclusive(v_pkg_398_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_448_ = lean_ctor_get(v_pkg_398_, 13);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_pkg_398_, 0);
lean_dec(v_unused_449_);
v___x_434_ = v_pkg_398_;
v_isShared_435_ = v_isSharedCheck_447_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_lintDriver_432_);
lean_inc(v_testDriver_431_);
lean_inc(v_buildArchive_430_);
lean_inc(v_postUpdateHooks_429_);
lean_inc(v_defaultScripts_428_);
lean_inc(v_scripts_427_);
lean_inc(v_cacheServices_426_);
lean_inc(v_defaultTargets_425_);
lean_inc(v_targetDeclMap_424_);
lean_inc(v_targetDecls_423_);
lean_inc(v_depPkgs_422_);
lean_inc(v_depConfigs_421_);
lean_inc(v_remoteUrl_420_);
lean_inc(v_scope_419_);
lean_inc(v_relManifestFile_418_);
lean_inc(v_relConfigFile_417_);
lean_inc(v_configFile_416_);
lean_inc(v_config_415_);
lean_inc(v_relDir_414_);
lean_inc(v_dir_413_);
lean_inc(v_origName_412_);
lean_inc(v_keyName_411_);
lean_inc(v_baseName_410_);
lean_dec(v_pkg_398_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_447_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = lean_array_get_size(v_packages_404_);
v___x_437_ = ((lean_object*)(l_Lake_Workspace_addPackage___closed__0));
lean_inc(v_keyName_411_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 13, v___x_437_);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 25, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_baseName_410_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_keyName_411_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_origName_412_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_dir_413_);
lean_ctor_set(v_reuseFailAlloc_446_, 5, v_relDir_414_);
lean_ctor_set(v_reuseFailAlloc_446_, 6, v_config_415_);
lean_ctor_set(v_reuseFailAlloc_446_, 7, v_configFile_416_);
lean_ctor_set(v_reuseFailAlloc_446_, 8, v_relConfigFile_417_);
lean_ctor_set(v_reuseFailAlloc_446_, 9, v_relManifestFile_418_);
lean_ctor_set(v_reuseFailAlloc_446_, 10, v_scope_419_);
lean_ctor_set(v_reuseFailAlloc_446_, 11, v_remoteUrl_420_);
lean_ctor_set(v_reuseFailAlloc_446_, 12, v_depConfigs_421_);
lean_ctor_set(v_reuseFailAlloc_446_, 13, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_446_, 14, v_depPkgs_422_);
lean_ctor_set(v_reuseFailAlloc_446_, 15, v_targetDecls_423_);
lean_ctor_set(v_reuseFailAlloc_446_, 16, v_targetDeclMap_424_);
lean_ctor_set(v_reuseFailAlloc_446_, 17, v_defaultTargets_425_);
lean_ctor_set(v_reuseFailAlloc_446_, 18, v_cacheServices_426_);
lean_ctor_set(v_reuseFailAlloc_446_, 19, v_scripts_427_);
lean_ctor_set(v_reuseFailAlloc_446_, 20, v_defaultScripts_428_);
lean_ctor_set(v_reuseFailAlloc_446_, 21, v_postUpdateHooks_429_);
lean_ctor_set(v_reuseFailAlloc_446_, 22, v_buildArchive_430_);
lean_ctor_set(v_reuseFailAlloc_446_, 23, v_testDriver_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 24, v_lintDriver_432_);
v___x_439_ = v_reuseFailAlloc_446_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
lean_inc_ref(v___x_439_);
v___x_440_ = lean_array_push(v_packages_404_, v___x_439_);
v___x_441_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_442_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_441_, v_keyName_411_, v___x_439_, v_packageMap_405_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 5, v___x_442_);
lean_ctor_set(v___x_408_, 4, v___x_440_);
v___x_444_ = v___x_408_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_lakeEnv_400_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_lakeConfig_401_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_lakeCache_402_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_lakeArgs_x3f_403_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_facetConfigs_406_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_451_, lean_object* v_self_452_){
_start:
{
lean_object* v_packageMap_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v_packageMap_453_ = lean_ctor_get(v_self_452_, 5);
lean_inc(v_packageMap_453_);
lean_dec_ref(v_self_452_);
v___x_454_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_455_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_454_, v_packageMap_453_, v_keyName_451_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_456_, lean_object* v___x_457_, lean_object* v___x_458_, lean_object* v_a_459_, lean_object* v_x_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_baseName_462_; uint8_t v___x_463_; 
v_baseName_462_ = lean_ctor_get(v_a_459_, 1);
v___x_463_ = lean_name_eq(v_baseName_462_, v_name_456_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_dec_ref(v_a_459_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_457_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec_ref(v___x_457_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v_a_459_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_458_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v_a_472_, lean_object* v_x_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_469_, v___x_470_, v___x_471_, v_a_472_, v_x_473_, v___y_474_);
lean_dec_ref(v___y_474_);
lean_dec(v_name_469_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_479_, lean_object* v_self_480_){
_start:
{
lean_object* v_packages_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___f_486_; size_t v_sz_487_; size_t v___x_488_; lean_object* v___x_489_; lean_object* v_fst_490_; 
v_packages_481_ = lean_ctor_get(v_self_480_, 4);
lean_inc_ref(v_packages_481_);
lean_dec_ref(v_self_480_);
v___x_482_ = ((lean_object*)(l_Lake_Workspace_findCacheService_x3f___closed__9));
v___x_483_ = lean_box(0);
v___x_484_ = lean_box(0);
v___x_485_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__0));
v___f_486_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_486_, 0, v_name_479_);
lean_closure_set(v___f_486_, 1, v___x_485_);
lean_closure_set(v___f_486_, 2, v___x_484_);
v_sz_487_ = lean_array_size(v_packages_481_);
v___x_488_ = ((size_t)0ULL);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_482_, v_packages_481_, v___f_486_, v_sz_487_, v___x_488_, v___x_485_);
v_fst_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_fst_490_);
lean_dec(v___x_489_);
if (lean_obj_tag(v_fst_490_) == 0)
{
return v___x_483_;
}
else
{
lean_object* v_val_491_; 
v_val_491_ = lean_ctor_get(v_fst_490_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v_fst_490_, 1);
return v_val_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_492_, lean_object* v_self_493_){
_start:
{
lean_object* v_packageMap_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_packageMap_494_ = lean_ctor_get(v_self_493_, 5);
lean_inc(v_packageMap_494_);
lean_dec_ref(v_self_493_);
v___x_495_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_496_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_495_, v_packageMap_494_, v_name_492_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_500_, lean_object* v_as_501_, size_t v_sz_502_, size_t v_i_503_, lean_object* v_b_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_505_ == 0)
{
lean_inc_ref(v_b_504_);
return v_b_504_;
}
else
{
lean_object* v_a_506_; lean_object* v_scripts_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_a_506_ = lean_array_uget_borrowed(v_as_501_, v_i_503_);
v_scripts_507_ = lean_ctor_get(v_a_506_, 19);
v___x_508_ = lean_box(0);
v___x_509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_507_, v_script_500_);
if (lean_obj_tag(v___x_509_) == 1)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_508_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; 
lean_dec(v___x_509_);
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_503_, v___x_513_);
v_i_503_ = v___x_514_;
v_b_504_ = v___x_512_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_516_, lean_object* v_as_517_, lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_b_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_522_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_516_, v_as_517_, v_sz_boxed_521_, v_i_boxed_522_, v_b_520_);
lean_dec_ref(v_b_520_);
lean_dec_ref(v_as_517_);
lean_dec(v_script_516_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_524_, lean_object* v_self_525_){
_start:
{
lean_object* v_packages_526_; lean_object* v___x_527_; lean_object* v___x_528_; size_t v_sz_529_; size_t v___x_530_; lean_object* v___x_531_; lean_object* v_fst_532_; 
v_packages_526_ = lean_ctor_get(v_self_525_, 4);
v___x_527_ = lean_box(0);
v___x_528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_529_ = lean_array_size(v_packages_526_);
v___x_530_ = ((size_t)0ULL);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_524_, v_packages_526_, v_sz_529_, v___x_530_, v___x_528_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_fst_532_);
lean_dec_ref(v___x_531_);
if (lean_obj_tag(v_fst_532_) == 0)
{
return v___x_527_;
}
else
{
lean_object* v_val_533_; 
v_val_533_ = lean_ctor_get(v_fst_532_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v_fst_532_, 1);
return v_val_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_534_, lean_object* v_self_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lake_Workspace_findScript_x3f(v_script_534_, v_self_535_);
lean_dec_ref(v_self_535_);
lean_dec(v_script_534_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_537_, lean_object* v_as_538_, size_t v_i_539_, size_t v_stop_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
v___x_543_ = l_Lake_Package_isLocalModule(v_mod_537_, v___x_542_);
if (v___x_543_ == 0)
{
size_t v___x_544_; size_t v___x_545_; 
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_539_, v___x_544_);
v_i_539_ = v___x_545_;
goto _start;
}
else
{
return v___x_543_;
}
}
else
{
uint8_t v___x_547_; 
v___x_547_ = 0;
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_548_, lean_object* v_as_549_, lean_object* v_i_550_, lean_object* v_stop_551_){
_start:
{
size_t v_i_boxed_552_; size_t v_stop_boxed_553_; uint8_t v_res_554_; lean_object* v_r_555_; 
v_i_boxed_552_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_stop_boxed_553_ = lean_unbox_usize(v_stop_551_);
lean_dec(v_stop_551_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_548_, v_as_549_, v_i_boxed_552_, v_stop_boxed_553_);
lean_dec_ref(v_as_549_);
lean_dec(v_mod_548_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_556_, lean_object* v_self_557_){
_start:
{
lean_object* v_packages_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_packages_558_ = lean_ctor_get(v_self_557_, 4);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_array_get_size(v_packages_558_);
v___x_561_ = lean_nat_dec_lt(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
return v___x_561_;
}
else
{
if (v___x_561_ == 0)
{
return v___x_561_;
}
else
{
size_t v___x_562_; size_t v___x_563_; uint8_t v___x_564_; 
v___x_562_ = ((size_t)0ULL);
v___x_563_ = lean_usize_of_nat(v___x_560_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_556_, v_packages_558_, v___x_562_, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_565_, lean_object* v_self_566_){
_start:
{
uint8_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l_Lake_Workspace_isLocalModule(v_mod_565_, v_self_566_);
lean_dec_ref(v_self_566_);
lean_dec(v_mod_565_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_569_, lean_object* v_as_570_, size_t v_i_571_, size_t v_stop_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_571_, v_stop_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_array_uget_borrowed(v_as_570_, v_i_571_);
v___x_575_ = l_Lake_Package_isBuildableModule(v_mod_569_, v___x_574_);
if (v___x_575_ == 0)
{
size_t v___x_576_; size_t v___x_577_; 
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_add(v_i_571_, v___x_576_);
v_i_571_ = v___x_577_;
goto _start;
}
else
{
return v___x_575_;
}
}
else
{
uint8_t v___x_579_; 
v___x_579_ = 0;
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_580_, lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_){
_start:
{
size_t v_i_boxed_584_; size_t v_stop_boxed_585_; uint8_t v_res_586_; lean_object* v_r_587_; 
v_i_boxed_584_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_580_, v_as_581_, v_i_boxed_584_, v_stop_boxed_585_);
lean_dec_ref(v_as_581_);
lean_dec(v_mod_580_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_588_, lean_object* v_self_589_){
_start:
{
lean_object* v_packages_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_packages_590_ = lean_ctor_get(v_self_589_, 4);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_get_size(v_packages_590_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
return v___x_593_;
}
else
{
if (v___x_593_ == 0)
{
return v___x_593_;
}
else
{
size_t v___x_594_; size_t v___x_595_; uint8_t v___x_596_; 
v___x_594_ = ((size_t)0ULL);
v___x_595_ = lean_usize_of_nat(v___x_592_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_588_, v_packages_590_, v___x_594_, v___x_595_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_597_, lean_object* v_self_598_){
_start:
{
uint8_t v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l_Lake_Workspace_isBuildableModule(v_mod_597_, v_self_598_);
lean_dec_ref(v_self_598_);
lean_dec(v_mod_597_);
v_r_600_ = lean_box(v_res_599_);
return v_r_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_604_, lean_object* v_as_605_, size_t v_sz_606_, size_t v_i_607_, lean_object* v_b_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_usize_dec_lt(v_i_607_, v_sz_606_);
if (v___x_609_ == 0)
{
lean_dec(v_mod_604_);
lean_inc_ref(v_b_608_);
return v_b_608_;
}
else
{
lean_object* v___x_610_; lean_object* v_a_611_; lean_object* v___x_612_; 
v___x_610_ = lean_box(0);
v_a_611_ = lean_array_uget_borrowed(v_as_605_, v_i_607_);
lean_inc(v_a_611_);
lean_inc(v_mod_604_);
v___x_612_ = l_Lake_Package_findModule_x3f(v_mod_604_, v_a_611_);
if (lean_obj_tag(v___x_612_) == 1)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_mod_604_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_610_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; size_t v___x_616_; size_t v___x_617_; 
lean_dec(v___x_612_);
v___x_615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_607_, v___x_616_);
v_i_607_ = v___x_617_;
v_b_608_ = v___x_615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_619_, lean_object* v_as_620_, lean_object* v_sz_621_, lean_object* v_i_622_, lean_object* v_b_623_){
_start:
{
size_t v_sz_boxed_624_; size_t v_i_boxed_625_; lean_object* v_res_626_; 
v_sz_boxed_624_ = lean_unbox_usize(v_sz_621_);
lean_dec(v_sz_621_);
v_i_boxed_625_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_res_626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_619_, v_as_620_, v_sz_boxed_624_, v_i_boxed_625_, v_b_623_);
lean_dec_ref(v_b_623_);
lean_dec_ref(v_as_620_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_627_, lean_object* v_self_628_){
_start:
{
lean_object* v_packages_629_; lean_object* v___x_630_; lean_object* v___x_631_; size_t v_sz_632_; size_t v___x_633_; lean_object* v___x_634_; lean_object* v_fst_635_; 
v_packages_629_ = lean_ctor_get(v_self_628_, 4);
v___x_630_ = lean_box(0);
v___x_631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_632_ = lean_array_size(v_packages_629_);
v___x_633_ = ((size_t)0ULL);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_627_, v_packages_629_, v_sz_632_, v___x_633_, v___x_631_);
v_fst_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_fst_635_);
lean_dec_ref(v___x_634_);
if (lean_obj_tag(v_fst_635_) == 0)
{
return v___x_630_;
}
else
{
lean_object* v_val_636_; 
v_val_636_ = lean_ctor_get(v_fst_635_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v_fst_635_, 1);
return v_val_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_637_, lean_object* v_self_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lake_Workspace_findModule_x3f(v_mod_637_, v_self_638_);
lean_dec_ref(v_self_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_640_, lean_object* v_as_641_, size_t v_i_642_, size_t v_stop_643_, lean_object* v_b_644_){
_start:
{
lean_object* v___y_646_; uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_eq(v_i_642_, v_stop_643_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_array_uget_borrowed(v_as_641_, v_i_642_);
lean_inc(v___x_651_);
lean_inc(v_mod_640_);
v___x_652_ = l_Lake_Package_findModule_x3f(v_mod_640_, v___x_651_);
if (lean_obj_tag(v___x_652_) == 0)
{
v___y_646_ = v_b_644_;
goto v___jp_645_;
}
else
{
lean_object* v_val_653_; lean_object* v___x_654_; 
v_val_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_val_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = lean_array_push(v_b_644_, v_val_653_);
v___y_646_ = v___x_654_;
goto v___jp_645_;
}
}
else
{
lean_dec(v_mod_640_);
return v_b_644_;
}
v___jp_645_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_642_, v___x_647_);
v_i_642_ = v___x_648_;
v_b_644_ = v___y_646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_655_, lean_object* v_as_656_, lean_object* v_i_657_, lean_object* v_stop_658_, lean_object* v_b_659_){
_start:
{
size_t v_i_boxed_660_; size_t v_stop_boxed_661_; lean_object* v_res_662_; 
v_i_boxed_660_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_stop_boxed_661_ = lean_unbox_usize(v_stop_658_);
lean_dec(v_stop_658_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_655_, v_as_656_, v_i_boxed_660_, v_stop_boxed_661_, v_b_659_);
lean_dec_ref(v_as_656_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_665_, lean_object* v_as_666_, lean_object* v_start_667_, lean_object* v_stop_668_){
_start:
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_670_ = lean_nat_dec_lt(v_start_667_, v_stop_668_);
if (v___x_670_ == 0)
{
lean_dec(v_mod_665_);
return v___x_669_;
}
else
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_array_get_size(v_as_666_);
v___x_672_ = lean_nat_dec_le(v_stop_668_, v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_lt(v_start_667_, v___x_671_);
if (v___x_673_ == 0)
{
lean_dec(v_mod_665_);
return v___x_669_;
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_usize_of_nat(v_start_667_);
v___x_675_ = lean_usize_of_nat(v___x_671_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_665_, v_as_666_, v___x_674_, v___x_675_, v___x_669_);
return v___x_676_;
}
}
else
{
size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_usize_of_nat(v_start_667_);
v___x_678_ = lean_usize_of_nat(v_stop_668_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_665_, v_as_666_, v___x_677_, v___x_678_, v___x_669_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_680_, lean_object* v_as_681_, lean_object* v_start_682_, lean_object* v_stop_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_680_, v_as_681_, v_start_682_, v_stop_683_);
lean_dec(v_stop_683_);
lean_dec(v_start_682_);
lean_dec_ref(v_as_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_685_, lean_object* v_self_686_){
_start:
{
lean_object* v_packages_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_packages_687_ = lean_ctor_get(v_self_686_, 4);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_packages_687_);
v___x_690_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_685_, v_packages_687_, v___x_688_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_691_, lean_object* v_self_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lake_Workspace_findModules(v_mod_691_, v_self_692_);
lean_dec_ref(v_self_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_694_, lean_object* v_as_695_, size_t v_sz_696_, size_t v_i_697_, lean_object* v_b_698_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_lt(v_i_697_, v_sz_696_);
if (v___x_699_ == 0)
{
lean_dec(v_mod_694_);
lean_inc_ref(v_b_698_);
return v_b_698_;
}
else
{
lean_object* v___x_700_; lean_object* v_a_701_; lean_object* v___x_702_; 
v___x_700_ = lean_box(0);
v_a_701_ = lean_array_uget_borrowed(v_as_695_, v_i_697_);
lean_inc(v_a_701_);
lean_inc(v_mod_694_);
v___x_702_ = l_Lake_Package_findTargetModule_x3f(v_mod_694_, v_a_701_);
if (lean_obj_tag(v___x_702_) == 1)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v_mod_694_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_700_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; size_t v___x_706_; size_t v___x_707_; 
lean_dec(v___x_702_);
v___x_705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_i_697_, v___x_706_);
v_i_697_ = v___x_707_;
v_b_698_ = v___x_705_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_709_, lean_object* v_as_710_, lean_object* v_sz_711_, lean_object* v_i_712_, lean_object* v_b_713_){
_start:
{
size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v_sz_boxed_714_ = lean_unbox_usize(v_sz_711_);
lean_dec(v_sz_711_);
v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_709_, v_as_710_, v_sz_boxed_714_, v_i_boxed_715_, v_b_713_);
lean_dec_ref(v_b_713_);
lean_dec_ref(v_as_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_717_, lean_object* v_self_718_){
_start:
{
lean_object* v_packages_719_; lean_object* v___x_720_; lean_object* v___x_721_; size_t v_sz_722_; size_t v___x_723_; lean_object* v___x_724_; lean_object* v_fst_725_; 
v_packages_719_ = lean_ctor_get(v_self_718_, 4);
v___x_720_ = lean_box(0);
v___x_721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_722_ = lean_array_size(v_packages_719_);
v___x_723_ = ((size_t)0ULL);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_717_, v_packages_719_, v_sz_722_, v___x_723_, v___x_721_);
v_fst_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_fst_725_);
lean_dec_ref(v___x_724_);
if (lean_obj_tag(v_fst_725_) == 0)
{
return v___x_720_;
}
else
{
lean_object* v_val_726_; 
v_val_726_ = lean_ctor_get(v_fst_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v_fst_725_, 1);
return v_val_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_727_, lean_object* v_self_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_727_, v_self_728_);
lean_dec_ref(v_self_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_730_, lean_object* v_as_731_, size_t v_sz_732_, size_t v_i_733_, lean_object* v_b_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = lean_usize_dec_lt(v_i_733_, v_sz_732_);
if (v___x_735_ == 0)
{
lean_dec_ref(v_path_730_);
lean_inc_ref(v_b_734_);
return v_b_734_;
}
else
{
lean_object* v___x_736_; lean_object* v_a_737_; lean_object* v___x_738_; 
v___x_736_ = lean_box(0);
v_a_737_ = lean_array_uget_borrowed(v_as_731_, v_i_733_);
lean_inc(v_a_737_);
lean_inc_ref(v_path_730_);
v___x_738_ = l_Lake_Package_findModuleBySrc_x3f(v_path_730_, v_a_737_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec_ref(v_path_730_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_736_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; size_t v___x_742_; size_t v___x_743_; 
lean_dec(v___x_738_);
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_733_, v___x_742_);
v_i_733_ = v___x_743_;
v_b_734_ = v___x_741_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_745_, lean_object* v_as_746_, lean_object* v_sz_747_, lean_object* v_i_748_, lean_object* v_b_749_){
_start:
{
size_t v_sz_boxed_750_; size_t v_i_boxed_751_; lean_object* v_res_752_; 
v_sz_boxed_750_ = lean_unbox_usize(v_sz_747_);
lean_dec(v_sz_747_);
v_i_boxed_751_ = lean_unbox_usize(v_i_748_);
lean_dec(v_i_748_);
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_745_, v_as_746_, v_sz_boxed_750_, v_i_boxed_751_, v_b_749_);
lean_dec_ref(v_b_749_);
lean_dec_ref(v_as_746_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_753_, lean_object* v_self_754_){
_start:
{
lean_object* v_packages_755_; lean_object* v___x_756_; lean_object* v___x_757_; size_t v_sz_758_; size_t v___x_759_; lean_object* v___x_760_; lean_object* v_fst_761_; 
v_packages_755_ = lean_ctor_get(v_self_754_, 4);
v___x_756_ = lean_box(0);
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_758_ = lean_array_size(v_packages_755_);
v___x_759_ = ((size_t)0ULL);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_753_, v_packages_755_, v_sz_758_, v___x_759_, v___x_757_);
v_fst_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_fst_761_);
lean_dec_ref(v___x_760_);
if (lean_obj_tag(v_fst_761_) == 0)
{
return v___x_756_;
}
else
{
lean_object* v_val_762_; 
v_val_762_ = lean_ctor_get(v_fst_761_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v_fst_761_, 1);
return v_val_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_763_, lean_object* v_self_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_763_, v_self_764_);
lean_dec_ref(v_self_764_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_769_, lean_object* v_as_770_, size_t v_sz_771_, size_t v_i_772_, lean_object* v_b_773_){
_start:
{
lean_object* v_a_775_; uint8_t v___x_779_; 
v___x_779_ = lean_usize_dec_lt(v_i_772_, v_sz_771_);
if (v___x_779_ == 0)
{
lean_inc_ref(v_b_773_);
return v_b_773_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_a_782_; lean_object* v___x_783_; 
v___x_780_ = lean_box(0);
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_782_ = lean_array_uget_borrowed(v_as_770_, v_i_772_);
v___x_783_ = l_Lake_Package_findTargetDecl_x3f(v_name_769_, v_a_782_);
if (lean_obj_tag(v___x_783_) == 0)
{
v_a_775_ = v___x_781_;
goto v___jp_774_;
}
else
{
lean_object* v_val_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_799_; 
v_val_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_799_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_799_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_val_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_799_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_name_788_; lean_object* v_kind_789_; lean_object* v_config_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_name_788_ = lean_ctor_get(v_val_784_, 1);
lean_inc(v_name_788_);
v_kind_789_ = lean_ctor_get(v_val_784_, 2);
lean_inc(v_kind_789_);
v_config_790_ = lean_ctor_get(v_val_784_, 3);
lean_inc(v_config_790_);
lean_dec(v_val_784_);
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_792_ = lean_name_eq(v_kind_789_, v___x_791_);
lean_dec(v_kind_789_);
if (v___x_792_ == 0)
{
lean_dec(v_config_790_);
lean_dec(v_name_788_);
lean_del_object(v___x_786_);
v_a_775_ = v___x_781_;
goto v___jp_774_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_inc(v_a_782_);
v___x_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_793_, 0, v_a_782_);
lean_ctor_set(v___x_793_, 1, v_name_788_);
lean_ctor_set(v___x_793_, 2, v_config_790_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_793_);
v___x_795_ = v___x_786_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_798_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_780_);
return v___x_797_;
}
}
}
}
}
v___jp_774_:
{
size_t v___x_776_; size_t v___x_777_; 
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_772_, v___x_776_);
v_i_772_ = v___x_777_;
v_b_773_ = v_a_775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_800_, lean_object* v_as_801_, lean_object* v_sz_802_, lean_object* v_i_803_, lean_object* v_b_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_802_);
lean_dec(v_sz_802_);
v_i_boxed_806_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_800_, v_as_801_, v_sz_boxed_805_, v_i_boxed_806_, v_b_804_);
lean_dec_ref(v_b_804_);
lean_dec_ref(v_as_801_);
lean_dec(v_name_800_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_808_, lean_object* v_self_809_){
_start:
{
lean_object* v_packages_810_; lean_object* v___x_811_; lean_object* v___x_812_; size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; lean_object* v_fst_816_; 
v_packages_810_ = lean_ctor_get(v_self_809_, 4);
v___x_811_ = lean_box(0);
v___x_812_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_813_ = lean_array_size(v_packages_810_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_808_, v_packages_810_, v_sz_813_, v___x_814_, v___x_812_);
v_fst_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_fst_816_);
lean_dec_ref(v___x_815_);
if (lean_obj_tag(v_fst_816_) == 0)
{
return v___x_811_;
}
else
{
lean_object* v_val_817_; 
v_val_817_ = lean_ctor_get(v_fst_816_, 0);
lean_inc(v_val_817_);
lean_dec_ref_known(v_fst_816_, 1);
return v_val_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_818_, lean_object* v_self_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lake_Workspace_findLeanLib_x3f(v_name_818_, v_self_819_);
lean_dec_ref(v_self_819_);
lean_dec(v_name_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_821_, lean_object* v_as_822_, size_t v_sz_823_, size_t v_i_824_, lean_object* v_b_825_){
_start:
{
lean_object* v_a_827_; uint8_t v___x_831_; 
v___x_831_ = lean_usize_dec_lt(v_i_824_, v_sz_823_);
if (v___x_831_ == 0)
{
lean_inc_ref(v_b_825_);
return v_b_825_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_a_834_; lean_object* v___x_835_; 
v___x_832_ = lean_box(0);
v___x_833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_834_ = lean_array_uget_borrowed(v_as_822_, v_i_824_);
v___x_835_ = l_Lake_Package_findTargetDecl_x3f(v_name_821_, v_a_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
v_a_827_ = v___x_833_;
goto v___jp_826_;
}
else
{
lean_object* v_val_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_851_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_851_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_851_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_val_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_851_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_name_840_; lean_object* v_kind_841_; lean_object* v_config_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_name_840_ = lean_ctor_get(v_val_836_, 1);
lean_inc(v_name_840_);
v_kind_841_ = lean_ctor_get(v_val_836_, 2);
lean_inc(v_kind_841_);
v_config_842_ = lean_ctor_get(v_val_836_, 3);
lean_inc(v_config_842_);
lean_dec(v_val_836_);
v___x_843_ = l_Lake_LeanExe_keyword;
v___x_844_ = lean_name_eq(v_kind_841_, v___x_843_);
lean_dec(v_kind_841_);
if (v___x_844_ == 0)
{
lean_dec(v_config_842_);
lean_dec(v_name_840_);
lean_del_object(v___x_838_);
v_a_827_ = v___x_833_;
goto v___jp_826_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_inc(v_a_834_);
v___x_845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_845_, 0, v_a_834_);
lean_ctor_set(v___x_845_, 1, v_name_840_);
lean_ctor_set(v___x_845_, 2, v_config_842_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_845_);
v___x_847_ = v___x_838_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_850_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_832_);
return v___x_849_;
}
}
}
}
}
v___jp_826_:
{
size_t v___x_828_; size_t v___x_829_; 
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_add(v_i_824_, v___x_828_);
v_i_824_ = v___x_829_;
v_b_825_ = v_a_827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_852_, lean_object* v_as_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_b_856_){
_start:
{
size_t v_sz_boxed_857_; size_t v_i_boxed_858_; lean_object* v_res_859_; 
v_sz_boxed_857_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_858_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_852_, v_as_853_, v_sz_boxed_857_, v_i_boxed_858_, v_b_856_);
lean_dec_ref(v_b_856_);
lean_dec_ref(v_as_853_);
lean_dec(v_name_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_860_, lean_object* v_self_861_){
_start:
{
lean_object* v_packages_862_; lean_object* v___x_863_; lean_object* v___x_864_; size_t v_sz_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v_fst_868_; 
v_packages_862_ = lean_ctor_get(v_self_861_, 4);
v___x_863_ = lean_box(0);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_865_ = lean_array_size(v_packages_862_);
v___x_866_ = ((size_t)0ULL);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_860_, v_packages_862_, v_sz_865_, v___x_866_, v___x_864_);
v_fst_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_fst_868_);
lean_dec_ref(v___x_867_);
if (lean_obj_tag(v_fst_868_) == 0)
{
return v___x_863_;
}
else
{
lean_object* v_val_869_; 
v_val_869_ = lean_ctor_get(v_fst_868_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_fst_868_, 1);
return v_val_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_870_, lean_object* v_self_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lake_Workspace_findLeanExe_x3f(v_name_870_, v_self_871_);
lean_dec_ref(v_self_871_);
lean_dec(v_name_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_873_, lean_object* v_as_874_, size_t v_sz_875_, size_t v_i_876_, lean_object* v_b_877_){
_start:
{
lean_object* v_a_879_; uint8_t v___x_883_; 
v___x_883_ = lean_usize_dec_lt(v_i_876_, v_sz_875_);
if (v___x_883_ == 0)
{
lean_inc_ref(v_b_877_);
return v_b_877_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_887_; 
v___x_884_ = lean_box(0);
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_886_ = lean_array_uget_borrowed(v_as_874_, v_i_876_);
v___x_887_ = l_Lake_Package_findTargetDecl_x3f(v_name_873_, v_a_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
v_a_879_ = v___x_885_;
goto v___jp_878_;
}
else
{
lean_object* v_val_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_903_; 
v_val_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_903_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_903_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_val_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_903_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_name_892_; lean_object* v_kind_893_; lean_object* v_config_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_name_892_ = lean_ctor_get(v_val_888_, 1);
lean_inc(v_name_892_);
v_kind_893_ = lean_ctor_get(v_val_888_, 2);
lean_inc(v_kind_893_);
v_config_894_ = lean_ctor_get(v_val_888_, 3);
lean_inc(v_config_894_);
lean_dec(v_val_888_);
v___x_895_ = l_Lake_ExternLib_keyword;
v___x_896_ = lean_name_eq(v_kind_893_, v___x_895_);
lean_dec(v_kind_893_);
if (v___x_896_ == 0)
{
lean_dec(v_config_894_);
lean_dec(v_name_892_);
lean_del_object(v___x_890_);
v_a_879_ = v___x_885_;
goto v___jp_878_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_899_; 
lean_inc(v_a_886_);
v___x_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_897_, 0, v_a_886_);
lean_ctor_set(v___x_897_, 1, v_name_892_);
lean_ctor_set(v___x_897_, 2, v_config_894_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_897_);
v___x_899_ = v___x_890_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_902_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_884_);
return v___x_901_;
}
}
}
}
}
v___jp_878_:
{
size_t v___x_880_; size_t v___x_881_; 
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_876_, v___x_880_);
v_i_876_ = v___x_881_;
v_b_877_ = v_a_879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_904_, lean_object* v_as_905_, lean_object* v_sz_906_, lean_object* v_i_907_, lean_object* v_b_908_){
_start:
{
size_t v_sz_boxed_909_; size_t v_i_boxed_910_; lean_object* v_res_911_; 
v_sz_boxed_909_ = lean_unbox_usize(v_sz_906_);
lean_dec(v_sz_906_);
v_i_boxed_910_ = lean_unbox_usize(v_i_907_);
lean_dec(v_i_907_);
v_res_911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_904_, v_as_905_, v_sz_boxed_909_, v_i_boxed_910_, v_b_908_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_as_905_);
lean_dec(v_name_904_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_912_, lean_object* v_self_913_){
_start:
{
lean_object* v_packages_914_; lean_object* v___x_915_; lean_object* v___x_916_; size_t v_sz_917_; size_t v___x_918_; lean_object* v___x_919_; lean_object* v_fst_920_; 
v_packages_914_ = lean_ctor_get(v_self_913_, 4);
v___x_915_ = lean_box(0);
v___x_916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_917_ = lean_array_size(v_packages_914_);
v___x_918_ = ((size_t)0ULL);
v___x_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_912_, v_packages_914_, v_sz_917_, v___x_918_, v___x_916_);
v_fst_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_fst_920_);
lean_dec_ref(v___x_919_);
if (lean_obj_tag(v_fst_920_) == 0)
{
return v___x_915_;
}
else
{
lean_object* v_val_921_; 
v_val_921_ = lean_ctor_get(v_fst_920_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v_fst_920_, 1);
return v_val_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_922_, lean_object* v_self_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lake_Workspace_findExternLib_x3f(v_name_922_, v_self_923_);
lean_dec_ref(v_self_923_);
lean_dec(v_name_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_925_, lean_object* v_f_926_){
_start:
{
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v___x_927_; 
lean_dec(v_f_926_);
v___x_927_ = lean_box(0);
return v___x_927_;
}
else
{
lean_object* v_val_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_936_; 
v_val_928_ = lean_ctor_get(v_a_925_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_a_925_);
if (v_isSharedCheck_936_ == 0)
{
v___x_930_ = v_a_925_;
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_val_928_);
lean_dec(v_a_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_apply_1(v_f_926_, v_val_928_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_937_, lean_object* v_00_u03b2_938_, lean_object* v_a_939_, lean_object* v_f_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_939_, v_f_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_942_, lean_object* v_x_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_a_942_);
lean_ctor_set(v___x_944_, 1, v_x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_948_, lean_object* v_as_949_, size_t v_sz_950_, size_t v_i_951_, lean_object* v_b_952_){
_start:
{
uint8_t v___x_953_; 
v___x_953_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
if (v___x_953_ == 0)
{
lean_inc_ref(v_b_952_);
return v_b_952_;
}
else
{
lean_object* v___x_954_; lean_object* v_a_955_; lean_object* v___f_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_954_ = lean_box(0);
v_a_955_ = lean_array_uget_borrowed(v_as_949_, v_i_951_);
lean_inc(v_a_955_);
v___f_956_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_956_, 0, v_a_955_);
v___x_957_ = l_Lake_Package_findTargetConfig_x3f(v_name_948_, v_a_955_);
v___x_958_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_957_, v___f_956_);
if (lean_obj_tag(v___x_958_) == 1)
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_954_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; size_t v___x_962_; size_t v___x_963_; 
lean_dec(v___x_958_);
v___x_961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_951_, v___x_962_);
v_i_951_ = v___x_963_;
v_b_952_ = v___x_961_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_965_, lean_object* v_as_966_, lean_object* v_sz_967_, lean_object* v_i_968_, lean_object* v_b_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_971_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_965_, v_as_966_, v_sz_boxed_970_, v_i_boxed_971_, v_b_969_);
lean_dec_ref(v_b_969_);
lean_dec_ref(v_as_966_);
lean_dec(v_name_965_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_973_, lean_object* v_self_974_){
_start:
{
lean_object* v_packages_975_; lean_object* v___x_976_; lean_object* v___x_977_; size_t v_sz_978_; size_t v___x_979_; lean_object* v___x_980_; lean_object* v_fst_981_; 
v_packages_975_ = lean_ctor_get(v_self_974_, 4);
v___x_976_ = lean_box(0);
v___x_977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_978_ = lean_array_size(v_packages_975_);
v___x_979_ = ((size_t)0ULL);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_973_, v_packages_975_, v_sz_978_, v___x_979_, v___x_977_);
v_fst_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_fst_981_);
lean_dec_ref(v___x_980_);
if (lean_obj_tag(v_fst_981_) == 0)
{
return v___x_976_;
}
else
{
lean_object* v_val_982_; 
v_val_982_ = lean_ctor_get(v_fst_981_, 0);
lean_inc(v_val_982_);
lean_dec_ref_known(v_fst_981_, 1);
return v_val_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_983_, lean_object* v_self_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_983_, v_self_984_);
lean_dec_ref(v_self_984_);
lean_dec(v_name_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v_a_986_);
lean_ctor_set(v___x_988_, 1, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_989_, lean_object* v_as_990_, size_t v_sz_991_, size_t v_i_992_, lean_object* v_b_993_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = lean_usize_dec_lt(v_i_992_, v_sz_991_);
if (v___x_994_ == 0)
{
lean_inc_ref(v_b_993_);
return v_b_993_;
}
else
{
lean_object* v___x_995_; lean_object* v_a_996_; lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_995_ = lean_box(0);
v_a_996_ = lean_array_uget_borrowed(v_as_990_, v_i_992_);
lean_inc(v_a_996_);
v___f_997_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_997_, 0, v_a_996_);
v___x_998_ = l_Lake_Package_findTargetDecl_x3f(v_name_989_, v_a_996_);
v___x_999_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_998_, v___f_997_);
if (lean_obj_tag(v___x_999_) == 1)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_995_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; 
lean_dec(v___x_999_);
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_992_, v___x_1003_);
v_i_992_ = v___x_1004_;
v_b_993_ = v___x_1002_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_1006_, lean_object* v_as_1007_, lean_object* v_sz_1008_, lean_object* v_i_1009_, lean_object* v_b_1010_){
_start:
{
size_t v_sz_boxed_1011_; size_t v_i_boxed_1012_; lean_object* v_res_1013_; 
v_sz_boxed_1011_ = lean_unbox_usize(v_sz_1008_);
lean_dec(v_sz_1008_);
v_i_boxed_1012_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_1006_, v_as_1007_, v_sz_boxed_1011_, v_i_boxed_1012_, v_b_1010_);
lean_dec_ref(v_b_1010_);
lean_dec_ref(v_as_1007_);
lean_dec(v_name_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_1014_, lean_object* v_self_1015_){
_start:
{
lean_object* v_packages_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; size_t v_sz_1019_; size_t v___x_1020_; lean_object* v___x_1021_; lean_object* v_fst_1022_; 
v_packages_1016_ = lean_ctor_get(v_self_1015_, 4);
v___x_1017_ = lean_box(0);
v___x_1018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_1019_ = lean_array_size(v_packages_1016_);
v___x_1020_ = ((size_t)0ULL);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_1014_, v_packages_1016_, v_sz_1019_, v___x_1020_, v___x_1018_);
v_fst_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_fst_1022_);
lean_dec_ref(v___x_1021_);
if (lean_obj_tag(v_fst_1022_) == 0)
{
return v___x_1017_;
}
else
{
lean_object* v_val_1023_; 
v_val_1023_ = lean_ctor_get(v_fst_1022_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v_fst_1022_, 1);
return v_val_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_1024_, lean_object* v_self_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_1024_, v_self_1025_);
lean_dec_ref(v_self_1025_);
lean_dec(v_name_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_1027_, lean_object* v_cfg_1028_, lean_object* v_self_1029_){
_start:
{
lean_object* v_lakeEnv_1030_; lean_object* v_lakeConfig_1031_; lean_object* v_lakeCache_1032_; lean_object* v_lakeArgs_x3f_1033_; lean_object* v_packages_1034_; lean_object* v_packageMap_1035_; lean_object* v_facetConfigs_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_lakeEnv_1030_ = lean_ctor_get(v_self_1029_, 0);
v_lakeConfig_1031_ = lean_ctor_get(v_self_1029_, 1);
v_lakeCache_1032_ = lean_ctor_get(v_self_1029_, 2);
v_lakeArgs_x3f_1033_ = lean_ctor_get(v_self_1029_, 3);
v_packages_1034_ = lean_ctor_get(v_self_1029_, 4);
v_packageMap_1035_ = lean_ctor_get(v_self_1029_, 5);
v_facetConfigs_1036_ = lean_ctor_get(v_self_1029_, 6);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_self_1029_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v_self_1029_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_facetConfigs_1036_);
lean_inc(v_packageMap_1035_);
lean_inc(v_packages_1034_);
lean_inc(v_lakeArgs_x3f_1033_);
lean_inc(v_lakeCache_1032_);
lean_inc(v_lakeConfig_1031_);
lean_inc(v_lakeEnv_1030_);
lean_dec(v_self_1029_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = l_Lake_FacetConfigMap_insert(v_name_1027_, v_cfg_1028_, v_facetConfigs_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 6, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_lakeEnv_1030_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_lakeConfig_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_lakeCache_1032_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_lakeArgs_x3f_1033_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v_packages_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 5, v_packageMap_1035_);
lean_ctor_set(v_reuseFailAlloc_1043_, 6, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_1045_, lean_object* v_self_1046_){
_start:
{
lean_object* v_facetConfigs_1047_; lean_object* v___x_1048_; 
v_facetConfigs_1047_ = lean_ctor_get(v_self_1046_, 6);
v___x_1048_ = l_Lake_FacetConfigMap_get_x3f(v_name_1045_, v_facetConfigs_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_1049_, lean_object* v_self_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1049_, v_self_1050_);
lean_dec_ref(v_self_1050_);
lean_dec(v_name_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_1052_, lean_object* v_cfg_1053_, lean_object* v_self_1054_){
_start:
{
lean_object* v_lakeEnv_1055_; lean_object* v_lakeConfig_1056_; lean_object* v_lakeCache_1057_; lean_object* v_lakeArgs_x3f_1058_; lean_object* v_packages_1059_; lean_object* v_packageMap_1060_; lean_object* v_facetConfigs_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_lakeEnv_1055_ = lean_ctor_get(v_self_1054_, 0);
v_lakeConfig_1056_ = lean_ctor_get(v_self_1054_, 1);
v_lakeCache_1057_ = lean_ctor_get(v_self_1054_, 2);
v_lakeArgs_x3f_1058_ = lean_ctor_get(v_self_1054_, 3);
v_packages_1059_ = lean_ctor_get(v_self_1054_, 4);
v_packageMap_1060_ = lean_ctor_get(v_self_1054_, 5);
v_facetConfigs_1061_ = lean_ctor_get(v_self_1054_, 6);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_self_1054_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_self_1054_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_facetConfigs_1061_);
lean_inc(v_packageMap_1060_);
lean_inc(v_packages_1059_);
lean_inc(v_lakeArgs_x3f_1058_);
lean_inc(v_lakeCache_1057_);
lean_inc(v_lakeConfig_1056_);
lean_inc(v_lakeEnv_1055_);
lean_dec(v_self_1054_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = l_Lake_FacetConfigMap_insert(v_name_1052_, v_cfg_1053_, v_facetConfigs_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 6, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_lakeEnv_1055_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_lakeConfig_1056_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_lakeCache_1057_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_lakeArgs_x3f_1058_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_packages_1059_);
lean_ctor_set(v_reuseFailAlloc_1068_, 5, v_packageMap_1060_);
lean_ctor_set(v_reuseFailAlloc_1068_, 6, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_1070_, lean_object* v_self_1071_){
_start:
{
lean_object* v_facetConfigs_1072_; lean_object* v___x_1073_; 
v_facetConfigs_1072_ = lean_ctor_get(v_self_1071_, 6);
v___x_1073_ = l_Lake_FacetConfigMap_get_x3f(v_name_1070_, v_facetConfigs_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_box(0);
return v___x_1074_;
}
else
{
lean_object* v_val_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_val_1075_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v___x_1073_, 1);
v___x_1076_ = l_Lake_Module_keyword;
v___x_1077_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1076_, v_val_1075_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1078_, lean_object* v_self_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1078_, v_self_1079_);
lean_dec_ref(v_self_1079_);
lean_dec(v_name_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1081_, lean_object* v_cfg_1082_, lean_object* v_self_1083_){
_start:
{
lean_object* v_lakeEnv_1084_; lean_object* v_lakeConfig_1085_; lean_object* v_lakeCache_1086_; lean_object* v_lakeArgs_x3f_1087_; lean_object* v_packages_1088_; lean_object* v_packageMap_1089_; lean_object* v_facetConfigs_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v_lakeEnv_1084_ = lean_ctor_get(v_self_1083_, 0);
v_lakeConfig_1085_ = lean_ctor_get(v_self_1083_, 1);
v_lakeCache_1086_ = lean_ctor_get(v_self_1083_, 2);
v_lakeArgs_x3f_1087_ = lean_ctor_get(v_self_1083_, 3);
v_packages_1088_ = lean_ctor_get(v_self_1083_, 4);
v_packageMap_1089_ = lean_ctor_get(v_self_1083_, 5);
v_facetConfigs_1090_ = lean_ctor_get(v_self_1083_, 6);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_self_1083_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v_self_1083_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_facetConfigs_1090_);
lean_inc(v_packageMap_1089_);
lean_inc(v_packages_1088_);
lean_inc(v_lakeArgs_x3f_1087_);
lean_inc(v_lakeCache_1086_);
lean_inc(v_lakeConfig_1085_);
lean_inc(v_lakeEnv_1084_);
lean_dec(v_self_1083_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = l_Lake_FacetConfigMap_insert(v_name_1081_, v_cfg_1082_, v_facetConfigs_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 6, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_lakeEnv_1084_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_lakeConfig_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_lakeCache_1086_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_lakeArgs_x3f_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_packages_1088_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v_packageMap_1089_);
lean_ctor_set(v_reuseFailAlloc_1097_, 6, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1099_, lean_object* v_self_1100_){
_start:
{
lean_object* v_facetConfigs_1101_; lean_object* v___x_1102_; 
v_facetConfigs_1101_ = lean_ctor_get(v_self_1100_, 6);
v___x_1102_ = l_Lake_FacetConfigMap_get_x3f(v_name_1099_, v_facetConfigs_1101_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_box(0);
return v___x_1103_;
}
else
{
lean_object* v_val_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_val_1104_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1105_ = l_Lake_Package_keyword;
v___x_1106_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1105_, v_val_1104_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1107_, lean_object* v_self_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1107_, v_self_1108_);
lean_dec_ref(v_self_1108_);
lean_dec(v_name_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1110_, lean_object* v_cfg_1111_, lean_object* v_self_1112_){
_start:
{
lean_object* v_lakeEnv_1113_; lean_object* v_lakeConfig_1114_; lean_object* v_lakeCache_1115_; lean_object* v_lakeArgs_x3f_1116_; lean_object* v_packages_1117_; lean_object* v_packageMap_1118_; lean_object* v_facetConfigs_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_lakeEnv_1113_ = lean_ctor_get(v_self_1112_, 0);
v_lakeConfig_1114_ = lean_ctor_get(v_self_1112_, 1);
v_lakeCache_1115_ = lean_ctor_get(v_self_1112_, 2);
v_lakeArgs_x3f_1116_ = lean_ctor_get(v_self_1112_, 3);
v_packages_1117_ = lean_ctor_get(v_self_1112_, 4);
v_packageMap_1118_ = lean_ctor_get(v_self_1112_, 5);
v_facetConfigs_1119_ = lean_ctor_get(v_self_1112_, 6);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_self_1112_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v_self_1112_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_facetConfigs_1119_);
lean_inc(v_packageMap_1118_);
lean_inc(v_packages_1117_);
lean_inc(v_lakeArgs_x3f_1116_);
lean_inc(v_lakeCache_1115_);
lean_inc(v_lakeConfig_1114_);
lean_inc(v_lakeEnv_1113_);
lean_dec(v_self_1112_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = l_Lake_FacetConfigMap_insert(v_name_1110_, v_cfg_1111_, v_facetConfigs_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 6, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_lakeEnv_1113_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_lakeConfig_1114_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_lakeCache_1115_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_lakeArgs_x3f_1116_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_packages_1117_);
lean_ctor_set(v_reuseFailAlloc_1126_, 5, v_packageMap_1118_);
lean_ctor_set(v_reuseFailAlloc_1126_, 6, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1128_, lean_object* v_self_1129_){
_start:
{
lean_object* v_facetConfigs_1130_; lean_object* v___x_1131_; 
v_facetConfigs_1130_ = lean_ctor_get(v_self_1129_, 6);
v___x_1131_ = l_Lake_FacetConfigMap_get_x3f(v_name_1128_, v_facetConfigs_1130_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_box(0);
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_val_1133_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_val_1133_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1135_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1134_, v_val_1133_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1136_, lean_object* v_self_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1136_, v_self_1137_);
lean_dec_ref(v_self_1137_);
lean_dec(v_name_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1139_, size_t v_i_1140_, size_t v_stop_1141_, lean_object* v_b_1142_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_usize_dec_eq(v_i_1140_, v_stop_1141_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v_config_1145_; lean_object* v_dir_1146_; lean_object* v_buildDir_1147_; lean_object* v_binDir_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; 
v___x_1144_ = lean_array_uget_borrowed(v_as_1139_, v_i_1140_);
v_config_1145_ = lean_ctor_get(v___x_1144_, 6);
v_dir_1146_ = lean_ctor_get(v___x_1144_, 4);
v_buildDir_1147_ = lean_ctor_get(v_config_1145_, 5);
v_binDir_1148_ = lean_ctor_get(v_config_1145_, 8);
lean_inc_ref(v_buildDir_1147_);
v___x_1149_ = l_System_FilePath_normalize(v_buildDir_1147_);
lean_inc_ref(v_dir_1146_);
v___x_1150_ = l_Lake_joinRelative(v_dir_1146_, v___x_1149_);
lean_inc_ref(v_binDir_1148_);
v___x_1151_ = l_System_FilePath_normalize(v_binDir_1148_);
v___x_1152_ = l_Lake_joinRelative(v___x_1150_, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_b_1142_);
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_add(v_i_1140_, v___x_1154_);
v_i_1140_ = v___x_1155_;
v_b_1142_ = v___x_1153_;
goto _start;
}
else
{
return v_b_1142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1157_, lean_object* v_i_1158_, lean_object* v_stop_1159_, lean_object* v_b_1160_){
_start:
{
size_t v_i_boxed_1161_; size_t v_stop_boxed_1162_; lean_object* v_res_1163_; 
v_i_boxed_1161_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_stop_boxed_1162_ = lean_unbox_usize(v_stop_1159_);
lean_dec(v_stop_1159_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1157_, v_i_boxed_1161_, v_stop_boxed_1162_, v_b_1160_);
lean_dec_ref(v_as_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1164_){
_start:
{
lean_object* v_packages_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_packages_1165_ = lean_ctor_get(v_self_1164_, 4);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = lean_array_get_size(v_packages_1165_);
v___x_1169_ = lean_nat_dec_lt(v___x_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
return v___x_1166_;
}
else
{
size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = lean_usize_of_nat(v___x_1168_);
v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1165_, v___x_1170_, v___x_1171_, v___x_1166_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lake_Workspace_binPath(v_self_1173_);
lean_dec_ref(v_self_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1175_, size_t v_i_1176_, size_t v_stop_1177_, lean_object* v_b_1178_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_eq(v_i_1176_, v_stop_1177_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v_config_1181_; lean_object* v_dir_1182_; lean_object* v_buildDir_1183_; lean_object* v_leanLibDir_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; 
v___x_1180_ = lean_array_uget_borrowed(v_as_1175_, v_i_1176_);
v_config_1181_ = lean_ctor_get(v___x_1180_, 6);
v_dir_1182_ = lean_ctor_get(v___x_1180_, 4);
v_buildDir_1183_ = lean_ctor_get(v_config_1181_, 5);
v_leanLibDir_1184_ = lean_ctor_get(v_config_1181_, 6);
lean_inc_ref(v_buildDir_1183_);
v___x_1185_ = l_System_FilePath_normalize(v_buildDir_1183_);
lean_inc_ref(v_dir_1182_);
v___x_1186_ = l_Lake_joinRelative(v_dir_1182_, v___x_1185_);
lean_inc_ref(v_leanLibDir_1184_);
v___x_1187_ = l_System_FilePath_normalize(v_leanLibDir_1184_);
v___x_1188_ = l_Lake_joinRelative(v___x_1186_, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v_b_1178_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1176_, v___x_1190_);
v_i_1176_ = v___x_1191_;
v_b_1178_ = v___x_1189_;
goto _start;
}
else
{
return v_b_1178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_stop_1195_, lean_object* v_b_1196_){
_start:
{
size_t v_i_boxed_1197_; size_t v_stop_boxed_1198_; lean_object* v_res_1199_; 
v_i_boxed_1197_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_stop_boxed_1198_ = lean_unbox_usize(v_stop_1195_);
lean_dec(v_stop_1195_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1193_, v_i_boxed_1197_, v_stop_boxed_1198_, v_b_1196_);
lean_dec_ref(v_as_1193_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1200_){
_start:
{
lean_object* v_packages_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_packages_1201_ = lean_ctor_get(v_self_1200_, 4);
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_array_get_size(v_packages_1201_);
v___x_1205_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
return v___x_1202_;
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1204_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1201_, v___x_1206_, v___x_1207_, v___x_1202_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* v_self_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lake_Workspace_leanPath(v_self_1209_);
lean_dec_ref(v_self_1209_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1211_, lean_object* v_as_1212_, size_t v_i_1213_, size_t v_stop_1214_, lean_object* v_b_1215_){
_start:
{
uint8_t v___x_1216_; 
v___x_1216_ = lean_usize_dec_eq(v_i_1213_, v_stop_1214_);
if (v___x_1216_ == 0)
{
size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v_kind_1220_; lean_object* v_config_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_sub(v_i_1213_, v___x_1217_);
v___x_1219_ = lean_array_uget_borrowed(v_as_1212_, v___x_1218_);
v_kind_1220_ = lean_ctor_get(v___x_1219_, 2);
v_config_1221_ = lean_ctor_get(v___x_1219_, 3);
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1223_ = lean_name_eq(v_kind_1220_, v___x_1222_);
if (v___x_1223_ == 0)
{
v_i_1213_ = v___x_1218_;
goto _start;
}
else
{
lean_object* v_config_1225_; lean_object* v_dir_1226_; lean_object* v_srcDir_1227_; lean_object* v_srcDir_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_config_1225_ = lean_ctor_get(v_x2_1211_, 6);
v_dir_1226_ = lean_ctor_get(v_x2_1211_, 4);
v_srcDir_1227_ = lean_ctor_get(v_config_1225_, 4);
v_srcDir_1228_ = lean_ctor_get(v_config_1221_, 1);
lean_inc_ref(v_srcDir_1227_);
v___x_1229_ = l_System_FilePath_normalize(v_srcDir_1227_);
lean_inc_ref(v_dir_1226_);
v___x_1230_ = l_Lake_joinRelative(v_dir_1226_, v___x_1229_);
lean_inc_ref(v_srcDir_1228_);
v___x_1231_ = l_Lake_joinRelative(v___x_1230_, v_srcDir_1228_);
v___x_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_b_1215_);
v_i_1213_ = v___x_1218_;
v_b_1215_ = v___x_1232_;
goto _start;
}
}
else
{
lean_dec_ref(v_x2_1211_);
return v_b_1215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1234_, lean_object* v_as_1235_, lean_object* v_i_1236_, lean_object* v_stop_1237_, lean_object* v_b_1238_){
_start:
{
size_t v_i_boxed_1239_; size_t v_stop_boxed_1240_; lean_object* v_res_1241_; 
v_i_boxed_1239_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_stop_boxed_1240_ = lean_unbox_usize(v_stop_1237_);
lean_dec(v_stop_1237_);
v_res_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1234_, v_as_1235_, v_i_boxed_1239_, v_stop_boxed_1240_, v_b_1238_);
lean_dec_ref(v_as_1235_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1242_, size_t v_i_1243_, size_t v_stop_1244_, lean_object* v_b_1245_){
_start:
{
lean_object* v___y_1247_; uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_eq(v_i_1243_, v_stop_1244_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v_targetDecls_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1252_ = lean_array_uget_borrowed(v_as_1242_, v_i_1243_);
v_targetDecls_1253_ = lean_ctor_get(v___x_1252_, 15);
v___x_1254_ = lean_array_get_size(v_targetDecls_1253_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_nat_dec_lt(v___x_1255_, v___x_1254_);
if (v___x_1256_ == 0)
{
v___y_1247_ = v_b_1245_;
goto v___jp_1246_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_usize_of_nat(v___x_1254_);
v___x_1258_ = ((size_t)0ULL);
lean_inc(v___x_1252_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1252_, v_targetDecls_1253_, v___x_1257_, v___x_1258_, v_b_1245_);
v___y_1247_ = v___x_1259_;
goto v___jp_1246_;
}
}
else
{
return v_b_1245_;
}
v___jp_1246_:
{
size_t v___x_1248_; size_t v___x_1249_; 
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_i_1243_, v___x_1248_);
v_i_1243_ = v___x_1249_;
v_b_1245_ = v___y_1247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1260_, lean_object* v_i_1261_, lean_object* v_stop_1262_, lean_object* v_b_1263_){
_start:
{
size_t v_i_boxed_1264_; size_t v_stop_boxed_1265_; lean_object* v_res_1266_; 
v_i_boxed_1264_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_stop_boxed_1265_ = lean_unbox_usize(v_stop_1262_);
lean_dec(v_stop_1262_);
v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1260_, v_i_boxed_1264_, v_stop_boxed_1265_, v_b_1263_);
lean_dec_ref(v_as_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1267_){
_start:
{
lean_object* v_packages_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_packages_1268_ = lean_ctor_get(v_self_1267_, 4);
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_array_get_size(v_packages_1268_);
v___x_1272_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
return v___x_1269_;
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = lean_usize_of_nat(v___x_1271_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1268_, v___x_1273_, v___x_1274_, v___x_1269_);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lake_Workspace_leanSrcPath(v_self_1276_);
lean_dec_ref(v_self_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1278_, size_t v_i_1279_, size_t v_stop_1280_, lean_object* v_b_1281_){
_start:
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_usize_dec_eq(v_i_1279_, v_stop_1280_);
if (v___x_1282_ == 0)
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; lean_object* v_config_1286_; lean_object* v_dir_1287_; lean_object* v_buildDir_1288_; lean_object* v_nativeLibDir_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_sub(v_i_1279_, v___x_1283_);
v___x_1285_ = lean_array_uget_borrowed(v_as_1278_, v___x_1284_);
v_config_1286_ = lean_ctor_get(v___x_1285_, 6);
v_dir_1287_ = lean_ctor_get(v___x_1285_, 4);
v_buildDir_1288_ = lean_ctor_get(v_config_1286_, 5);
v_nativeLibDir_1289_ = lean_ctor_get(v_config_1286_, 7);
lean_inc_ref(v_buildDir_1288_);
v___x_1290_ = l_System_FilePath_normalize(v_buildDir_1288_);
lean_inc_ref(v_dir_1287_);
v___x_1291_ = l_Lake_joinRelative(v_dir_1287_, v___x_1290_);
lean_inc_ref(v_nativeLibDir_1289_);
v___x_1292_ = l_System_FilePath_normalize(v_nativeLibDir_1289_);
v___x_1293_ = l_Lake_joinRelative(v___x_1291_, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_b_1281_);
v_i_1279_ = v___x_1284_;
v_b_1281_ = v___x_1294_;
goto _start;
}
else
{
return v_b_1281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1296_, lean_object* v_i_1297_, lean_object* v_stop_1298_, lean_object* v_b_1299_){
_start:
{
size_t v_i_boxed_1300_; size_t v_stop_boxed_1301_; lean_object* v_res_1302_; 
v_i_boxed_1300_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_stop_boxed_1301_ = lean_unbox_usize(v_stop_1298_);
lean_dec(v_stop_1298_);
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1296_, v_i_boxed_1300_, v_stop_boxed_1301_, v_b_1299_);
lean_dec_ref(v_as_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1303_){
_start:
{
lean_object* v_packages_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_packages_1304_ = lean_ctor_get(v_self_1303_, 4);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_array_get_size(v_packages_1304_);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_nat_dec_lt(v___x_1307_, v___x_1306_);
if (v___x_1308_ == 0)
{
return v___x_1305_;
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_usize_of_nat(v___x_1306_);
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1304_, v___x_1309_, v___x_1310_, v___x_1305_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lake_Workspace_sharedLibPath(v_self_1312_);
lean_dec_ref(v_self_1312_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = l_System_Platform_isWindows;
if (v___x_1315_ == 0)
{
lean_object* v_lakeEnv_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v_lakeEnv_1316_ = lean_ctor_get(v_self_1314_, 0);
v___x_1317_ = l_Lake_Workspace_binPath(v_self_1314_);
v___x_1318_ = l_Lake_Env_path(v_lakeEnv_1316_);
v___x_1319_ = l_List_appendTR___redArg(v___x_1317_, v___x_1318_);
return v___x_1319_;
}
else
{
lean_object* v_lakeEnv_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_lakeEnv_1320_ = lean_ctor_get(v_self_1314_, 0);
v___x_1321_ = l_Lake_Workspace_binPath(v_self_1314_);
v___x_1322_ = l_Lake_Workspace_sharedLibPath(v_self_1314_);
v___x_1323_ = l_List_appendTR___redArg(v___x_1321_, v___x_1322_);
v___x_1324_ = l_Lake_Env_path(v_lakeEnv_1320_);
v___x_1325_ = l_List_appendTR___redArg(v___x_1323_, v___x_1324_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lake_Workspace_augmentedPath(v_self_1326_);
lean_dec_ref(v_self_1326_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1328_){
_start:
{
lean_object* v_lakeEnv_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_lakeEnv_1329_ = lean_ctor_get(v_self_1328_, 0);
v___x_1330_ = l_Lake_Workspace_leanPath(v_self_1328_);
v___x_1331_ = l_Lake_Env_leanPath(v_lakeEnv_1329_);
v___x_1332_ = l_List_appendTR___redArg(v___x_1330_, v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lake_Workspace_augmentedLeanPath(v_self_1333_);
lean_dec_ref(v_self_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1335_){
_start:
{
lean_object* v_lakeEnv_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_lakeEnv_1336_ = lean_ctor_get(v_self_1335_, 0);
v___x_1337_ = l_Lake_Workspace_leanSrcPath(v_self_1335_);
v___x_1338_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1336_);
v___x_1339_ = l_List_appendTR___redArg(v___x_1337_, v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1340_);
lean_dec_ref(v_self_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1342_){
_start:
{
lean_object* v_lakeEnv_1343_; lean_object* v_lean_1344_; lean_object* v_initSharedLibPath_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_lakeEnv_1343_ = lean_ctor_get(v_self_1342_, 0);
v_lean_1344_ = lean_ctor_get(v_lakeEnv_1343_, 1);
v_initSharedLibPath_1345_ = lean_ctor_get(v_lakeEnv_1343_, 17);
lean_inc(v_initSharedLibPath_1345_);
v___x_1346_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1344_);
v___x_1347_ = l_Lake_Workspace_sharedLibPath(v_self_1342_);
lean_dec_ref(v_self_1342_);
v___x_1348_ = l_List_appendTR___redArg(v___x_1346_, v___x_1347_);
v___x_1349_ = l_List_appendTR___redArg(v___x_1348_, v_initSharedLibPath_1345_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0(lean_object* v_x_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__0___closed__1));
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0___boxed(lean_object* v_x_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_x_1355_);
lean_dec(v_x_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1(uint8_t v_b_1363_){
_start:
{
if (v_b_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__1));
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__3));
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___boxed(lean_object* v_b_1366_){
_start:
{
uint8_t v_b_boxed_1367_; lean_object* v_res_1368_; 
v_b_boxed_1367_ = lean_unbox(v_b_1366_);
v_res_1368_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_b_boxed_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1376_){
_start:
{
lean_object* v_lakeEnv_1377_; lean_object* v_lakeCache_1378_; lean_object* v_packages_1379_; lean_object* v_enableArtifactCache_x3f_1380_; lean_object* v_restoreAllArtifacts_x3f_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1440_; lean_object* v___y_1441_; uint8_t v_val_1442_; lean_object* v___x_1444_; lean_object* v___y_1446_; uint8_t v_val_1459_; 
v_lakeEnv_1377_ = lean_ctor_get(v_self_1376_, 0);
v_lakeCache_1378_ = lean_ctor_get(v_self_1376_, 2);
v_packages_1379_ = lean_ctor_get(v_self_1376_, 4);
v_enableArtifactCache_x3f_1380_ = lean_ctor_get(v_lakeEnv_1377_, 6);
v_restoreAllArtifacts_x3f_1381_ = lean_ctor_get(v_lakeEnv_1377_, 7);
lean_inc_ref(v_lakeEnv_1377_);
v___x_1382_ = l_Lake_Env_baseVars(v_lakeEnv_1377_);
v___x_1383_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1378_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_lakeCache_1378_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1444_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (lean_obj_tag(v_enableArtifactCache_x3f_1380_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_config_1463_; lean_object* v_enableArtifactCache_x3f_1464_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_fget_borrowed(v_packages_1379_, v___x_1461_);
v_config_1463_ = lean_ctor_get(v___x_1462_, 6);
v_enableArtifactCache_x3f_1464_ = lean_ctor_get(v_config_1463_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1464_) == 1)
{
lean_object* v_val_1465_; uint8_t v___x_1466_; 
v_val_1465_ = lean_ctor_get(v_enableArtifactCache_x3f_1464_, 0);
v___x_1466_ = lean_unbox(v_val_1465_);
v_val_1459_ = v___x_1466_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_enableArtifactCache_x3f_1464_);
v___y_1446_ = v___x_1467_;
goto v___jp_1445_;
}
}
else
{
lean_object* v_val_1468_; uint8_t v___x_1469_; 
v_val_1468_ = lean_ctor_get(v_enableArtifactCache_x3f_1380_, 0);
v___x_1469_ = lean_unbox(v_val_1468_);
v_val_1459_ = v___x_1469_;
goto v___jp_1458_;
}
v___jp_1386_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v_vars_1408_; uint8_t v___x_1409_; 
lean_inc_ref(v___y_1389_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___y_1389_);
lean_ctor_set(v___x_1393_, 1, v___y_1392_);
v___x_1394_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1395_ = l_Lake_Workspace_augmentedPath(v_self_1376_);
v___x_1396_ = l_System_SearchPath_toString(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1394_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = lean_unsigned_to_nat(7u);
v___x_1400_ = lean_mk_empty_array_with_capacity(v___x_1399_);
v___x_1401_ = lean_array_push(v___x_1400_, v___x_1385_);
v___x_1402_ = lean_array_push(v___x_1401_, v___y_1387_);
v___x_1403_ = lean_array_push(v___x_1402_, v___y_1391_);
v___x_1404_ = lean_array_push(v___x_1403_, v___y_1390_);
v___x_1405_ = lean_array_push(v___x_1404_, v___y_1388_);
v___x_1406_ = lean_array_push(v___x_1405_, v___x_1393_);
v___x_1407_ = lean_array_push(v___x_1406_, v___x_1398_);
v_vars_1408_ = l_Array_append___redArg(v___x_1382_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = l_System_Platform_isWindows;
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1410_ = l_Lake_sharedLibPathEnvVar;
v___x_1411_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1376_);
v___x_1412_ = l_System_SearchPath_toString(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1410_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_array_push(v_vars_1408_, v___x_1414_);
return v___x_1415_;
}
else
{
lean_dec_ref(v_self_1376_);
return v_vars_1408_;
}
}
v___jp_1416_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_config_1422_; uint8_t v_bootstrap_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_array_fget_borrowed(v_packages_1379_, v___x_1420_);
v_config_1422_ = lean_ctor_get(v___x_1421_, 6);
v_bootstrap_1423_ = lean_ctor_get_uint8(v_config_1422_, sizeof(void*)*28);
lean_inc_ref(v___y_1418_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___y_1418_);
lean_ctor_set(v___x_1424_, 1, v___y_1419_);
v___x_1425_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
v___x_1426_ = l_Lake_Workspace_augmentedLeanPath(v_self_1376_);
v___x_1427_ = l_System_SearchPath_toString(v___x_1426_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1425_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1431_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1376_);
v___x_1432_ = l_System_SearchPath_toString(v___x_1431_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1430_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
if (v_bootstrap_1423_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = l_Lake_Env_leanGithash(v_lakeEnv_1377_);
v___x_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
v___y_1387_ = v___y_1417_;
v___y_1388_ = v___x_1434_;
v___y_1389_ = v___x_1435_;
v___y_1390_ = v___x_1429_;
v___y_1391_ = v___x_1424_;
v___y_1392_ = v___x_1437_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_box(0);
v___y_1387_ = v___y_1417_;
v___y_1388_ = v___x_1434_;
v___y_1389_ = v___x_1435_;
v___y_1390_ = v___x_1429_;
v___y_1391_ = v___x_1424_;
v___y_1392_ = v___x_1438_;
goto v___jp_1386_;
}
}
v___jp_1439_:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1442_);
v___y_1417_ = v___y_1440_;
v___y_1418_ = v___y_1441_;
v___y_1419_ = v___x_1443_;
goto v___jp_1416_;
}
v___jp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1444_);
lean_ctor_set(v___x_1447_, 1, v___y_1446_);
v___x_1448_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__6));
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1381_) == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_config_1451_; lean_object* v_restoreAllArtifacts_x3f_1452_; 
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_array_fget_borrowed(v_packages_1379_, v___x_1449_);
v_config_1451_ = lean_ctor_get(v___x_1450_, 6);
v_restoreAllArtifacts_x3f_1452_ = lean_ctor_get(v_config_1451_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1452_) == 1)
{
lean_object* v_val_1453_; uint8_t v___x_1454_; 
v_val_1453_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1452_, 0);
v___x_1454_ = lean_unbox(v_val_1453_);
v___y_1440_ = v___x_1447_;
v___y_1441_ = v___x_1448_;
v_val_1442_ = v___x_1454_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_restoreAllArtifacts_x3f_1452_);
v___y_1417_ = v___x_1447_;
v___y_1418_ = v___x_1448_;
v___y_1419_ = v___x_1455_;
goto v___jp_1416_;
}
}
else
{
lean_object* v_val_1456_; uint8_t v___x_1457_; 
v_val_1456_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1381_, 0);
v___x_1457_ = lean_unbox(v_val_1456_);
v___y_1440_ = v___x_1447_;
v___y_1441_ = v___x_1448_;
v_val_1442_ = v___x_1457_;
goto v___jp_1439_;
}
}
v___jp_1458_:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1459_);
v___y_1446_ = v___x_1460_;
goto v___jp_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1470_, size_t v_i_1471_, size_t v_stop_1472_, lean_object* v_b_1473_){
_start:
{
uint8_t v___x_1475_; 
v___x_1475_ = lean_usize_dec_eq(v_i_1471_, v_stop_1472_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_array_uget_borrowed(v_as_1470_, v_i_1471_);
lean_inc(v___x_1476_);
v___x_1477_ = l_Lake_Package_clean(v___x_1476_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; size_t v___x_1479_; size_t v___x_1480_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1471_, v___x_1479_);
v_i_1471_ = v___x_1480_;
v_b_1473_ = v_a_1478_;
goto _start;
}
else
{
return v___x_1477_;
}
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_b_1473_);
return v___x_1482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1483_, lean_object* v_i_1484_, lean_object* v_stop_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_){
_start:
{
size_t v_i_boxed_1488_; size_t v_stop_boxed_1489_; lean_object* v_res_1490_; 
v_i_boxed_1488_ = lean_unbox_usize(v_i_1484_);
lean_dec(v_i_1484_);
v_stop_boxed_1489_ = lean_unbox_usize(v_stop_1485_);
lean_dec(v_stop_1485_);
v_res_1490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1483_, v_i_boxed_1488_, v_stop_boxed_1489_, v_b_1486_);
lean_dec_ref(v_as_1483_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* v_self_1491_){
_start:
{
lean_object* v_packages_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v_packages_1493_ = lean_ctor_get(v_self_1491_, 4);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_array_get_size(v_packages_1493_);
v___x_1496_ = lean_box(0);
v___x_1497_ = lean_nat_dec_lt(v___x_1494_, v___x_1495_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
return v___x_1498_;
}
else
{
size_t v___x_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = ((size_t)0ULL);
v___x_1500_ = lean_usize_of_nat(v___x_1495_);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1493_, v___x_1499_, v___x_1500_, v___x_1496_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lake_Workspace_clean(v_self_1502_);
lean_dec_ref(v_self_1502_);
return v_res_1504_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanExe(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ExternLib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_TargetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakeConfig(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanExe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_TargetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LakeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Util_OpaqueType(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanExe(uint8_t builtin);
lean_object* initialize_Lake_Config_ExternLib(uint8_t builtin);
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_TargetConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_LakeConfig(uint8_t builtin);
lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanExe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_TargetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LakeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Workspace(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lake.Config.Workspace
// Imports: public import Lake.Config.Env public import Lake.Config.LeanExe public import Lake.Config.ExternLib public import Lake.Config.FacetConfig public import Lake.Config.TargetConfig public import Lake.Config.LakeConfig meta import Lake.Util.OpaqueType import Lean.DocString.Syntax
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Package_isLocalModule(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_get_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lake_Package_isBuildableModule(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
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
static const lean_string_object l_Lake_computeLakeCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_computeLakeCache___closed__0 = (const lean_object*)&l_Lake_computeLakeCache___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_computeLakeCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeLakeCache___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_Raw___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_Raw___private__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object*);
static const lean_string_object l_Lake_Workspace_packageOverridesFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "package-overrides.json"};
static const lean_object* l_Lake_Workspace_packageOverridesFile___closed__0 = (const lean_object*)&l_Lake_Workspace_packageOverridesFile___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object*);
static const lean_closure_object l_Lake_Workspace_addPackage_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_addPackage_x27___redArg___closed__0 = (const lean_object*)&l_Lake_Workspace_addPackage_x27___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Workspace_findPackageByName_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__0 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__0_value;
static const lean_closure_object l_Lake_Workspace_findPackageByName_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__1 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__1_value;
static const lean_closure_object l_Lake_Workspace_findPackageByName_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__2 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__2_value;
static const lean_closure_object l_Lake_Workspace_findPackageByName_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__3 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__3_value;
static const lean_closure_object l_Lake_Workspace_findPackageByName_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__4 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__4_value;
static const lean_closure_object l_Lake_Workspace_findPackageByName_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__5 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__5_value;
static const lean_closure_object l_Lake_Workspace_findPackageByName_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__6 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__6_value;
static const lean_ctor_object l_Lake_Workspace_findPackageByName_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__0_value),((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__1_value)}};
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__7 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__7_value;
static const lean_ctor_object l_Lake_Workspace_findPackageByName_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__7_value),((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__2_value),((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__3_value),((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__4_value),((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__5_value)}};
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__8 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__8_value;
static const lean_ctor_object l_Lake_Workspace_findPackageByName_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__8_value),((lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__6_value)}};
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__9 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__9_value;
static const lean_ctor_object l_Lake_Workspace_findPackageByName_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Workspace_findPackageByName_x3f___closed__10 = (const lean_object*)&l_Lake_Workspace_findPackageByName_x3f___closed__10_value;
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
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LAKE_CACHE_DIR"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__0 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__0_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__1 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__1_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LAKE_ARTIFACT_CACHE"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__2 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__2_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LEAN_PATH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__3 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__3_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LEAN_SRC_PATH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__4 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__4_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "LEAN_GITHASH"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__5 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__5_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__6 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__6_value;
static const lean_ctor_object l_Lake_Workspace_augmentedEnvVars___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__6_value)}};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__7 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__7_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__8 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__8_value;
static const lean_ctor_object l_Lake_Workspace_augmentedEnvVars___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__8_value)}};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__9 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__9_value;
static const lean_string_object l_Lake_Workspace_augmentedEnvVars___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__10 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__10_value;
static const lean_ctor_object l_Lake_Workspace_augmentedEnvVars___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__10_value)}};
static const lean_object* l_Lake_Workspace_augmentedEnvVars___closed__11 = (const lean_object*)&l_Lake_Workspace_augmentedEnvVars___closed__11_value;
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
v_bootstrap_5_ = lean_ctor_get_uint8(v_config_4_, sizeof(void*)*26);
if (v_bootstrap_5_ == 0)
{
lean_object* v_lakeCache_x3f_6_; 
v_lakeCache_x3f_6_ = lean_ctor_get(v_lakeEnv_3_, 7);
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
v_lakeSystemCache_x3f_13_ = lean_ctor_get(v_lakeEnv_3_, 8);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_Raw___private__1(lean_object* v_pkg_23_, lean_object* v_lakeEnv_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lake_computeLakeCache(v_pkg_23_, v_lakeEnv_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_Raw___private__1___boxed(lean_object* v_pkg_26_, lean_object* v_lakeEnv_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_Workspace_Raw___private__1(v_pkg_26_, v_lakeEnv_27_);
lean_dec_ref(v_lakeEnv_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(lean_object* v_a_29_){
_start:
{
lean_inc_ref(v_a_29_);
return v_a_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk___boxed(lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(v_a_30_);
lean_dec_ref(v_a_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(lean_object* v_a_34_){
_start:
{
lean_inc(v_a_34_);
return v_a_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet___boxed(lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(v_a_35_);
lean_dec(v_a_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(lean_object* v_inst_39_){
_start:
{
lean_inc_ref(v_inst_39_);
return v_inst_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace___boxed(lean_object* v_inst_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(v_inst_40_);
lean_dec_ref(v_inst_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(lean_object* v_self_47_, lean_object* v_as_48_, size_t v_i_49_, size_t v_stop_50_, lean_object* v_b_51_){
_start:
{
lean_object* v___y_53_; uint8_t v___x_60_; 
v___x_60_ = lean_usize_dec_eq(v_i_49_, v_stop_50_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_74_; 
v___x_61_ = lean_array_uget_borrowed(v_as_48_, v_i_49_);
v___x_74_ = l_Lake_Package_findTargetDecl_x3f(v___x_61_, v_self_47_);
if (lean_obj_tag(v___x_74_) == 0)
{
goto v___jp_62_;
}
else
{
lean_object* v_val_75_; lean_object* v_kind_76_; lean_object* v_config_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_val_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v___x_74_);
v_kind_76_ = lean_ctor_get(v_val_75_, 2);
lean_inc(v_kind_76_);
v_config_77_ = lean_ctor_get(v_val_75_, 3);
lean_inc(v_config_77_);
lean_dec(v_val_75_);
v___x_78_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_79_ = lean_name_eq(v_kind_76_, v___x_78_);
lean_dec(v_kind_76_);
if (v___x_79_ == 0)
{
lean_dec(v_config_77_);
goto v___jp_62_;
}
else
{
lean_object* v_roots_80_; lean_object* v___x_81_; 
v_roots_80_ = lean_ctor_get(v_config_77_, 2);
lean_inc_ref(v_roots_80_);
lean_dec(v_config_77_);
v___x_81_ = l_Array_append___redArg(v_b_51_, v_roots_80_);
lean_dec_ref(v_roots_80_);
v___y_53_ = v___x_81_;
goto v___jp_52_;
}
}
v___jp_62_:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lake_Package_findTargetDecl_x3f(v___x_61_, v_self_47_);
if (lean_obj_tag(v___x_63_) == 0)
{
goto v___jp_57_;
}
else
{
lean_object* v_val_64_; lean_object* v_kind_65_; lean_object* v_config_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_val_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref(v___x_63_);
v_kind_65_ = lean_ctor_get(v_val_64_, 2);
lean_inc(v_kind_65_);
v_config_66_ = lean_ctor_get(v_val_64_, 3);
lean_inc(v_config_66_);
lean_dec(v_val_64_);
v___x_67_ = l_Lake_LeanExe_keyword;
v___x_68_ = lean_name_eq(v_kind_65_, v___x_67_);
lean_dec(v_kind_65_);
if (v___x_68_ == 0)
{
lean_dec(v_config_66_);
goto v___jp_57_;
}
else
{
lean_object* v_root_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_root_69_ = lean_ctor_get(v_config_66_, 2);
lean_inc(v_root_69_);
lean_dec(v_config_66_);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_mk_empty_array_with_capacity(v___x_70_);
v___x_72_ = lean_array_push(v___x_71_, v_root_69_);
v___x_73_ = l_Array_append___redArg(v_b_51_, v___x_72_);
lean_dec_ref(v___x_72_);
v___y_53_ = v___x_73_;
goto v___jp_52_;
}
}
}
}
else
{
return v_b_51_;
}
v___jp_52_:
{
size_t v___x_54_; size_t v___x_55_; 
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_add(v_i_49_, v___x_54_);
v_i_49_ = v___x_55_;
v_b_51_ = v___y_53_;
goto _start;
}
v___jp_57_:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0));
v___x_59_ = l_Array_append___redArg(v_b_51_, v___x_58_);
v___y_53_ = v___x_59_;
goto v___jp_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___boxed(lean_object* v_self_82_, lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_, lean_object* v_b_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_82_, v_as_83_, v_i_boxed_87_, v_stop_boxed_88_, v_b_86_);
lean_dec_ref(v_as_83_);
lean_dec_ref(v_self_82_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots(lean_object* v_self_92_){
_start:
{
lean_object* v_defaultTargets_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_defaultTargets_93_ = lean_ctor_get(v_self_92_, 15);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = ((lean_object*)(l_Lake_Package_defaultTargetRoots___closed__0));
v___x_96_ = lean_array_get_size(v_defaultTargets_93_);
v___x_97_ = lean_nat_dec_lt(v___x_94_, v___x_96_);
if (v___x_97_ == 0)
{
return v___x_95_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = lean_nat_dec_le(v___x_96_, v___x_96_);
if (v___x_98_ == 0)
{
if (v___x_97_ == 0)
{
return v___x_95_;
}
else
{
size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; 
v___x_99_ = ((size_t)0ULL);
v___x_100_ = lean_usize_of_nat(v___x_96_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_92_, v_defaultTargets_93_, v___x_99_, v___x_100_, v___x_95_);
return v___x_101_;
}
}
else
{
size_t v___x_102_; size_t v___x_103_; lean_object* v___x_104_; 
v___x_102_ = ((size_t)0ULL);
v___x_103_ = lean_usize_of_nat(v___x_96_);
v___x_104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_92_, v_defaultTargets_93_, v___x_102_, v___x_103_, v___x_95_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots___boxed(lean_object* v_self_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lake_Package_defaultTargetRoots(v_self_105_);
lean_dec_ref(v_self_105_);
return v_res_106_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(lean_object* v_ws_107_){
_start:
{
lean_object* v_root_108_; lean_object* v_config_109_; uint8_t v_bootstrap_110_; 
v_root_108_ = lean_ctor_get(v_ws_107_, 0);
v_config_109_ = lean_ctor_get(v_root_108_, 6);
v_bootstrap_110_ = lean_ctor_get_uint8(v_config_109_, sizeof(void*)*26);
return v_bootstrap_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(lean_object* v_ws_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(v_ws_111_);
lean_dec_ref(v_ws_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object* v_self_114_){
_start:
{
lean_object* v_root_115_; lean_object* v_dir_116_; 
v_root_115_ = lean_ctor_get(v_self_114_, 0);
v_dir_116_ = lean_ctor_get(v_root_115_, 4);
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
lean_object* v_root_120_; lean_object* v_config_121_; lean_object* v_toWorkspaceConfig_122_; 
v_root_120_ = lean_ctor_get(v_self_119_, 0);
v_config_121_ = lean_ctor_get(v_root_120_, 6);
v_toWorkspaceConfig_122_ = lean_ctor_get(v_config_121_, 0);
lean_inc_ref(v_toWorkspaceConfig_122_);
return v_toWorkspaceConfig_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object* v_self_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lake_Workspace_config(v_self_123_);
lean_dec_ref(v_self_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object* v_self_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lake_defaultLakeDir;
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object* v_self_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lake_Workspace_relLakeDir(v_self_127_);
lean_dec_ref(v_self_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object* v_self_129_){
_start:
{
lean_object* v_root_130_; lean_object* v_dir_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_root_130_ = lean_ctor_get(v_self_129_, 0);
lean_inc_ref(v_root_130_);
lean_dec_ref(v_self_129_);
v_dir_131_ = lean_ctor_get(v_root_130_, 4);
lean_inc_ref(v_dir_131_);
lean_dec_ref(v_root_130_);
v___x_132_ = l_Lake_defaultLakeDir;
v___x_133_ = l_Lake_joinRelative(v_dir_131_, v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f(lean_object* v_ws_134_){
_start:
{
lean_object* v_lakeEnv_135_; lean_object* v_enableArtifactCache_x3f_136_; 
v_lakeEnv_135_ = lean_ctor_get(v_ws_134_, 1);
v_enableArtifactCache_x3f_136_ = lean_ctor_get(v_lakeEnv_135_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_136_) == 0)
{
lean_object* v_root_137_; lean_object* v_config_138_; lean_object* v_enableArtifactCache_x3f_139_; 
v_root_137_ = lean_ctor_get(v_ws_134_, 0);
v_config_138_ = lean_ctor_get(v_root_137_, 6);
v_enableArtifactCache_x3f_139_ = lean_ctor_get(v_config_138_, 24);
lean_inc(v_enableArtifactCache_x3f_139_);
return v_enableArtifactCache_x3f_139_;
}
else
{
lean_inc_ref(v_enableArtifactCache_x3f_136_);
return v_enableArtifactCache_x3f_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f___boxed(lean_object* v_ws_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lake_Workspace_enableArtifactCache_x3f(v_ws_140_);
lean_dec_ref(v_ws_140_);
return v_res_141_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_enableArtifactCache(lean_object* v_ws_142_){
_start:
{
lean_object* v_lakeEnv_143_; lean_object* v_enableArtifactCache_x3f_144_; 
v_lakeEnv_143_ = lean_ctor_get(v_ws_142_, 1);
v_enableArtifactCache_x3f_144_ = lean_ctor_get(v_lakeEnv_143_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_144_) == 0)
{
lean_object* v_root_145_; lean_object* v_config_146_; lean_object* v_enableArtifactCache_x3f_147_; 
v_root_145_ = lean_ctor_get(v_ws_142_, 0);
v_config_146_ = lean_ctor_get(v_root_145_, 6);
v_enableArtifactCache_x3f_147_ = lean_ctor_get(v_config_146_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_147_) == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
else
{
lean_object* v_val_149_; uint8_t v___x_150_; 
v_val_149_ = lean_ctor_get(v_enableArtifactCache_x3f_147_, 0);
v___x_150_ = lean_unbox(v_val_149_);
return v___x_150_;
}
}
else
{
lean_object* v_val_151_; uint8_t v___x_152_; 
v_val_151_ = lean_ctor_get(v_enableArtifactCache_x3f_144_, 0);
v___x_152_ = lean_unbox(v_val_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache___boxed(lean_object* v_ws_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lake_Workspace_enableArtifactCache(v_ws_153_);
lean_dec_ref(v_ws_153_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object* v_ws_156_){
_start:
{
lean_object* v_lakeEnv_157_; lean_object* v_enableArtifactCache_x3f_158_; 
v_lakeEnv_157_ = lean_ctor_get(v_ws_156_, 1);
v_enableArtifactCache_x3f_158_ = lean_ctor_get(v_lakeEnv_157_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_158_) == 0)
{
lean_object* v_root_159_; lean_object* v_config_160_; lean_object* v_enableArtifactCache_x3f_161_; 
v_root_159_ = lean_ctor_get(v_ws_156_, 0);
v_config_160_ = lean_ctor_get(v_root_159_, 6);
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
v_val_165_ = lean_ctor_get(v_enableArtifactCache_x3f_158_, 0);
v___x_166_ = lean_unbox(v_val_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheWritable___boxed(lean_object* v_ws_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_167_);
lean_dec_ref(v_ws_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheEnabled(lean_object* v_ws_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheEnabled___boxed(lean_object* v_ws_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lake_Workspace_isRootArtifactCacheEnabled(v_ws_172_);
lean_dec_ref(v_ws_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f(lean_object* v_ws_175_){
_start:
{
lean_object* v_root_176_; lean_object* v_config_177_; lean_object* v_restoreAllArtifacts_x3f_178_; 
v_root_176_ = lean_ctor_get(v_ws_175_, 0);
v_config_177_ = lean_ctor_get(v_root_176_, 6);
v_restoreAllArtifacts_x3f_178_ = lean_ctor_get(v_config_177_, 25);
lean_inc(v_restoreAllArtifacts_x3f_178_);
return v_restoreAllArtifacts_x3f_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(lean_object* v_ws_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lake_Workspace_restoreAllArtifacts_x3f(v_ws_179_);
lean_dec_ref(v_ws_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain(lean_object* v_ws_181_){
_start:
{
lean_object* v_lakeEnv_182_; lean_object* v_toolchain_183_; 
v_lakeEnv_182_ = lean_ctor_get(v_ws_181_, 1);
v_toolchain_183_ = lean_ctor_get(v_lakeEnv_182_, 18);
lean_inc_ref(v_toolchain_183_);
return v_toolchain_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain___boxed(lean_object* v_ws_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lake_Workspace_cacheToolchain(v_ws_184_);
lean_dec_ref(v_ws_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService(lean_object* v_ws_186_){
_start:
{
lean_object* v_lakeConfig_187_; lean_object* v_defaultCacheService_188_; 
v_lakeConfig_187_ = lean_ctor_get(v_ws_186_, 2);
v_defaultCacheService_188_ = lean_ctor_get(v_lakeConfig_187_, 1);
lean_inc_ref(v_defaultCacheService_188_);
return v_defaultCacheService_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService___boxed(lean_object* v_ws_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lake_Workspace_defaultCacheService(v_ws_189_);
lean_dec_ref(v_ws_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f(lean_object* v_ws_191_){
_start:
{
lean_object* v_lakeConfig_192_; lean_object* v_defaultCacheUploadService_x3f_193_; 
v_lakeConfig_192_ = lean_ctor_get(v_ws_191_, 2);
v_defaultCacheUploadService_x3f_193_ = lean_ctor_get(v_lakeConfig_192_, 2);
lean_inc(v_defaultCacheUploadService_x3f_193_);
return v_defaultCacheUploadService_x3f_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(lean_object* v_ws_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_Workspace_defaultCacheUploadService_x3f(v_ws_194_);
lean_dec_ref(v_ws_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object* v_ws_196_, lean_object* v_service_197_){
_start:
{
lean_object* v_lakeConfig_198_; lean_object* v_cacheServices_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_lakeConfig_198_ = lean_ctor_get(v_ws_196_, 2);
v_cacheServices_199_ = lean_ctor_get(v_lakeConfig_198_, 3);
v___x_200_ = lean_box(0);
v___x_201_ = l_Lean_Name_str___override(v___x_200_, v_service_197_);
v___x_202_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_199_, v___x_201_);
lean_dec(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object* v_ws_203_, lean_object* v_service_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lake_Workspace_findCacheService_x3f(v_ws_203_, v_service_204_);
lean_dec_ref(v_ws_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* v_self_206_){
_start:
{
lean_object* v_root_207_; lean_object* v_config_208_; lean_object* v_toWorkspaceConfig_209_; lean_object* v___x_210_; 
v_root_207_ = lean_ctor_get(v_self_206_, 0);
lean_inc_ref(v_root_207_);
lean_dec_ref(v_self_206_);
v_config_208_ = lean_ctor_get(v_root_207_, 6);
lean_inc_ref(v_config_208_);
lean_dec_ref(v_root_207_);
v_toWorkspaceConfig_209_ = lean_ctor_get(v_config_208_, 0);
lean_inc_ref(v_toWorkspaceConfig_209_);
lean_dec_ref(v_config_208_);
v___x_210_ = l_System_FilePath_normalize(v_toWorkspaceConfig_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* v_self_211_){
_start:
{
lean_object* v_root_212_; lean_object* v_config_213_; lean_object* v_dir_214_; lean_object* v_toWorkspaceConfig_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_root_212_ = lean_ctor_get(v_self_211_, 0);
lean_inc_ref(v_root_212_);
lean_dec_ref(v_self_211_);
v_config_213_ = lean_ctor_get(v_root_212_, 6);
lean_inc_ref(v_config_213_);
v_dir_214_ = lean_ctor_get(v_root_212_, 4);
lean_inc_ref(v_dir_214_);
lean_dec_ref(v_root_212_);
v_toWorkspaceConfig_215_ = lean_ctor_get(v_config_213_, 0);
lean_inc_ref(v_toWorkspaceConfig_215_);
lean_dec_ref(v_config_213_);
v___x_216_ = l_System_FilePath_normalize(v_toWorkspaceConfig_215_);
v___x_217_ = l_Lake_joinRelative(v_dir_214_, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object* v_self_218_){
_start:
{
lean_object* v_root_219_; lean_object* v_config_220_; lean_object* v_toLeanConfig_221_; lean_object* v_moreLeanArgs_222_; 
v_root_219_ = lean_ctor_get(v_self_218_, 0);
v_config_220_ = lean_ctor_get(v_root_219_, 6);
v_toLeanConfig_221_ = lean_ctor_get(v_config_220_, 1);
v_moreLeanArgs_222_ = lean_ctor_get(v_toLeanConfig_221_, 1);
lean_inc_ref(v_moreLeanArgs_222_);
return v_moreLeanArgs_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object* v_self_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lake_Workspace_leanArgs(v_self_223_);
lean_dec_ref(v_self_223_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* v_self_225_){
_start:
{
lean_object* v_root_226_; lean_object* v_config_227_; lean_object* v_toLeanConfig_228_; lean_object* v_leanOptions_229_; lean_object* v___x_230_; 
v_root_226_ = lean_ctor_get(v_self_225_, 0);
v_config_227_ = lean_ctor_get(v_root_226_, 6);
v_toLeanConfig_228_ = lean_ctor_get(v_config_227_, 1);
v_leanOptions_229_ = lean_ctor_get(v_toLeanConfig_228_, 0);
v___x_230_ = l_Lean_LeanOptions_ofArray(v_leanOptions_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* v_self_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_Workspace_leanOptions(v_self_231_);
lean_dec_ref(v_self_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* v_self_233_){
_start:
{
lean_object* v_root_234_; lean_object* v_config_235_; lean_object* v_toLeanConfig_236_; lean_object* v_leanOptions_237_; lean_object* v_moreServerOptions_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_root_234_ = lean_ctor_get(v_self_233_, 0);
v_config_235_ = lean_ctor_get(v_root_234_, 6);
v_toLeanConfig_236_ = lean_ctor_get(v_config_235_, 1);
v_leanOptions_237_ = lean_ctor_get(v_toLeanConfig_236_, 0);
v_moreServerOptions_238_ = lean_ctor_get(v_toLeanConfig_236_, 4);
v___x_239_ = l_Lean_LeanOptions_ofArray(v_leanOptions_237_);
v___x_240_ = l_Lean_LeanOptions_appendArray(v___x_239_, v_moreServerOptions_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* v_self_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lake_Workspace_serverOptions(v_self_241_);
lean_dec_ref(v_self_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object* v_self_243_){
_start:
{
lean_object* v_root_244_; lean_object* v___x_245_; 
v_root_244_ = lean_ctor_get(v_self_243_, 0);
v___x_245_ = l_Lake_Package_defaultTargetRoots(v_root_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object* v_self_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_Workspace_defaultTargetRoots(v_self_246_);
lean_dec_ref(v_self_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* v_self_248_){
_start:
{
lean_object* v_root_249_; lean_object* v_dir_250_; lean_object* v_relManifestFile_251_; lean_object* v___x_252_; 
v_root_249_ = lean_ctor_get(v_self_248_, 0);
lean_inc_ref(v_root_249_);
lean_dec_ref(v_self_248_);
v_dir_250_ = lean_ctor_get(v_root_249_, 4);
lean_inc_ref(v_dir_250_);
v_relManifestFile_251_ = lean_ctor_get(v_root_249_, 9);
lean_inc_ref(v_relManifestFile_251_);
lean_dec_ref(v_root_249_);
v___x_252_ = l_Lake_joinRelative(v_dir_250_, v_relManifestFile_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* v_self_254_){
_start:
{
lean_object* v_root_255_; lean_object* v_dir_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_root_255_ = lean_ctor_get(v_self_254_, 0);
lean_inc_ref(v_root_255_);
lean_dec_ref(v_self_254_);
v_dir_256_ = lean_ctor_get(v_root_255_, 4);
lean_inc_ref(v_dir_256_);
lean_dec_ref(v_root_255_);
v___x_257_ = l_Lake_defaultLakeDir;
v___x_258_ = l_Lake_joinRelative(v_dir_256_, v___x_257_);
v___x_259_ = ((lean_object*)(l_Lake_Workspace_packageOverridesFile___closed__0));
v___x_260_ = l_Lake_joinRelative(v___x_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object* v_pkg_262_, lean_object* v_self_263_){
_start:
{
lean_object* v_root_264_; lean_object* v_lakeEnv_265_; lean_object* v_lakeConfig_266_; lean_object* v_lakeCache_267_; lean_object* v_lakeArgs_x3f_268_; lean_object* v_packages_269_; lean_object* v_packageMap_270_; lean_object* v_facetConfigs_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_282_; 
v_root_264_ = lean_ctor_get(v_self_263_, 0);
v_lakeEnv_265_ = lean_ctor_get(v_self_263_, 1);
v_lakeConfig_266_ = lean_ctor_get(v_self_263_, 2);
v_lakeCache_267_ = lean_ctor_get(v_self_263_, 3);
v_lakeArgs_x3f_268_ = lean_ctor_get(v_self_263_, 4);
v_packages_269_ = lean_ctor_get(v_self_263_, 5);
v_packageMap_270_ = lean_ctor_get(v_self_263_, 6);
v_facetConfigs_271_ = lean_ctor_get(v_self_263_, 7);
v_isSharedCheck_282_ = !lean_is_exclusive(v_self_263_);
if (v_isSharedCheck_282_ == 0)
{
v___x_273_ = v_self_263_;
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_facetConfigs_271_);
lean_inc(v_packageMap_270_);
lean_inc(v_packages_269_);
lean_inc(v_lakeArgs_x3f_268_);
lean_inc(v_lakeCache_267_);
lean_inc(v_lakeConfig_266_);
lean_inc(v_lakeEnv_265_);
lean_inc(v_root_264_);
lean_dec(v_self_263_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_keyName_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v_keyName_275_ = lean_ctor_get(v_pkg_262_, 2);
lean_inc(v_keyName_275_);
lean_inc_ref(v_pkg_262_);
v___x_276_ = lean_array_push(v_packages_269_, v_pkg_262_);
v___x_277_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_278_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_277_, v_keyName_275_, v_pkg_262_, v_packageMap_270_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 6, v___x_278_);
lean_ctor_set(v___x_273_, 5, v___x_276_);
v___x_280_ = v___x_273_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_root_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_lakeEnv_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_lakeConfig_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_lakeCache_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_lakeArgs_x3f_268_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_facetConfigs_271_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object* v_pkg_283_, lean_object* v_self_284_, lean_object* v_h_285_){
_start:
{
lean_object* v_root_286_; lean_object* v_lakeEnv_287_; lean_object* v_lakeConfig_288_; lean_object* v_lakeCache_289_; lean_object* v_lakeArgs_x3f_290_; lean_object* v_packages_291_; lean_object* v_packageMap_292_; lean_object* v_facetConfigs_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_304_; 
v_root_286_ = lean_ctor_get(v_self_284_, 0);
v_lakeEnv_287_ = lean_ctor_get(v_self_284_, 1);
v_lakeConfig_288_ = lean_ctor_get(v_self_284_, 2);
v_lakeCache_289_ = lean_ctor_get(v_self_284_, 3);
v_lakeArgs_x3f_290_ = lean_ctor_get(v_self_284_, 4);
v_packages_291_ = lean_ctor_get(v_self_284_, 5);
v_packageMap_292_ = lean_ctor_get(v_self_284_, 6);
v_facetConfigs_293_ = lean_ctor_get(v_self_284_, 7);
v_isSharedCheck_304_ = !lean_is_exclusive(v_self_284_);
if (v_isSharedCheck_304_ == 0)
{
v___x_295_ = v_self_284_;
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_facetConfigs_293_);
lean_inc(v_packageMap_292_);
lean_inc(v_packages_291_);
lean_inc(v_lakeArgs_x3f_290_);
lean_inc(v_lakeCache_289_);
lean_inc(v_lakeConfig_288_);
lean_inc(v_lakeEnv_287_);
lean_inc(v_root_286_);
lean_dec(v_self_284_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_304_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_keyName_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
v_keyName_297_ = lean_ctor_get(v_pkg_283_, 2);
lean_inc(v_keyName_297_);
lean_inc_ref(v_pkg_283_);
v___x_298_ = lean_array_push(v_packages_291_, v_pkg_283_);
v___x_299_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_300_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_299_, v_keyName_297_, v_pkg_283_, v_packageMap_292_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 6, v___x_300_);
lean_ctor_set(v___x_295_, 5, v___x_298_);
v___x_302_ = v___x_295_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_root_286_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_lakeEnv_287_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_lakeConfig_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_lakeCache_289_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_lakeArgs_x3f_290_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_facetConfigs_293_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_305_, lean_object* v_self_306_){
_start:
{
lean_object* v_root_307_; lean_object* v_lakeEnv_308_; lean_object* v_lakeConfig_309_; lean_object* v_lakeCache_310_; lean_object* v_lakeArgs_x3f_311_; lean_object* v_packages_312_; lean_object* v_packageMap_313_; lean_object* v_facetConfigs_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_354_; 
v_root_307_ = lean_ctor_get(v_self_306_, 0);
v_lakeEnv_308_ = lean_ctor_get(v_self_306_, 1);
v_lakeConfig_309_ = lean_ctor_get(v_self_306_, 2);
v_lakeCache_310_ = lean_ctor_get(v_self_306_, 3);
v_lakeArgs_x3f_311_ = lean_ctor_get(v_self_306_, 4);
v_packages_312_ = lean_ctor_get(v_self_306_, 5);
v_packageMap_313_ = lean_ctor_get(v_self_306_, 6);
v_facetConfigs_314_ = lean_ctor_get(v_self_306_, 7);
v_isSharedCheck_354_ = !lean_is_exclusive(v_self_306_);
if (v_isSharedCheck_354_ == 0)
{
v___x_316_ = v_self_306_;
v_isShared_317_ = v_isSharedCheck_354_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_facetConfigs_314_);
lean_inc(v_packageMap_313_);
lean_inc(v_packages_312_);
lean_inc(v_lakeArgs_x3f_311_);
lean_inc(v_lakeCache_310_);
lean_inc(v_lakeConfig_309_);
lean_inc(v_lakeEnv_308_);
lean_inc(v_root_307_);
lean_dec(v_self_306_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_354_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_baseName_318_; lean_object* v_keyName_319_; lean_object* v_origName_320_; lean_object* v_dir_321_; lean_object* v_relDir_322_; lean_object* v_config_323_; lean_object* v_configFile_324_; lean_object* v_relConfigFile_325_; lean_object* v_relManifestFile_326_; lean_object* v_scope_327_; lean_object* v_remoteUrl_328_; lean_object* v_depConfigs_329_; lean_object* v_targetDecls_330_; lean_object* v_targetDeclMap_331_; lean_object* v_defaultTargets_332_; lean_object* v_scripts_333_; lean_object* v_defaultScripts_334_; lean_object* v_postUpdateHooks_335_; lean_object* v_buildArchive_336_; lean_object* v_testDriver_337_; lean_object* v_lintDriver_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_352_; 
v_baseName_318_ = lean_ctor_get(v_pkg_305_, 1);
v_keyName_319_ = lean_ctor_get(v_pkg_305_, 2);
v_origName_320_ = lean_ctor_get(v_pkg_305_, 3);
v_dir_321_ = lean_ctor_get(v_pkg_305_, 4);
v_relDir_322_ = lean_ctor_get(v_pkg_305_, 5);
v_config_323_ = lean_ctor_get(v_pkg_305_, 6);
v_configFile_324_ = lean_ctor_get(v_pkg_305_, 7);
v_relConfigFile_325_ = lean_ctor_get(v_pkg_305_, 8);
v_relManifestFile_326_ = lean_ctor_get(v_pkg_305_, 9);
v_scope_327_ = lean_ctor_get(v_pkg_305_, 10);
v_remoteUrl_328_ = lean_ctor_get(v_pkg_305_, 11);
v_depConfigs_329_ = lean_ctor_get(v_pkg_305_, 12);
v_targetDecls_330_ = lean_ctor_get(v_pkg_305_, 13);
v_targetDeclMap_331_ = lean_ctor_get(v_pkg_305_, 14);
v_defaultTargets_332_ = lean_ctor_get(v_pkg_305_, 15);
v_scripts_333_ = lean_ctor_get(v_pkg_305_, 16);
v_defaultScripts_334_ = lean_ctor_get(v_pkg_305_, 17);
v_postUpdateHooks_335_ = lean_ctor_get(v_pkg_305_, 18);
v_buildArchive_336_ = lean_ctor_get(v_pkg_305_, 19);
v_testDriver_337_ = lean_ctor_get(v_pkg_305_, 20);
v_lintDriver_338_ = lean_ctor_get(v_pkg_305_, 21);
v_isSharedCheck_352_ = !lean_is_exclusive(v_pkg_305_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_pkg_305_, 0);
lean_dec(v_unused_353_);
v___x_340_ = v_pkg_305_;
v_isShared_341_ = v_isSharedCheck_352_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_lintDriver_338_);
lean_inc(v_testDriver_337_);
lean_inc(v_buildArchive_336_);
lean_inc(v_postUpdateHooks_335_);
lean_inc(v_defaultScripts_334_);
lean_inc(v_scripts_333_);
lean_inc(v_defaultTargets_332_);
lean_inc(v_targetDeclMap_331_);
lean_inc(v_targetDecls_330_);
lean_inc(v_depConfigs_329_);
lean_inc(v_remoteUrl_328_);
lean_inc(v_scope_327_);
lean_inc(v_relManifestFile_326_);
lean_inc(v_relConfigFile_325_);
lean_inc(v_configFile_324_);
lean_inc(v_config_323_);
lean_inc(v_relDir_322_);
lean_inc(v_dir_321_);
lean_inc(v_origName_320_);
lean_inc(v_keyName_319_);
lean_inc(v_baseName_318_);
lean_dec(v_pkg_305_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_352_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_342_ = lean_array_get_size(v_packages_312_);
lean_inc(v_keyName_319_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_342_);
v___x_344_ = v___x_340_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 22, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_baseName_318_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_keyName_319_);
lean_ctor_set(v_reuseFailAlloc_351_, 3, v_origName_320_);
lean_ctor_set(v_reuseFailAlloc_351_, 4, v_dir_321_);
lean_ctor_set(v_reuseFailAlloc_351_, 5, v_relDir_322_);
lean_ctor_set(v_reuseFailAlloc_351_, 6, v_config_323_);
lean_ctor_set(v_reuseFailAlloc_351_, 7, v_configFile_324_);
lean_ctor_set(v_reuseFailAlloc_351_, 8, v_relConfigFile_325_);
lean_ctor_set(v_reuseFailAlloc_351_, 9, v_relManifestFile_326_);
lean_ctor_set(v_reuseFailAlloc_351_, 10, v_scope_327_);
lean_ctor_set(v_reuseFailAlloc_351_, 11, v_remoteUrl_328_);
lean_ctor_set(v_reuseFailAlloc_351_, 12, v_depConfigs_329_);
lean_ctor_set(v_reuseFailAlloc_351_, 13, v_targetDecls_330_);
lean_ctor_set(v_reuseFailAlloc_351_, 14, v_targetDeclMap_331_);
lean_ctor_set(v_reuseFailAlloc_351_, 15, v_defaultTargets_332_);
lean_ctor_set(v_reuseFailAlloc_351_, 16, v_scripts_333_);
lean_ctor_set(v_reuseFailAlloc_351_, 17, v_defaultScripts_334_);
lean_ctor_set(v_reuseFailAlloc_351_, 18, v_postUpdateHooks_335_);
lean_ctor_set(v_reuseFailAlloc_351_, 19, v_buildArchive_336_);
lean_ctor_set(v_reuseFailAlloc_351_, 20, v_testDriver_337_);
lean_ctor_set(v_reuseFailAlloc_351_, 21, v_lintDriver_338_);
v___x_344_ = v_reuseFailAlloc_351_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
lean_inc_ref(v___x_344_);
v___x_345_ = lean_array_push(v_packages_312_, v___x_344_);
v___x_346_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_347_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_346_, v_keyName_319_, v___x_344_, v_packageMap_313_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 6, v___x_347_);
lean_ctor_set(v___x_316_, 5, v___x_345_);
v___x_349_ = v___x_316_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_root_307_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_lakeEnv_308_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_lakeConfig_309_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_lakeCache_310_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_lakeArgs_x3f_311_);
lean_ctor_set(v_reuseFailAlloc_350_, 5, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_350_, 6, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_350_, 7, v_facetConfigs_314_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_355_, lean_object* v_self_356_){
_start:
{
lean_object* v_packageMap_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_packageMap_357_ = lean_ctor_get(v_self_356_, 6);
lean_inc(v_packageMap_357_);
lean_dec_ref(v_self_356_);
v___x_358_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_359_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_358_, v_packageMap_357_, v_keyName_355_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_360_, lean_object* v___x_361_, lean_object* v___x_362_, lean_object* v_a_363_, lean_object* v_x_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_baseName_366_; uint8_t v___x_367_; 
v_baseName_366_ = lean_ctor_get(v_a_363_, 1);
v___x_367_ = lean_name_eq(v_baseName_366_, v_name_360_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
lean_dec_ref(v_a_363_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_361_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_dec_ref(v___x_361_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_a_363_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_362_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_373_, lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v_a_376_, lean_object* v_x_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_373_, v___x_374_, v___x_375_, v_a_376_, v_x_377_, v___y_378_);
lean_dec_ref(v___y_378_);
lean_dec(v_name_373_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_402_, lean_object* v_self_403_){
_start:
{
lean_object* v_packages_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___f_409_; size_t v_sz_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v_fst_413_; 
v_packages_404_ = lean_ctor_get(v_self_403_, 5);
lean_inc_ref(v_packages_404_);
lean_dec_ref(v_self_403_);
v___x_405_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__9));
v___x_406_ = lean_box(0);
v___x_407_ = lean_box(0);
v___x_408_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__10));
v___f_409_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_409_, 0, v_name_402_);
lean_closure_set(v___f_409_, 1, v___x_408_);
lean_closure_set(v___f_409_, 2, v___x_407_);
v_sz_410_ = lean_array_size(v_packages_404_);
v___x_411_ = ((size_t)0ULL);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_405_, v_packages_404_, v___f_409_, v_sz_410_, v___x_411_, v___x_408_);
v_fst_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_fst_413_);
lean_dec(v___x_412_);
if (lean_obj_tag(v_fst_413_) == 0)
{
return v___x_406_;
}
else
{
lean_object* v_val_414_; 
v_val_414_ = lean_ctor_get(v_fst_413_, 0);
lean_inc(v_val_414_);
lean_dec_ref(v_fst_413_);
return v_val_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_415_, lean_object* v_self_416_){
_start:
{
lean_object* v_packageMap_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_packageMap_417_ = lean_ctor_get(v_self_416_, 6);
lean_inc(v_packageMap_417_);
lean_dec_ref(v_self_416_);
v___x_418_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_419_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_418_, v_packageMap_417_, v_name_415_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_423_, lean_object* v_as_424_, size_t v_sz_425_, size_t v_i_426_, lean_object* v_b_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = lean_usize_dec_lt(v_i_426_, v_sz_425_);
if (v___x_428_ == 0)
{
lean_inc_ref(v_b_427_);
return v_b_427_;
}
else
{
lean_object* v_a_429_; lean_object* v_scripts_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_a_429_ = lean_array_uget_borrowed(v_as_424_, v_i_426_);
v_scripts_430_ = lean_ctor_get(v_a_429_, 16);
v___x_431_ = lean_box(0);
v___x_432_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_430_, v_script_423_);
if (lean_obj_tag(v___x_432_) == 1)
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_431_);
return v___x_434_;
}
else
{
lean_object* v___x_435_; size_t v___x_436_; size_t v___x_437_; 
lean_dec(v___x_432_);
v___x_435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_426_, v___x_436_);
v_i_426_ = v___x_437_;
v_b_427_ = v___x_435_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_439_, lean_object* v_as_440_, lean_object* v_sz_441_, lean_object* v_i_442_, lean_object* v_b_443_){
_start:
{
size_t v_sz_boxed_444_; size_t v_i_boxed_445_; lean_object* v_res_446_; 
v_sz_boxed_444_ = lean_unbox_usize(v_sz_441_);
lean_dec(v_sz_441_);
v_i_boxed_445_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_res_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_439_, v_as_440_, v_sz_boxed_444_, v_i_boxed_445_, v_b_443_);
lean_dec_ref(v_b_443_);
lean_dec_ref(v_as_440_);
lean_dec(v_script_439_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_447_, lean_object* v_self_448_){
_start:
{
lean_object* v_packages_449_; lean_object* v___x_450_; lean_object* v___x_451_; size_t v_sz_452_; size_t v___x_453_; lean_object* v___x_454_; lean_object* v_fst_455_; 
v_packages_449_ = lean_ctor_get(v_self_448_, 5);
v___x_450_ = lean_box(0);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_452_ = lean_array_size(v_packages_449_);
v___x_453_ = ((size_t)0ULL);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_447_, v_packages_449_, v_sz_452_, v___x_453_, v___x_451_);
v_fst_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_fst_455_);
lean_dec_ref(v___x_454_);
if (lean_obj_tag(v_fst_455_) == 0)
{
return v___x_450_;
}
else
{
lean_object* v_val_456_; 
v_val_456_ = lean_ctor_get(v_fst_455_, 0);
lean_inc(v_val_456_);
lean_dec_ref(v_fst_455_);
return v_val_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_457_, lean_object* v_self_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lake_Workspace_findScript_x3f(v_script_457_, v_self_458_);
lean_dec_ref(v_self_458_);
lean_dec(v_script_457_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_460_, lean_object* v_as_461_, size_t v_i_462_, size_t v_stop_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_eq(v_i_462_, v_stop_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_array_uget_borrowed(v_as_461_, v_i_462_);
v___x_466_ = l_Lake_Package_isLocalModule(v_mod_460_, v___x_465_);
if (v___x_466_ == 0)
{
size_t v___x_467_; size_t v___x_468_; 
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_add(v_i_462_, v___x_467_);
v_i_462_ = v___x_468_;
goto _start;
}
else
{
return v___x_466_;
}
}
else
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_471_, lean_object* v_as_472_, lean_object* v_i_473_, lean_object* v_stop_474_){
_start:
{
size_t v_i_boxed_475_; size_t v_stop_boxed_476_; uint8_t v_res_477_; lean_object* v_r_478_; 
v_i_boxed_475_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_stop_boxed_476_ = lean_unbox_usize(v_stop_474_);
lean_dec(v_stop_474_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_471_, v_as_472_, v_i_boxed_475_, v_stop_boxed_476_);
lean_dec_ref(v_as_472_);
lean_dec(v_mod_471_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_479_, lean_object* v_self_480_){
_start:
{
lean_object* v_packages_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_packages_481_ = lean_ctor_get(v_self_480_, 5);
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_array_get_size(v_packages_481_);
v___x_484_ = lean_nat_dec_lt(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
return v___x_484_;
}
else
{
if (v___x_484_ == 0)
{
return v___x_484_;
}
else
{
size_t v___x_485_; size_t v___x_486_; uint8_t v___x_487_; 
v___x_485_ = ((size_t)0ULL);
v___x_486_ = lean_usize_of_nat(v___x_483_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_479_, v_packages_481_, v___x_485_, v___x_486_);
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_488_, lean_object* v_self_489_){
_start:
{
uint8_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_Lake_Workspace_isLocalModule(v_mod_488_, v_self_489_);
lean_dec_ref(v_self_489_);
lean_dec(v_mod_488_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_492_, lean_object* v_as_493_, size_t v_i_494_, size_t v_stop_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_eq(v_i_494_, v_stop_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_array_uget_borrowed(v_as_493_, v_i_494_);
v___x_498_ = l_Lake_Package_isBuildableModule(v_mod_492_, v___x_497_);
if (v___x_498_ == 0)
{
size_t v___x_499_; size_t v___x_500_; 
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_494_, v___x_499_);
v_i_494_ = v___x_500_;
goto _start;
}
else
{
return v___x_498_;
}
}
else
{
uint8_t v___x_502_; 
v___x_502_ = 0;
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_503_, lean_object* v_as_504_, lean_object* v_i_505_, lean_object* v_stop_506_){
_start:
{
size_t v_i_boxed_507_; size_t v_stop_boxed_508_; uint8_t v_res_509_; lean_object* v_r_510_; 
v_i_boxed_507_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_508_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_509_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_503_, v_as_504_, v_i_boxed_507_, v_stop_boxed_508_);
lean_dec_ref(v_as_504_);
lean_dec(v_mod_503_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_511_, lean_object* v_self_512_){
_start:
{
lean_object* v_packages_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_packages_513_ = lean_ctor_get(v_self_512_, 5);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_array_get_size(v_packages_513_);
v___x_516_ = lean_nat_dec_lt(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
return v___x_516_;
}
else
{
if (v___x_516_ == 0)
{
return v___x_516_;
}
else
{
size_t v___x_517_; size_t v___x_518_; uint8_t v___x_519_; 
v___x_517_ = ((size_t)0ULL);
v___x_518_ = lean_usize_of_nat(v___x_515_);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_511_, v_packages_513_, v___x_517_, v___x_518_);
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_520_, lean_object* v_self_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Lake_Workspace_isBuildableModule(v_mod_520_, v_self_521_);
lean_dec_ref(v_self_521_);
lean_dec(v_mod_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_527_, lean_object* v_as_528_, size_t v_sz_529_, size_t v_i_530_, lean_object* v_b_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = lean_usize_dec_lt(v_i_530_, v_sz_529_);
if (v___x_532_ == 0)
{
lean_dec(v_mod_527_);
lean_inc_ref(v_b_531_);
return v_b_531_;
}
else
{
lean_object* v___x_533_; lean_object* v_a_534_; lean_object* v___x_535_; 
v___x_533_ = lean_box(0);
v_a_534_ = lean_array_uget_borrowed(v_as_528_, v_i_530_);
lean_inc(v_a_534_);
lean_inc(v_mod_527_);
v___x_535_ = l_Lake_Package_findModule_x3f(v_mod_527_, v_a_534_);
if (lean_obj_tag(v___x_535_) == 1)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_mod_527_);
v___x_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_533_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; size_t v___x_539_; size_t v___x_540_; 
lean_dec(v___x_535_);
v___x_538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_add(v_i_530_, v___x_539_);
v_i_530_ = v___x_540_;
v_b_531_ = v___x_538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_542_, lean_object* v_as_543_, lean_object* v_sz_544_, lean_object* v_i_545_, lean_object* v_b_546_){
_start:
{
size_t v_sz_boxed_547_; size_t v_i_boxed_548_; lean_object* v_res_549_; 
v_sz_boxed_547_ = lean_unbox_usize(v_sz_544_);
lean_dec(v_sz_544_);
v_i_boxed_548_ = lean_unbox_usize(v_i_545_);
lean_dec(v_i_545_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_542_, v_as_543_, v_sz_boxed_547_, v_i_boxed_548_, v_b_546_);
lean_dec_ref(v_b_546_);
lean_dec_ref(v_as_543_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_550_, lean_object* v_self_551_){
_start:
{
lean_object* v_packages_552_; lean_object* v___x_553_; lean_object* v___x_554_; size_t v_sz_555_; size_t v___x_556_; lean_object* v___x_557_; lean_object* v_fst_558_; 
v_packages_552_ = lean_ctor_get(v_self_551_, 5);
v___x_553_ = lean_box(0);
v___x_554_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_555_ = lean_array_size(v_packages_552_);
v___x_556_ = ((size_t)0ULL);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_550_, v_packages_552_, v_sz_555_, v___x_556_, v___x_554_);
v_fst_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_fst_558_);
lean_dec_ref(v___x_557_);
if (lean_obj_tag(v_fst_558_) == 0)
{
return v___x_553_;
}
else
{
lean_object* v_val_559_; 
v_val_559_ = lean_ctor_get(v_fst_558_, 0);
lean_inc(v_val_559_);
lean_dec_ref(v_fst_558_);
return v_val_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_560_, lean_object* v_self_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lake_Workspace_findModule_x3f(v_mod_560_, v_self_561_);
lean_dec_ref(v_self_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_563_, lean_object* v_as_564_, size_t v_i_565_, size_t v_stop_566_, lean_object* v_b_567_){
_start:
{
lean_object* v___y_569_; uint8_t v___x_573_; 
v___x_573_ = lean_usize_dec_eq(v_i_565_, v_stop_566_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_array_uget_borrowed(v_as_564_, v_i_565_);
lean_inc(v___x_574_);
lean_inc(v_mod_563_);
v___x_575_ = l_Lake_Package_findModule_x3f(v_mod_563_, v___x_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
v___y_569_ = v_b_567_;
goto v___jp_568_;
}
else
{
lean_object* v_val_576_; lean_object* v___x_577_; 
v_val_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_val_576_);
lean_dec_ref(v___x_575_);
v___x_577_ = lean_array_push(v_b_567_, v_val_576_);
v___y_569_ = v___x_577_;
goto v___jp_568_;
}
}
else
{
lean_dec(v_mod_563_);
return v_b_567_;
}
v___jp_568_:
{
size_t v___x_570_; size_t v___x_571_; 
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_add(v_i_565_, v___x_570_);
v_i_565_ = v___x_571_;
v_b_567_ = v___y_569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_578_, lean_object* v_as_579_, lean_object* v_i_580_, lean_object* v_stop_581_, lean_object* v_b_582_){
_start:
{
size_t v_i_boxed_583_; size_t v_stop_boxed_584_; lean_object* v_res_585_; 
v_i_boxed_583_ = lean_unbox_usize(v_i_580_);
lean_dec(v_i_580_);
v_stop_boxed_584_ = lean_unbox_usize(v_stop_581_);
lean_dec(v_stop_581_);
v_res_585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_578_, v_as_579_, v_i_boxed_583_, v_stop_boxed_584_, v_b_582_);
lean_dec_ref(v_as_579_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_588_, lean_object* v_as_589_, lean_object* v_start_590_, lean_object* v_stop_591_){
_start:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_593_ = lean_nat_dec_lt(v_start_590_, v_stop_591_);
if (v___x_593_ == 0)
{
lean_dec(v_mod_588_);
return v___x_592_;
}
else
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_array_get_size(v_as_589_);
v___x_595_ = lean_nat_dec_le(v_stop_591_, v___x_594_);
if (v___x_595_ == 0)
{
uint8_t v___x_596_; 
v___x_596_ = lean_nat_dec_lt(v_start_590_, v___x_594_);
if (v___x_596_ == 0)
{
lean_dec(v_mod_588_);
return v___x_592_;
}
else
{
size_t v___x_597_; size_t v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_usize_of_nat(v_start_590_);
v___x_598_ = lean_usize_of_nat(v___x_594_);
v___x_599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_588_, v_as_589_, v___x_597_, v___x_598_, v___x_592_);
return v___x_599_;
}
}
else
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_usize_of_nat(v_start_590_);
v___x_601_ = lean_usize_of_nat(v_stop_591_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_588_, v_as_589_, v___x_600_, v___x_601_, v___x_592_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_603_, lean_object* v_as_604_, lean_object* v_start_605_, lean_object* v_stop_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_603_, v_as_604_, v_start_605_, v_stop_606_);
lean_dec(v_stop_606_);
lean_dec(v_start_605_);
lean_dec_ref(v_as_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_608_, lean_object* v_self_609_){
_start:
{
lean_object* v_packages_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_packages_610_ = lean_ctor_get(v_self_609_, 5);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_array_get_size(v_packages_610_);
v___x_613_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_608_, v_packages_610_, v___x_611_, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_614_, lean_object* v_self_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lake_Workspace_findModules(v_mod_614_, v_self_615_);
lean_dec_ref(v_self_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_617_, lean_object* v_as_618_, size_t v_sz_619_, size_t v_i_620_, lean_object* v_b_621_){
_start:
{
uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_lt(v_i_620_, v_sz_619_);
if (v___x_622_ == 0)
{
lean_dec(v_mod_617_);
lean_inc_ref(v_b_621_);
return v_b_621_;
}
else
{
lean_object* v___x_623_; lean_object* v_a_624_; lean_object* v___x_625_; 
v___x_623_ = lean_box(0);
v_a_624_ = lean_array_uget_borrowed(v_as_618_, v_i_620_);
lean_inc(v_a_624_);
lean_inc(v_mod_617_);
v___x_625_ = l_Lake_Package_findTargetModule_x3f(v_mod_617_, v_a_624_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v_mod_617_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_623_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; 
lean_dec(v___x_625_);
v___x_628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_620_, v___x_629_);
v_i_620_ = v___x_630_;
v_b_621_ = v___x_628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_632_, lean_object* v_as_633_, lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_b_636_){
_start:
{
size_t v_sz_boxed_637_; size_t v_i_boxed_638_; lean_object* v_res_639_; 
v_sz_boxed_637_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_638_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_632_, v_as_633_, v_sz_boxed_637_, v_i_boxed_638_, v_b_636_);
lean_dec_ref(v_b_636_);
lean_dec_ref(v_as_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_640_, lean_object* v_self_641_){
_start:
{
lean_object* v_packages_642_; lean_object* v___x_643_; lean_object* v___x_644_; size_t v_sz_645_; size_t v___x_646_; lean_object* v___x_647_; lean_object* v_fst_648_; 
v_packages_642_ = lean_ctor_get(v_self_641_, 5);
v___x_643_ = lean_box(0);
v___x_644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_645_ = lean_array_size(v_packages_642_);
v___x_646_ = ((size_t)0ULL);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_640_, v_packages_642_, v_sz_645_, v___x_646_, v___x_644_);
v_fst_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_fst_648_);
lean_dec_ref(v___x_647_);
if (lean_obj_tag(v_fst_648_) == 0)
{
return v___x_643_;
}
else
{
lean_object* v_val_649_; 
v_val_649_ = lean_ctor_get(v_fst_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref(v_fst_648_);
return v_val_649_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_650_, lean_object* v_self_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_650_, v_self_651_);
lean_dec_ref(v_self_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_653_, lean_object* v_as_654_, size_t v_sz_655_, size_t v_i_656_, lean_object* v_b_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = lean_usize_dec_lt(v_i_656_, v_sz_655_);
if (v___x_658_ == 0)
{
lean_dec_ref(v_path_653_);
lean_inc_ref(v_b_657_);
return v_b_657_;
}
else
{
lean_object* v___x_659_; lean_object* v_a_660_; lean_object* v___x_661_; 
v___x_659_ = lean_box(0);
v_a_660_ = lean_array_uget_borrowed(v_as_654_, v_i_656_);
lean_inc(v_a_660_);
lean_inc_ref(v_path_653_);
v___x_661_ = l_Lake_Package_findModuleBySrc_x3f(v_path_653_, v_a_660_);
if (lean_obj_tag(v___x_661_) == 1)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec_ref(v_path_653_);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___x_659_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; size_t v___x_665_; size_t v___x_666_; 
lean_dec(v___x_661_);
v___x_664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_656_, v___x_665_);
v_i_656_ = v___x_666_;
v_b_657_ = v___x_664_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_668_, lean_object* v_as_669_, lean_object* v_sz_670_, lean_object* v_i_671_, lean_object* v_b_672_){
_start:
{
size_t v_sz_boxed_673_; size_t v_i_boxed_674_; lean_object* v_res_675_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_670_);
lean_dec(v_sz_670_);
v_i_boxed_674_ = lean_unbox_usize(v_i_671_);
lean_dec(v_i_671_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_668_, v_as_669_, v_sz_boxed_673_, v_i_boxed_674_, v_b_672_);
lean_dec_ref(v_b_672_);
lean_dec_ref(v_as_669_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_676_, lean_object* v_self_677_){
_start:
{
lean_object* v_packages_678_; lean_object* v___x_679_; lean_object* v___x_680_; size_t v_sz_681_; size_t v___x_682_; lean_object* v___x_683_; lean_object* v_fst_684_; 
v_packages_678_ = lean_ctor_get(v_self_677_, 5);
v___x_679_ = lean_box(0);
v___x_680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_681_ = lean_array_size(v_packages_678_);
v___x_682_ = ((size_t)0ULL);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_676_, v_packages_678_, v_sz_681_, v___x_682_, v___x_680_);
v_fst_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_fst_684_);
lean_dec_ref(v___x_683_);
if (lean_obj_tag(v_fst_684_) == 0)
{
return v___x_679_;
}
else
{
lean_object* v_val_685_; 
v_val_685_ = lean_ctor_get(v_fst_684_, 0);
lean_inc(v_val_685_);
lean_dec_ref(v_fst_684_);
return v_val_685_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_686_, lean_object* v_self_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_686_, v_self_687_);
lean_dec_ref(v_self_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_692_, lean_object* v_as_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_b_696_){
_start:
{
lean_object* v_a_698_; uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_702_ == 0)
{
lean_inc_ref(v_b_696_);
return v_b_696_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_a_705_; lean_object* v___x_706_; 
v___x_703_ = lean_box(0);
v___x_704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_705_ = lean_array_uget_borrowed(v_as_693_, v_i_695_);
v___x_706_ = l_Lake_Package_findTargetDecl_x3f(v_name_692_, v_a_705_);
if (lean_obj_tag(v___x_706_) == 0)
{
v_a_698_ = v___x_704_;
goto v___jp_697_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_722_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_722_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_722_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_722_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_name_711_; lean_object* v_kind_712_; lean_object* v_config_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_name_711_ = lean_ctor_get(v_val_707_, 1);
lean_inc(v_name_711_);
v_kind_712_ = lean_ctor_get(v_val_707_, 2);
lean_inc(v_kind_712_);
v_config_713_ = lean_ctor_get(v_val_707_, 3);
lean_inc(v_config_713_);
lean_dec(v_val_707_);
v___x_714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_715_ = lean_name_eq(v_kind_712_, v___x_714_);
lean_dec(v_kind_712_);
if (v___x_715_ == 0)
{
lean_dec(v_config_713_);
lean_dec(v_name_711_);
lean_del_object(v___x_709_);
v_a_698_ = v___x_704_;
goto v___jp_697_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_718_; 
lean_inc(v_a_705_);
v___x_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_716_, 0, v_a_705_);
lean_ctor_set(v___x_716_, 1, v_name_711_);
lean_ctor_set(v___x_716_, 2, v_config_713_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_716_);
v___x_718_ = v___x_709_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_721_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_703_);
return v___x_720_;
}
}
}
}
}
v___jp_697_:
{
size_t v___x_699_; size_t v___x_700_; 
v___x_699_ = ((size_t)1ULL);
v___x_700_ = lean_usize_add(v_i_695_, v___x_699_);
v_i_695_ = v___x_700_;
v_b_696_ = v_a_698_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_723_, lean_object* v_as_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_b_727_){
_start:
{
size_t v_sz_boxed_728_; size_t v_i_boxed_729_; lean_object* v_res_730_; 
v_sz_boxed_728_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_729_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_723_, v_as_724_, v_sz_boxed_728_, v_i_boxed_729_, v_b_727_);
lean_dec_ref(v_b_727_);
lean_dec_ref(v_as_724_);
lean_dec(v_name_723_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_731_, lean_object* v_self_732_){
_start:
{
lean_object* v_packages_733_; lean_object* v___x_734_; lean_object* v___x_735_; size_t v_sz_736_; size_t v___x_737_; lean_object* v___x_738_; lean_object* v_fst_739_; 
v_packages_733_ = lean_ctor_get(v_self_732_, 5);
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_736_ = lean_array_size(v_packages_733_);
v___x_737_ = ((size_t)0ULL);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_731_, v_packages_733_, v_sz_736_, v___x_737_, v___x_735_);
v_fst_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_fst_739_);
lean_dec_ref(v___x_738_);
if (lean_obj_tag(v_fst_739_) == 0)
{
return v___x_734_;
}
else
{
lean_object* v_val_740_; 
v_val_740_ = lean_ctor_get(v_fst_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref(v_fst_739_);
return v_val_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_741_, lean_object* v_self_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lake_Workspace_findLeanLib_x3f(v_name_741_, v_self_742_);
lean_dec_ref(v_self_742_);
lean_dec(v_name_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_744_, lean_object* v_as_745_, size_t v_sz_746_, size_t v_i_747_, lean_object* v_b_748_){
_start:
{
lean_object* v_a_750_; uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_747_, v_sz_746_);
if (v___x_754_ == 0)
{
lean_inc_ref(v_b_748_);
return v_b_748_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_758_; 
v___x_755_ = lean_box(0);
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_757_ = lean_array_uget_borrowed(v_as_745_, v_i_747_);
v___x_758_ = l_Lake_Package_findTargetDecl_x3f(v_name_744_, v_a_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
v_a_750_ = v___x_756_;
goto v___jp_749_;
}
else
{
lean_object* v_val_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_774_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_774_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_774_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_val_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_774_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_name_763_; lean_object* v_kind_764_; lean_object* v_config_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_name_763_ = lean_ctor_get(v_val_759_, 1);
lean_inc(v_name_763_);
v_kind_764_ = lean_ctor_get(v_val_759_, 2);
lean_inc(v_kind_764_);
v_config_765_ = lean_ctor_get(v_val_759_, 3);
lean_inc(v_config_765_);
lean_dec(v_val_759_);
v___x_766_ = l_Lake_LeanExe_keyword;
v___x_767_ = lean_name_eq(v_kind_764_, v___x_766_);
lean_dec(v_kind_764_);
if (v___x_767_ == 0)
{
lean_dec(v_config_765_);
lean_dec(v_name_763_);
lean_del_object(v___x_761_);
v_a_750_ = v___x_756_;
goto v___jp_749_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_770_; 
lean_inc(v_a_757_);
v___x_768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_768_, 0, v_a_757_);
lean_ctor_set(v___x_768_, 1, v_name_763_);
lean_ctor_set(v___x_768_, 2, v_config_765_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_768_);
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_773_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___x_755_);
return v___x_772_;
}
}
}
}
}
v___jp_749_:
{
size_t v___x_751_; size_t v___x_752_; 
v___x_751_ = ((size_t)1ULL);
v___x_752_ = lean_usize_add(v_i_747_, v___x_751_);
v_i_747_ = v___x_752_;
v_b_748_ = v_a_750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_775_, lean_object* v_as_776_, lean_object* v_sz_777_, lean_object* v_i_778_, lean_object* v_b_779_){
_start:
{
size_t v_sz_boxed_780_; size_t v_i_boxed_781_; lean_object* v_res_782_; 
v_sz_boxed_780_ = lean_unbox_usize(v_sz_777_);
lean_dec(v_sz_777_);
v_i_boxed_781_ = lean_unbox_usize(v_i_778_);
lean_dec(v_i_778_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_775_, v_as_776_, v_sz_boxed_780_, v_i_boxed_781_, v_b_779_);
lean_dec_ref(v_b_779_);
lean_dec_ref(v_as_776_);
lean_dec(v_name_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_783_, lean_object* v_self_784_){
_start:
{
lean_object* v_packages_785_; lean_object* v___x_786_; lean_object* v___x_787_; size_t v_sz_788_; size_t v___x_789_; lean_object* v___x_790_; lean_object* v_fst_791_; 
v_packages_785_ = lean_ctor_get(v_self_784_, 5);
v___x_786_ = lean_box(0);
v___x_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_788_ = lean_array_size(v_packages_785_);
v___x_789_ = ((size_t)0ULL);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_783_, v_packages_785_, v_sz_788_, v___x_789_, v___x_787_);
v_fst_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_fst_791_);
lean_dec_ref(v___x_790_);
if (lean_obj_tag(v_fst_791_) == 0)
{
return v___x_786_;
}
else
{
lean_object* v_val_792_; 
v_val_792_ = lean_ctor_get(v_fst_791_, 0);
lean_inc(v_val_792_);
lean_dec_ref(v_fst_791_);
return v_val_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_793_, lean_object* v_self_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lake_Workspace_findLeanExe_x3f(v_name_793_, v_self_794_);
lean_dec_ref(v_self_794_);
lean_dec(v_name_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_796_, lean_object* v_as_797_, size_t v_sz_798_, size_t v_i_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_a_802_; uint8_t v___x_806_; 
v___x_806_ = lean_usize_dec_lt(v_i_799_, v_sz_798_);
if (v___x_806_ == 0)
{
lean_inc_ref(v_b_800_);
return v_b_800_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_a_809_; lean_object* v___x_810_; 
v___x_807_ = lean_box(0);
v___x_808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_809_ = lean_array_uget_borrowed(v_as_797_, v_i_799_);
v___x_810_ = l_Lake_Package_findTargetDecl_x3f(v_name_796_, v_a_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
v_a_802_ = v___x_808_;
goto v___jp_801_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_826_; 
v_val_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_826_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_826_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_826_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_name_815_; lean_object* v_kind_816_; lean_object* v_config_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_name_815_ = lean_ctor_get(v_val_811_, 1);
lean_inc(v_name_815_);
v_kind_816_ = lean_ctor_get(v_val_811_, 2);
lean_inc(v_kind_816_);
v_config_817_ = lean_ctor_get(v_val_811_, 3);
lean_inc(v_config_817_);
lean_dec(v_val_811_);
v___x_818_ = l_Lake_ExternLib_keyword;
v___x_819_ = lean_name_eq(v_kind_816_, v___x_818_);
lean_dec(v_kind_816_);
if (v___x_819_ == 0)
{
lean_dec(v_config_817_);
lean_dec(v_name_815_);
lean_del_object(v___x_813_);
v_a_802_ = v___x_808_;
goto v___jp_801_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_822_; 
lean_inc(v_a_809_);
v___x_820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_820_, 0, v_a_809_);
lean_ctor_set(v___x_820_, 1, v_name_815_);
lean_ctor_set(v___x_820_, 2, v_config_817_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_820_);
v___x_822_ = v___x_813_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_825_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_807_);
return v___x_824_;
}
}
}
}
}
v___jp_801_:
{
size_t v___x_803_; size_t v___x_804_; 
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_add(v_i_799_, v___x_803_);
v_i_799_ = v___x_804_;
v_b_800_ = v_a_802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_827_, lean_object* v_as_828_, lean_object* v_sz_829_, lean_object* v_i_830_, lean_object* v_b_831_){
_start:
{
size_t v_sz_boxed_832_; size_t v_i_boxed_833_; lean_object* v_res_834_; 
v_sz_boxed_832_ = lean_unbox_usize(v_sz_829_);
lean_dec(v_sz_829_);
v_i_boxed_833_ = lean_unbox_usize(v_i_830_);
lean_dec(v_i_830_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_827_, v_as_828_, v_sz_boxed_832_, v_i_boxed_833_, v_b_831_);
lean_dec_ref(v_b_831_);
lean_dec_ref(v_as_828_);
lean_dec(v_name_827_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_835_, lean_object* v_self_836_){
_start:
{
lean_object* v_packages_837_; lean_object* v___x_838_; lean_object* v___x_839_; size_t v_sz_840_; size_t v___x_841_; lean_object* v___x_842_; lean_object* v_fst_843_; 
v_packages_837_ = lean_ctor_get(v_self_836_, 5);
v___x_838_ = lean_box(0);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_840_ = lean_array_size(v_packages_837_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_835_, v_packages_837_, v_sz_840_, v___x_841_, v___x_839_);
v_fst_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_fst_843_);
lean_dec_ref(v___x_842_);
if (lean_obj_tag(v_fst_843_) == 0)
{
return v___x_838_;
}
else
{
lean_object* v_val_844_; 
v_val_844_ = lean_ctor_get(v_fst_843_, 0);
lean_inc(v_val_844_);
lean_dec_ref(v_fst_843_);
return v_val_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_845_, lean_object* v_self_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lake_Workspace_findExternLib_x3f(v_name_845_, v_self_846_);
lean_dec_ref(v_self_846_);
lean_dec(v_name_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_848_, lean_object* v_f_849_){
_start:
{
if (lean_obj_tag(v_a_848_) == 0)
{
lean_object* v___x_850_; 
lean_dec(v_f_849_);
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_val_851_ = lean_ctor_get(v_a_848_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v_a_848_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v_a_848_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v_a_848_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_apply_1(v_f_849_, v_val_851_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_860_, lean_object* v_00_u03b2_861_, lean_object* v_a_862_, lean_object* v_f_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_862_, v_f_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v_a_865_);
lean_ctor_set(v___x_867_, 1, v_x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_871_, lean_object* v_as_872_, size_t v_sz_873_, size_t v_i_874_, lean_object* v_b_875_){
_start:
{
uint8_t v___x_876_; 
v___x_876_ = lean_usize_dec_lt(v_i_874_, v_sz_873_);
if (v___x_876_ == 0)
{
lean_inc_ref(v_b_875_);
return v_b_875_;
}
else
{
lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_877_ = lean_box(0);
v_a_878_ = lean_array_uget_borrowed(v_as_872_, v_i_874_);
lean_inc(v_a_878_);
v___f_879_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_879_, 0, v_a_878_);
v___x_880_ = l_Lake_Package_findTargetConfig_x3f(v_name_871_, v_a_878_);
v___x_881_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_880_, v___f_879_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_877_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; size_t v___x_885_; size_t v___x_886_; 
lean_dec(v___x_881_);
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_add(v_i_874_, v___x_885_);
v_i_874_ = v___x_886_;
v_b_875_ = v___x_884_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_888_, lean_object* v_as_889_, lean_object* v_sz_890_, lean_object* v_i_891_, lean_object* v_b_892_){
_start:
{
size_t v_sz_boxed_893_; size_t v_i_boxed_894_; lean_object* v_res_895_; 
v_sz_boxed_893_ = lean_unbox_usize(v_sz_890_);
lean_dec(v_sz_890_);
v_i_boxed_894_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_res_895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_888_, v_as_889_, v_sz_boxed_893_, v_i_boxed_894_, v_b_892_);
lean_dec_ref(v_b_892_);
lean_dec_ref(v_as_889_);
lean_dec(v_name_888_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_896_, lean_object* v_self_897_){
_start:
{
lean_object* v_packages_898_; lean_object* v___x_899_; lean_object* v___x_900_; size_t v_sz_901_; size_t v___x_902_; lean_object* v___x_903_; lean_object* v_fst_904_; 
v_packages_898_ = lean_ctor_get(v_self_897_, 5);
v___x_899_ = lean_box(0);
v___x_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_901_ = lean_array_size(v_packages_898_);
v___x_902_ = ((size_t)0ULL);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_896_, v_packages_898_, v_sz_901_, v___x_902_, v___x_900_);
v_fst_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_fst_904_);
lean_dec_ref(v___x_903_);
if (lean_obj_tag(v_fst_904_) == 0)
{
return v___x_899_;
}
else
{
lean_object* v_val_905_; 
v_val_905_ = lean_ctor_get(v_fst_904_, 0);
lean_inc(v_val_905_);
lean_dec_ref(v_fst_904_);
return v_val_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_906_, lean_object* v_self_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_906_, v_self_907_);
lean_dec_ref(v_self_907_);
lean_dec(v_name_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_909_, lean_object* v_x_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_a_909_);
lean_ctor_set(v___x_911_, 1, v_x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_912_, lean_object* v_as_913_, size_t v_sz_914_, size_t v_i_915_, lean_object* v_b_916_){
_start:
{
uint8_t v___x_917_; 
v___x_917_ = lean_usize_dec_lt(v_i_915_, v_sz_914_);
if (v___x_917_ == 0)
{
lean_inc_ref(v_b_916_);
return v_b_916_;
}
else
{
lean_object* v___x_918_; lean_object* v_a_919_; lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_918_ = lean_box(0);
v_a_919_ = lean_array_uget_borrowed(v_as_913_, v_i_915_);
lean_inc(v_a_919_);
v___f_920_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_920_, 0, v_a_919_);
v___x_921_ = l_Lake_Package_findTargetDecl_x3f(v_name_912_, v_a_919_);
v___x_922_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_921_, v___f_920_);
if (lean_obj_tag(v___x_922_) == 1)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_918_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; size_t v___x_926_; size_t v___x_927_; 
lean_dec(v___x_922_);
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_915_, v___x_926_);
v_i_915_ = v___x_927_;
v_b_916_ = v___x_925_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_929_, lean_object* v_as_930_, lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_b_933_){
_start:
{
size_t v_sz_boxed_934_; size_t v_i_boxed_935_; lean_object* v_res_936_; 
v_sz_boxed_934_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_935_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_929_, v_as_930_, v_sz_boxed_934_, v_i_boxed_935_, v_b_933_);
lean_dec_ref(v_b_933_);
lean_dec_ref(v_as_930_);
lean_dec(v_name_929_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_937_, lean_object* v_self_938_){
_start:
{
lean_object* v_packages_939_; lean_object* v___x_940_; lean_object* v___x_941_; size_t v_sz_942_; size_t v___x_943_; lean_object* v___x_944_; lean_object* v_fst_945_; 
v_packages_939_ = lean_ctor_get(v_self_938_, 5);
v___x_940_ = lean_box(0);
v___x_941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_942_ = lean_array_size(v_packages_939_);
v___x_943_ = ((size_t)0ULL);
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_937_, v_packages_939_, v_sz_942_, v___x_943_, v___x_941_);
v_fst_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_fst_945_);
lean_dec_ref(v___x_944_);
if (lean_obj_tag(v_fst_945_) == 0)
{
return v___x_940_;
}
else
{
lean_object* v_val_946_; 
v_val_946_ = lean_ctor_get(v_fst_945_, 0);
lean_inc(v_val_946_);
lean_dec_ref(v_fst_945_);
return v_val_946_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_947_, lean_object* v_self_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_947_, v_self_948_);
lean_dec_ref(v_self_948_);
lean_dec(v_name_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_950_, lean_object* v_cfg_951_, lean_object* v_self_952_){
_start:
{
lean_object* v_root_953_; lean_object* v_lakeEnv_954_; lean_object* v_lakeConfig_955_; lean_object* v_lakeCache_956_; lean_object* v_lakeArgs_x3f_957_; lean_object* v_packages_958_; lean_object* v_packageMap_959_; lean_object* v_facetConfigs_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_root_953_ = lean_ctor_get(v_self_952_, 0);
v_lakeEnv_954_ = lean_ctor_get(v_self_952_, 1);
v_lakeConfig_955_ = lean_ctor_get(v_self_952_, 2);
v_lakeCache_956_ = lean_ctor_get(v_self_952_, 3);
v_lakeArgs_x3f_957_ = lean_ctor_get(v_self_952_, 4);
v_packages_958_ = lean_ctor_get(v_self_952_, 5);
v_packageMap_959_ = lean_ctor_get(v_self_952_, 6);
v_facetConfigs_960_ = lean_ctor_get(v_self_952_, 7);
v_isSharedCheck_968_ = !lean_is_exclusive(v_self_952_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v_self_952_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_facetConfigs_960_);
lean_inc(v_packageMap_959_);
lean_inc(v_packages_958_);
lean_inc(v_lakeArgs_x3f_957_);
lean_inc(v_lakeCache_956_);
lean_inc(v_lakeConfig_955_);
lean_inc(v_lakeEnv_954_);
lean_inc(v_root_953_);
lean_dec(v_self_952_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = l_Lake_FacetConfigMap_insert(v_name_950_, v_cfg_951_, v_facetConfigs_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 7, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_root_953_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_lakeEnv_954_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_lakeConfig_955_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_lakeCache_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_lakeArgs_x3f_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 5, v_packages_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 6, v_packageMap_959_);
lean_ctor_set(v_reuseFailAlloc_967_, 7, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_969_, lean_object* v_self_970_){
_start:
{
lean_object* v_facetConfigs_971_; lean_object* v___x_972_; 
v_facetConfigs_971_ = lean_ctor_get(v_self_970_, 7);
v___x_972_ = l_Lake_FacetConfigMap_get_x3f(v_name_969_, v_facetConfigs_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_973_, lean_object* v_self_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_973_, v_self_974_);
lean_dec_ref(v_self_974_);
lean_dec(v_name_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_976_, lean_object* v_cfg_977_, lean_object* v_self_978_){
_start:
{
lean_object* v_root_979_; lean_object* v_lakeEnv_980_; lean_object* v_lakeConfig_981_; lean_object* v_lakeCache_982_; lean_object* v_lakeArgs_x3f_983_; lean_object* v_packages_984_; lean_object* v_packageMap_985_; lean_object* v_facetConfigs_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_root_979_ = lean_ctor_get(v_self_978_, 0);
v_lakeEnv_980_ = lean_ctor_get(v_self_978_, 1);
v_lakeConfig_981_ = lean_ctor_get(v_self_978_, 2);
v_lakeCache_982_ = lean_ctor_get(v_self_978_, 3);
v_lakeArgs_x3f_983_ = lean_ctor_get(v_self_978_, 4);
v_packages_984_ = lean_ctor_get(v_self_978_, 5);
v_packageMap_985_ = lean_ctor_get(v_self_978_, 6);
v_facetConfigs_986_ = lean_ctor_get(v_self_978_, 7);
v_isSharedCheck_994_ = !lean_is_exclusive(v_self_978_);
if (v_isSharedCheck_994_ == 0)
{
v___x_988_ = v_self_978_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_facetConfigs_986_);
lean_inc(v_packageMap_985_);
lean_inc(v_packages_984_);
lean_inc(v_lakeArgs_x3f_983_);
lean_inc(v_lakeCache_982_);
lean_inc(v_lakeConfig_981_);
lean_inc(v_lakeEnv_980_);
lean_inc(v_root_979_);
lean_dec(v_self_978_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = l_Lake_FacetConfigMap_insert(v_name_976_, v_cfg_977_, v_facetConfigs_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 7, v___x_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_root_979_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_lakeEnv_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_lakeConfig_981_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_lakeCache_982_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_lakeArgs_x3f_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 5, v_packages_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 6, v_packageMap_985_);
lean_ctor_set(v_reuseFailAlloc_993_, 7, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_995_, lean_object* v_self_996_){
_start:
{
lean_object* v_facetConfigs_997_; lean_object* v___x_998_; 
v_facetConfigs_997_ = lean_ctor_get(v_self_996_, 7);
v___x_998_ = l_Lake_FacetConfigMap_get_x3f(v_name_995_, v_facetConfigs_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(0);
return v___x_999_;
}
else
{
lean_object* v_val_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_val_1000_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_val_1000_);
lean_dec_ref(v___x_998_);
v___x_1001_ = l_Lake_Module_keyword;
v___x_1002_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1001_, v_val_1000_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1003_, lean_object* v_self_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1003_, v_self_1004_);
lean_dec_ref(v_self_1004_);
lean_dec(v_name_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1006_, lean_object* v_cfg_1007_, lean_object* v_self_1008_){
_start:
{
lean_object* v_root_1009_; lean_object* v_lakeEnv_1010_; lean_object* v_lakeConfig_1011_; lean_object* v_lakeCache_1012_; lean_object* v_lakeArgs_x3f_1013_; lean_object* v_packages_1014_; lean_object* v_packageMap_1015_; lean_object* v_facetConfigs_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1024_; 
v_root_1009_ = lean_ctor_get(v_self_1008_, 0);
v_lakeEnv_1010_ = lean_ctor_get(v_self_1008_, 1);
v_lakeConfig_1011_ = lean_ctor_get(v_self_1008_, 2);
v_lakeCache_1012_ = lean_ctor_get(v_self_1008_, 3);
v_lakeArgs_x3f_1013_ = lean_ctor_get(v_self_1008_, 4);
v_packages_1014_ = lean_ctor_get(v_self_1008_, 5);
v_packageMap_1015_ = lean_ctor_get(v_self_1008_, 6);
v_facetConfigs_1016_ = lean_ctor_get(v_self_1008_, 7);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_self_1008_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1018_ = v_self_1008_;
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_facetConfigs_1016_);
lean_inc(v_packageMap_1015_);
lean_inc(v_packages_1014_);
lean_inc(v_lakeArgs_x3f_1013_);
lean_inc(v_lakeCache_1012_);
lean_inc(v_lakeConfig_1011_);
lean_inc(v_lakeEnv_1010_);
lean_inc(v_root_1009_);
lean_dec(v_self_1008_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1024_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1020_ = l_Lake_FacetConfigMap_insert(v_name_1006_, v_cfg_1007_, v_facetConfigs_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 7, v___x_1020_);
v___x_1022_ = v___x_1018_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_root_1009_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_lakeEnv_1010_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_lakeConfig_1011_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_lakeCache_1012_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_lakeArgs_x3f_1013_);
lean_ctor_set(v_reuseFailAlloc_1023_, 5, v_packages_1014_);
lean_ctor_set(v_reuseFailAlloc_1023_, 6, v_packageMap_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 7, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1025_, lean_object* v_self_1026_){
_start:
{
lean_object* v_facetConfigs_1027_; lean_object* v___x_1028_; 
v_facetConfigs_1027_ = lean_ctor_get(v_self_1026_, 7);
v___x_1028_ = l_Lake_FacetConfigMap_get_x3f(v_name_1025_, v_facetConfigs_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_box(0);
return v___x_1029_;
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_val_1030_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v___x_1028_);
v___x_1031_ = l_Lake_Package_keyword;
v___x_1032_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1031_, v_val_1030_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1033_, lean_object* v_self_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1033_, v_self_1034_);
lean_dec_ref(v_self_1034_);
lean_dec(v_name_1033_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1036_, lean_object* v_cfg_1037_, lean_object* v_self_1038_){
_start:
{
lean_object* v_root_1039_; lean_object* v_lakeEnv_1040_; lean_object* v_lakeConfig_1041_; lean_object* v_lakeCache_1042_; lean_object* v_lakeArgs_x3f_1043_; lean_object* v_packages_1044_; lean_object* v_packageMap_1045_; lean_object* v_facetConfigs_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v_root_1039_ = lean_ctor_get(v_self_1038_, 0);
v_lakeEnv_1040_ = lean_ctor_get(v_self_1038_, 1);
v_lakeConfig_1041_ = lean_ctor_get(v_self_1038_, 2);
v_lakeCache_1042_ = lean_ctor_get(v_self_1038_, 3);
v_lakeArgs_x3f_1043_ = lean_ctor_get(v_self_1038_, 4);
v_packages_1044_ = lean_ctor_get(v_self_1038_, 5);
v_packageMap_1045_ = lean_ctor_get(v_self_1038_, 6);
v_facetConfigs_1046_ = lean_ctor_get(v_self_1038_, 7);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_self_1038_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1048_ = v_self_1038_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_facetConfigs_1046_);
lean_inc(v_packageMap_1045_);
lean_inc(v_packages_1044_);
lean_inc(v_lakeArgs_x3f_1043_);
lean_inc(v_lakeCache_1042_);
lean_inc(v_lakeConfig_1041_);
lean_inc(v_lakeEnv_1040_);
lean_inc(v_root_1039_);
lean_dec(v_self_1038_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = l_Lake_FacetConfigMap_insert(v_name_1036_, v_cfg_1037_, v_facetConfigs_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 7, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_root_1039_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_lakeEnv_1040_);
lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_lakeConfig_1041_);
lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_lakeCache_1042_);
lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_lakeArgs_x3f_1043_);
lean_ctor_set(v_reuseFailAlloc_1053_, 5, v_packages_1044_);
lean_ctor_set(v_reuseFailAlloc_1053_, 6, v_packageMap_1045_);
lean_ctor_set(v_reuseFailAlloc_1053_, 7, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1055_, lean_object* v_self_1056_){
_start:
{
lean_object* v_facetConfigs_1057_; lean_object* v___x_1058_; 
v_facetConfigs_1057_ = lean_ctor_get(v_self_1056_, 7);
v___x_1058_ = l_Lake_FacetConfigMap_get_x3f(v_name_1055_, v_facetConfigs_1057_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_box(0);
return v___x_1059_;
}
else
{
lean_object* v_val_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_val_1060_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_val_1060_);
lean_dec_ref(v___x_1058_);
v___x_1061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1062_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1061_, v_val_1060_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1063_, lean_object* v_self_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1063_, v_self_1064_);
lean_dec_ref(v_self_1064_);
lean_dec(v_name_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1066_, size_t v_i_1067_, size_t v_stop_1068_, lean_object* v_b_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_eq(v_i_1067_, v_stop_1068_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; lean_object* v_config_1072_; lean_object* v_dir_1073_; lean_object* v_buildDir_1074_; lean_object* v_binDir_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; 
v___x_1071_ = lean_array_uget_borrowed(v_as_1066_, v_i_1067_);
v_config_1072_ = lean_ctor_get(v___x_1071_, 6);
v_dir_1073_ = lean_ctor_get(v___x_1071_, 4);
v_buildDir_1074_ = lean_ctor_get(v_config_1072_, 5);
v_binDir_1075_ = lean_ctor_get(v_config_1072_, 8);
lean_inc_ref(v_buildDir_1074_);
v___x_1076_ = l_System_FilePath_normalize(v_buildDir_1074_);
lean_inc_ref(v_dir_1073_);
v___x_1077_ = l_Lake_joinRelative(v_dir_1073_, v___x_1076_);
lean_inc_ref(v_binDir_1075_);
v___x_1078_ = l_System_FilePath_normalize(v_binDir_1075_);
v___x_1079_ = l_Lake_joinRelative(v___x_1077_, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v_b_1069_);
v___x_1081_ = ((size_t)1ULL);
v___x_1082_ = lean_usize_add(v_i_1067_, v___x_1081_);
v_i_1067_ = v___x_1082_;
v_b_1069_ = v___x_1080_;
goto _start;
}
else
{
return v_b_1069_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1084_, lean_object* v_i_1085_, lean_object* v_stop_1086_, lean_object* v_b_1087_){
_start:
{
size_t v_i_boxed_1088_; size_t v_stop_boxed_1089_; lean_object* v_res_1090_; 
v_i_boxed_1088_ = lean_unbox_usize(v_i_1085_);
lean_dec(v_i_1085_);
v_stop_boxed_1089_ = lean_unbox_usize(v_stop_1086_);
lean_dec(v_stop_1086_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1084_, v_i_boxed_1088_, v_stop_boxed_1089_, v_b_1087_);
lean_dec_ref(v_as_1084_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1091_){
_start:
{
lean_object* v_packages_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_packages_1092_ = lean_ctor_get(v_self_1091_, 5);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_array_get_size(v_packages_1092_);
v___x_1096_ = lean_nat_dec_lt(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
return v___x_1093_;
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_le(v___x_1095_, v___x_1095_);
if (v___x_1097_ == 0)
{
if (v___x_1096_ == 0)
{
return v___x_1093_;
}
else
{
size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = lean_usize_of_nat(v___x_1095_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1092_, v___x_1098_, v___x_1099_, v___x_1093_);
return v___x_1100_;
}
}
else
{
size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = lean_usize_of_nat(v___x_1095_);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1092_, v___x_1101_, v___x_1102_, v___x_1093_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lake_Workspace_binPath(v_self_1104_);
lean_dec_ref(v_self_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1106_, size_t v_i_1107_, size_t v_stop_1108_, lean_object* v_b_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_eq(v_i_1107_, v_stop_1108_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; lean_object* v_config_1112_; lean_object* v_dir_1113_; lean_object* v_buildDir_1114_; lean_object* v_leanLibDir_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; 
v___x_1111_ = lean_array_uget_borrowed(v_as_1106_, v_i_1107_);
v_config_1112_ = lean_ctor_get(v___x_1111_, 6);
v_dir_1113_ = lean_ctor_get(v___x_1111_, 4);
v_buildDir_1114_ = lean_ctor_get(v_config_1112_, 5);
v_leanLibDir_1115_ = lean_ctor_get(v_config_1112_, 6);
lean_inc_ref(v_buildDir_1114_);
v___x_1116_ = l_System_FilePath_normalize(v_buildDir_1114_);
lean_inc_ref(v_dir_1113_);
v___x_1117_ = l_Lake_joinRelative(v_dir_1113_, v___x_1116_);
lean_inc_ref(v_leanLibDir_1115_);
v___x_1118_ = l_System_FilePath_normalize(v_leanLibDir_1115_);
v___x_1119_ = l_Lake_joinRelative(v___x_1117_, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_b_1109_);
v___x_1121_ = ((size_t)1ULL);
v___x_1122_ = lean_usize_add(v_i_1107_, v___x_1121_);
v_i_1107_ = v___x_1122_;
v_b_1109_ = v___x_1120_;
goto _start;
}
else
{
return v_b_1109_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1124_, lean_object* v_i_1125_, lean_object* v_stop_1126_, lean_object* v_b_1127_){
_start:
{
size_t v_i_boxed_1128_; size_t v_stop_boxed_1129_; lean_object* v_res_1130_; 
v_i_boxed_1128_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_stop_boxed_1129_ = lean_unbox_usize(v_stop_1126_);
lean_dec(v_stop_1126_);
v_res_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1124_, v_i_boxed_1128_, v_stop_boxed_1129_, v_b_1127_);
lean_dec_ref(v_as_1124_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1131_){
_start:
{
lean_object* v_packages_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_packages_1132_ = lean_ctor_get(v_self_1131_, 5);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = lean_array_get_size(v_packages_1132_);
v___x_1136_ = lean_nat_dec_lt(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
return v___x_1133_;
}
else
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_nat_dec_le(v___x_1135_, v___x_1135_);
if (v___x_1137_ == 0)
{
if (v___x_1136_ == 0)
{
return v___x_1133_;
}
else
{
size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = lean_usize_of_nat(v___x_1135_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1132_, v___x_1138_, v___x_1139_, v___x_1133_);
return v___x_1140_;
}
}
else
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1135_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1132_, v___x_1141_, v___x_1142_, v___x_1133_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* v_self_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lake_Workspace_leanPath(v_self_1144_);
lean_dec_ref(v_self_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1146_, lean_object* v_as_1147_, size_t v_i_1148_, size_t v_stop_1149_, lean_object* v_b_1150_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_usize_dec_eq(v_i_1148_, v_stop_1149_);
if (v___x_1151_ == 0)
{
size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; lean_object* v_kind_1155_; lean_object* v_config_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1152_ = ((size_t)1ULL);
v___x_1153_ = lean_usize_sub(v_i_1148_, v___x_1152_);
v___x_1154_ = lean_array_uget_borrowed(v_as_1147_, v___x_1153_);
v_kind_1155_ = lean_ctor_get(v___x_1154_, 2);
v_config_1156_ = lean_ctor_get(v___x_1154_, 3);
v___x_1157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1158_ = lean_name_eq(v_kind_1155_, v___x_1157_);
if (v___x_1158_ == 0)
{
v_i_1148_ = v___x_1153_;
goto _start;
}
else
{
lean_object* v_config_1160_; lean_object* v_dir_1161_; lean_object* v_srcDir_1162_; lean_object* v_srcDir_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_config_1160_ = lean_ctor_get(v_x2_1146_, 6);
v_dir_1161_ = lean_ctor_get(v_x2_1146_, 4);
v_srcDir_1162_ = lean_ctor_get(v_config_1160_, 4);
v_srcDir_1163_ = lean_ctor_get(v_config_1156_, 1);
lean_inc_ref(v_srcDir_1162_);
v___x_1164_ = l_System_FilePath_normalize(v_srcDir_1162_);
lean_inc_ref(v_dir_1161_);
v___x_1165_ = l_Lake_joinRelative(v_dir_1161_, v___x_1164_);
lean_inc_ref(v_srcDir_1163_);
v___x_1166_ = l_Lake_joinRelative(v___x_1165_, v_srcDir_1163_);
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_b_1150_);
v_i_1148_ = v___x_1153_;
v_b_1150_ = v___x_1167_;
goto _start;
}
}
else
{
lean_dec_ref(v_x2_1146_);
return v_b_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1169_, lean_object* v_as_1170_, lean_object* v_i_1171_, lean_object* v_stop_1172_, lean_object* v_b_1173_){
_start:
{
size_t v_i_boxed_1174_; size_t v_stop_boxed_1175_; lean_object* v_res_1176_; 
v_i_boxed_1174_ = lean_unbox_usize(v_i_1171_);
lean_dec(v_i_1171_);
v_stop_boxed_1175_ = lean_unbox_usize(v_stop_1172_);
lean_dec(v_stop_1172_);
v_res_1176_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1169_, v_as_1170_, v_i_boxed_1174_, v_stop_boxed_1175_, v_b_1173_);
lean_dec_ref(v_as_1170_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1177_, size_t v_i_1178_, size_t v_stop_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v___y_1182_; uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_eq(v_i_1178_, v_stop_1179_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v_targetDecls_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1187_ = lean_array_uget_borrowed(v_as_1177_, v_i_1178_);
v_targetDecls_1188_ = lean_ctor_get(v___x_1187_, 13);
v___x_1189_ = lean_array_get_size(v_targetDecls_1188_);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_nat_dec_lt(v___x_1190_, v___x_1189_);
if (v___x_1191_ == 0)
{
v___y_1182_ = v_b_1180_;
goto v___jp_1181_;
}
else
{
size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_usize_of_nat(v___x_1189_);
v___x_1193_ = ((size_t)0ULL);
lean_inc(v___x_1187_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1187_, v_targetDecls_1188_, v___x_1192_, v___x_1193_, v_b_1180_);
v___y_1182_ = v___x_1194_;
goto v___jp_1181_;
}
}
else
{
return v_b_1180_;
}
v___jp_1181_:
{
size_t v___x_1183_; size_t v___x_1184_; 
v___x_1183_ = ((size_t)1ULL);
v___x_1184_ = lean_usize_add(v_i_1178_, v___x_1183_);
v_i_1178_ = v___x_1184_;
v_b_1180_ = v___y_1182_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1195_, lean_object* v_i_1196_, lean_object* v_stop_1197_, lean_object* v_b_1198_){
_start:
{
size_t v_i_boxed_1199_; size_t v_stop_boxed_1200_; lean_object* v_res_1201_; 
v_i_boxed_1199_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_stop_boxed_1200_ = lean_unbox_usize(v_stop_1197_);
lean_dec(v_stop_1197_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1195_, v_i_boxed_1199_, v_stop_boxed_1200_, v_b_1198_);
lean_dec_ref(v_as_1195_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1202_){
_start:
{
lean_object* v_packages_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_packages_1203_ = lean_ctor_get(v_self_1202_, 5);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = lean_array_get_size(v_packages_1203_);
v___x_1207_ = lean_nat_dec_lt(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_nat_dec_le(v___x_1206_, v___x_1206_);
if (v___x_1208_ == 0)
{
if (v___x_1207_ == 0)
{
return v___x_1204_;
}
else
{
size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = lean_usize_of_nat(v___x_1206_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1203_, v___x_1209_, v___x_1210_, v___x_1204_);
return v___x_1211_;
}
}
else
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = lean_usize_of_nat(v___x_1206_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1203_, v___x_1212_, v___x_1213_, v___x_1204_);
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lake_Workspace_leanSrcPath(v_self_1215_);
lean_dec_ref(v_self_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1217_, size_t v_i_1218_, size_t v_stop_1219_, lean_object* v_b_1220_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_usize_dec_eq(v_i_1218_, v_stop_1219_);
if (v___x_1221_ == 0)
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; lean_object* v_config_1225_; lean_object* v_dir_1226_; lean_object* v_buildDir_1227_; lean_object* v_nativeLibDir_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_sub(v_i_1218_, v___x_1222_);
v___x_1224_ = lean_array_uget_borrowed(v_as_1217_, v___x_1223_);
v_config_1225_ = lean_ctor_get(v___x_1224_, 6);
v_dir_1226_ = lean_ctor_get(v___x_1224_, 4);
v_buildDir_1227_ = lean_ctor_get(v_config_1225_, 5);
v_nativeLibDir_1228_ = lean_ctor_get(v_config_1225_, 7);
lean_inc_ref(v_buildDir_1227_);
v___x_1229_ = l_System_FilePath_normalize(v_buildDir_1227_);
lean_inc_ref(v_dir_1226_);
v___x_1230_ = l_Lake_joinRelative(v_dir_1226_, v___x_1229_);
lean_inc_ref(v_nativeLibDir_1228_);
v___x_1231_ = l_System_FilePath_normalize(v_nativeLibDir_1228_);
v___x_1232_ = l_Lake_joinRelative(v___x_1230_, v___x_1231_);
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v_b_1220_);
v_i_1218_ = v___x_1223_;
v_b_1220_ = v___x_1233_;
goto _start;
}
else
{
return v_b_1220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1235_, lean_object* v_i_1236_, lean_object* v_stop_1237_, lean_object* v_b_1238_){
_start:
{
size_t v_i_boxed_1239_; size_t v_stop_boxed_1240_; lean_object* v_res_1241_; 
v_i_boxed_1239_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_stop_boxed_1240_ = lean_unbox_usize(v_stop_1237_);
lean_dec(v_stop_1237_);
v_res_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1235_, v_i_boxed_1239_, v_stop_boxed_1240_, v_b_1238_);
lean_dec_ref(v_as_1235_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1242_){
_start:
{
lean_object* v_packages_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_packages_1243_ = lean_ctor_get(v_self_1242_, 5);
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_array_get_size(v_packages_1243_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_nat_dec_lt(v___x_1246_, v___x_1245_);
if (v___x_1247_ == 0)
{
return v___x_1244_;
}
else
{
size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_usize_of_nat(v___x_1245_);
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1243_, v___x_1248_, v___x_1249_, v___x_1244_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lake_Workspace_sharedLibPath(v_self_1251_);
lean_dec_ref(v_self_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1253_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = l_System_Platform_isWindows;
if (v___x_1254_ == 0)
{
lean_object* v_lakeEnv_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_lakeEnv_1255_ = lean_ctor_get(v_self_1253_, 1);
v___x_1256_ = l_Lake_Workspace_binPath(v_self_1253_);
v___x_1257_ = l_Lake_Env_path(v_lakeEnv_1255_);
v___x_1258_ = l_List_appendTR___redArg(v___x_1256_, v___x_1257_);
return v___x_1258_;
}
else
{
lean_object* v_lakeEnv_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_lakeEnv_1259_ = lean_ctor_get(v_self_1253_, 1);
v___x_1260_ = l_Lake_Workspace_binPath(v_self_1253_);
v___x_1261_ = l_Lake_Workspace_sharedLibPath(v_self_1253_);
v___x_1262_ = l_List_appendTR___redArg(v___x_1260_, v___x_1261_);
v___x_1263_ = l_Lake_Env_path(v_lakeEnv_1259_);
v___x_1264_ = l_List_appendTR___redArg(v___x_1262_, v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lake_Workspace_augmentedPath(v_self_1265_);
lean_dec_ref(v_self_1265_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1267_){
_start:
{
lean_object* v_lakeEnv_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_lakeEnv_1268_ = lean_ctor_get(v_self_1267_, 1);
v___x_1269_ = l_Lake_Workspace_leanPath(v_self_1267_);
v___x_1270_ = l_Lake_Env_leanPath(v_lakeEnv_1268_);
v___x_1271_ = l_List_appendTR___redArg(v___x_1269_, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lake_Workspace_augmentedLeanPath(v_self_1272_);
lean_dec_ref(v_self_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1274_){
_start:
{
lean_object* v_lakeEnv_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_lakeEnv_1275_ = lean_ctor_get(v_self_1274_, 1);
v___x_1276_ = l_Lake_Workspace_leanSrcPath(v_self_1274_);
v___x_1277_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1275_);
v___x_1278_ = l_List_appendTR___redArg(v___x_1276_, v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1279_);
lean_dec_ref(v_self_1279_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1281_){
_start:
{
lean_object* v_lakeEnv_1282_; lean_object* v_lean_1283_; lean_object* v_initSharedLibPath_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_lakeEnv_1282_ = lean_ctor_get(v_self_1281_, 1);
v_lean_1283_ = lean_ctor_get(v_lakeEnv_1282_, 1);
v_initSharedLibPath_1284_ = lean_ctor_get(v_lakeEnv_1282_, 16);
lean_inc(v_initSharedLibPath_1284_);
v___x_1285_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1283_);
v___x_1286_ = l_Lake_Workspace_sharedLibPath(v_self_1281_);
lean_dec_ref(v_self_1281_);
v___x_1287_ = l_List_appendTR___redArg(v___x_1285_, v___x_1286_);
v___x_1288_ = l_List_appendTR___redArg(v___x_1287_, v_initSharedLibPath_1284_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1304_){
_start:
{
lean_object* v_lakeEnv_1305_; lean_object* v_root_1306_; lean_object* v_lakeCache_1307_; lean_object* v_enableArtifactCache_x3f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___x_1341_; lean_object* v___y_1343_; uint8_t v_val_1362_; 
v_lakeEnv_1305_ = lean_ctor_get(v_self_1304_, 1);
v_root_1306_ = lean_ctor_get(v_self_1304_, 0);
v_lakeCache_1307_ = lean_ctor_get(v_self_1304_, 3);
v_enableArtifactCache_x3f_1308_ = lean_ctor_get(v_lakeEnv_1305_, 6);
lean_inc_ref(v_lakeEnv_1305_);
v___x_1309_ = l_Lake_Env_baseVars(v_lakeEnv_1305_);
v___x_1310_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1307_);
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_lakeCache_1307_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1341_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
if (lean_obj_tag(v_enableArtifactCache_x3f_1308_) == 0)
{
lean_object* v_config_1365_; lean_object* v_enableArtifactCache_x3f_1366_; 
v_config_1365_ = lean_ctor_get(v_root_1306_, 6);
v_enableArtifactCache_x3f_1366_ = lean_ctor_get(v_config_1365_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1366_) == 1)
{
lean_object* v_val_1367_; uint8_t v___x_1368_; 
v_val_1367_ = lean_ctor_get(v_enableArtifactCache_x3f_1366_, 0);
v___x_1368_ = lean_unbox(v_val_1367_);
v_val_1362_ = v___x_1368_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1369_; 
v___x_1369_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__11));
v___y_1343_ = v___x_1369_;
goto v___jp_1342_;
}
}
else
{
lean_object* v_val_1370_; uint8_t v___x_1371_; 
v_val_1370_ = lean_ctor_get(v_enableArtifactCache_x3f_1308_, 0);
v___x_1371_ = lean_unbox(v_val_1370_);
v_val_1362_ = v___x_1371_;
goto v___jp_1361_;
}
v___jp_1313_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_vars_1333_; uint8_t v___x_1334_; 
lean_inc_ref(v___y_1316_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___y_1316_);
lean_ctor_set(v___x_1319_, 1, v___y_1318_);
v___x_1320_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1321_ = l_Lake_Workspace_augmentedPath(v_self_1304_);
v___x_1322_ = l_System_SearchPath_toString(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1320_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_unsigned_to_nat(6u);
v___x_1326_ = lean_mk_empty_array_with_capacity(v___x_1325_);
v___x_1327_ = lean_array_push(v___x_1326_, v___x_1312_);
v___x_1328_ = lean_array_push(v___x_1327_, v___y_1314_);
v___x_1329_ = lean_array_push(v___x_1328_, v___y_1315_);
v___x_1330_ = lean_array_push(v___x_1329_, v___y_1317_);
v___x_1331_ = lean_array_push(v___x_1330_, v___x_1319_);
v___x_1332_ = lean_array_push(v___x_1331_, v___x_1324_);
v_vars_1333_ = l_Array_append___redArg(v___x_1309_, v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = l_System_Platform_isWindows;
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1335_ = l_Lake_sharedLibPathEnvVar;
v___x_1336_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1304_);
v___x_1337_ = l_System_SearchPath_toString(v___x_1336_);
v___x_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1335_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = lean_array_push(v_vars_1333_, v___x_1339_);
return v___x_1340_;
}
else
{
lean_dec_ref(v_self_1304_);
return v_vars_1333_;
}
}
v___jp_1342_:
{
lean_object* v_config_1344_; uint8_t v_bootstrap_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_config_1344_ = lean_ctor_get(v_root_1306_, 6);
v_bootstrap_1345_ = lean_ctor_get_uint8(v_config_1344_, sizeof(void*)*26);
lean_inc(v___y_1343_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1341_);
lean_ctor_set(v___x_1346_, 1, v___y_1343_);
v___x_1347_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1348_ = l_Lake_Workspace_augmentedLeanPath(v_self_1304_);
v___x_1349_ = l_System_SearchPath_toString(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1347_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
v___x_1353_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1304_);
v___x_1354_ = l_System_SearchPath_toString(v___x_1353_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1352_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (v_bootstrap_1345_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = l_Lake_Env_leanGithash(v_lakeEnv_1305_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
v___y_1314_ = v___x_1346_;
v___y_1315_ = v___x_1351_;
v___y_1316_ = v___x_1357_;
v___y_1317_ = v___x_1356_;
v___y_1318_ = v___x_1359_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_box(0);
v___y_1314_ = v___x_1346_;
v___y_1315_ = v___x_1351_;
v___y_1316_ = v___x_1357_;
v___y_1317_ = v___x_1356_;
v___y_1318_ = v___x_1360_;
goto v___jp_1313_;
}
}
v___jp_1361_:
{
if (v_val_1362_ == 0)
{
lean_object* v___x_1363_; 
v___x_1363_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__7));
v___y_1343_ = v___x_1363_;
goto v___jp_1342_;
}
else
{
lean_object* v___x_1364_; 
v___x_1364_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__9));
v___y_1343_ = v___x_1364_;
goto v___jp_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1372_, size_t v_i_1373_, size_t v_stop_1374_, lean_object* v_b_1375_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_eq(v_i_1373_, v_stop_1374_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_array_uget_borrowed(v_as_1372_, v_i_1373_);
lean_inc(v___x_1378_);
v___x_1379_ = l_Lake_Package_clean(v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; size_t v___x_1381_; size_t v___x_1382_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = ((size_t)1ULL);
v___x_1382_ = lean_usize_add(v_i_1373_, v___x_1381_);
v_i_1373_ = v___x_1382_;
v_b_1375_ = v_a_1380_;
goto _start;
}
else
{
return v___x_1379_;
}
}
else
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_b_1375_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1385_, lean_object* v_i_1386_, lean_object* v_stop_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_){
_start:
{
size_t v_i_boxed_1390_; size_t v_stop_boxed_1391_; lean_object* v_res_1392_; 
v_i_boxed_1390_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_stop_boxed_1391_ = lean_unbox_usize(v_stop_1387_);
lean_dec(v_stop_1387_);
v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1385_, v_i_boxed_1390_, v_stop_boxed_1391_, v_b_1388_);
lean_dec_ref(v_as_1385_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* v_self_1393_){
_start:
{
lean_object* v_packages_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_packages_1395_ = lean_ctor_get(v_self_1393_, 5);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_array_get_size(v_packages_1395_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_nat_dec_lt(v___x_1396_, v___x_1397_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
return v___x_1400_;
}
else
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_nat_dec_le(v___x_1397_, v___x_1397_);
if (v___x_1401_ == 0)
{
if (v___x_1399_ == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1398_);
return v___x_1402_;
}
else
{
size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = lean_usize_of_nat(v___x_1397_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1395_, v___x_1403_, v___x_1404_, v___x_1398_);
return v___x_1405_;
}
}
else
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = lean_usize_of_nat(v___x_1397_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1395_, v___x_1406_, v___x_1407_, v___x_1398_);
return v___x_1408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lake_Workspace_clean(v_self_1409_);
lean_dec_ref(v_self_1409_);
return v_res_1411_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanExe(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ExternLib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_TargetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakeConfig(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

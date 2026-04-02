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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lake_Package_isLocalModule(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_computeLakeCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cache"};
static const lean_object* l_Lake_computeLakeCache___closed__0 = (const lean_object*)&l_Lake_computeLakeCache___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_computeLakeCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeLakeCache___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace___private__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Workspace_findPackageByKey_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Workspace_findPackageByKey_x3f___closed__0 = (const lean_object*)&l_Lake_Workspace_findPackageByKey_x3f___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Workspace___private__1(lean_object* v_pkg_23_, lean_object* v_lakeEnv_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lake_computeLakeCache(v_pkg_23_, v_lakeEnv_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace___private__1___boxed(lean_object* v_pkg_26_, lean_object* v_lakeEnv_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_Workspace___private__1(v_pkg_26_, v_lakeEnv_27_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(lean_object* v_k_261_, lean_object* v_v_262_, lean_object* v_t_263_){
_start:
{
if (lean_obj_tag(v_t_263_) == 0)
{
lean_object* v_size_264_; lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v_l_267_; lean_object* v_r_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_548_; 
v_size_264_ = lean_ctor_get(v_t_263_, 0);
v_k_265_ = lean_ctor_get(v_t_263_, 1);
v_v_266_ = lean_ctor_get(v_t_263_, 2);
v_l_267_ = lean_ctor_get(v_t_263_, 3);
v_r_268_ = lean_ctor_get(v_t_263_, 4);
v_isSharedCheck_548_ = !lean_is_exclusive(v_t_263_);
if (v_isSharedCheck_548_ == 0)
{
v___x_270_ = v_t_263_;
v_isShared_271_ = v_isSharedCheck_548_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_r_268_);
lean_inc(v_l_267_);
lean_inc(v_v_266_);
lean_inc(v_k_265_);
lean_inc(v_size_264_);
lean_dec(v_t_263_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_548_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
uint8_t v___x_272_; 
v___x_272_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_261_, v_k_265_);
switch(v___x_272_)
{
case 0:
{
lean_object* v_impl_273_; lean_object* v___x_274_; 
lean_dec(v_size_264_);
v_impl_273_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_k_261_, v_v_262_, v_l_267_);
v___x_274_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_268_) == 0)
{
lean_object* v_size_275_; lean_object* v_size_276_; lean_object* v_k_277_; lean_object* v_v_278_; lean_object* v_l_279_; lean_object* v_r_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_size_275_ = lean_ctor_get(v_r_268_, 0);
v_size_276_ = lean_ctor_get(v_impl_273_, 0);
lean_inc(v_size_276_);
v_k_277_ = lean_ctor_get(v_impl_273_, 1);
lean_inc(v_k_277_);
v_v_278_ = lean_ctor_get(v_impl_273_, 2);
lean_inc(v_v_278_);
v_l_279_ = lean_ctor_get(v_impl_273_, 3);
lean_inc(v_l_279_);
v_r_280_ = lean_ctor_get(v_impl_273_, 4);
lean_inc(v_r_280_);
v___x_281_ = lean_unsigned_to_nat(3u);
v___x_282_ = lean_nat_mul(v___x_281_, v_size_275_);
v___x_283_ = lean_nat_dec_lt(v___x_282_, v_size_276_);
lean_dec(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
lean_dec(v_r_280_);
lean_dec(v_l_279_);
lean_dec(v_v_278_);
lean_dec(v_k_277_);
v___x_284_ = lean_nat_add(v___x_274_, v_size_276_);
lean_dec(v_size_276_);
v___x_285_ = lean_nat_add(v___x_284_, v_size_275_);
lean_dec(v___x_284_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 3, v_impl_273_);
lean_ctor_set(v___x_270_, 0, v___x_285_);
v___x_287_ = v___x_270_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_impl_273_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_r_268_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_354_; 
v_isSharedCheck_354_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; 
v_unused_355_ = lean_ctor_get(v_impl_273_, 4);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_impl_273_, 2);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v_impl_273_, 1);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_359_);
v___x_290_ = v_impl_273_;
v_isShared_291_ = v_isSharedCheck_354_;
goto v_resetjp_289_;
}
else
{
lean_dec(v_impl_273_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_354_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_size_292_; lean_object* v_size_293_; lean_object* v_k_294_; lean_object* v_v_295_; lean_object* v_l_296_; lean_object* v_r_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_size_292_ = lean_ctor_get(v_l_279_, 0);
v_size_293_ = lean_ctor_get(v_r_280_, 0);
v_k_294_ = lean_ctor_get(v_r_280_, 1);
v_v_295_ = lean_ctor_get(v_r_280_, 2);
v_l_296_ = lean_ctor_get(v_r_280_, 3);
v_r_297_ = lean_ctor_get(v_r_280_, 4);
v___x_298_ = lean_unsigned_to_nat(2u);
v___x_299_ = lean_nat_mul(v___x_298_, v_size_292_);
v___x_300_ = lean_nat_dec_lt(v_size_293_, v___x_299_);
lean_dec(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_329_; 
lean_inc(v_r_297_);
lean_inc(v_l_296_);
lean_inc(v_v_295_);
lean_inc(v_k_294_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_r_280_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; lean_object* v_unused_331_; lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_330_ = lean_ctor_get(v_r_280_, 4);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_r_280_, 3);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_r_280_, 2);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_r_280_, 1);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_r_280_, 0);
lean_dec(v_unused_334_);
v___x_302_ = v_r_280_;
v_isShared_303_ = v_isSharedCheck_329_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_r_280_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_329_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___x_317_; lean_object* v___y_319_; 
v___x_304_ = lean_nat_add(v___x_274_, v_size_276_);
lean_dec(v_size_276_);
v___x_305_ = lean_nat_add(v___x_304_, v_size_275_);
lean_dec(v___x_304_);
v___x_317_ = lean_nat_add(v___x_274_, v_size_292_);
if (lean_obj_tag(v_l_296_) == 0)
{
lean_object* v_size_327_; 
v_size_327_ = lean_ctor_get(v_l_296_, 0);
lean_inc(v_size_327_);
v___y_319_ = v_size_327_;
goto v___jp_318_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___y_319_ = v___x_328_;
goto v___jp_318_;
}
v___jp_306_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_nat_add(v___y_307_, v___y_309_);
lean_dec(v___y_309_);
lean_dec(v___y_307_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 4, v_r_268_);
lean_ctor_set(v___x_302_, 3, v_r_297_);
lean_ctor_set(v___x_302_, 2, v_v_266_);
lean_ctor_set(v___x_302_, 1, v_k_265_);
lean_ctor_set(v___x_302_, 0, v___x_310_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_r_297_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_r_268_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v___x_312_);
lean_ctor_set(v___x_290_, 3, v___y_308_);
lean_ctor_set(v___x_290_, 2, v_v_295_);
lean_ctor_set(v___x_290_, 1, v_k_294_);
lean_ctor_set(v___x_290_, 0, v___x_305_);
v___x_314_ = v___x_290_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_k_294_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v_v_295_);
lean_ctor_set(v_reuseFailAlloc_315_, 3, v___y_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 4, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
v___jp_318_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_nat_add(v___x_317_, v___y_319_);
lean_dec(v___y_319_);
lean_dec(v___x_317_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_l_296_);
lean_ctor_set(v___x_270_, 3, v_l_279_);
lean_ctor_set(v___x_270_, 2, v_v_278_);
lean_ctor_set(v___x_270_, 1, v_k_277_);
lean_ctor_set(v___x_270_, 0, v___x_320_);
v___x_322_ = v___x_270_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_k_277_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_v_278_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_l_279_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_l_296_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_nat_add(v___x_274_, v_size_275_);
if (lean_obj_tag(v_r_297_) == 0)
{
lean_object* v_size_324_; 
v_size_324_ = lean_ctor_get(v_r_297_, 0);
lean_inc(v_size_324_);
v___y_307_ = v___x_323_;
v___y_308_ = v___x_322_;
v___y_309_ = v_size_324_;
goto v___jp_306_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___y_307_ = v___x_323_;
v___y_308_ = v___x_322_;
v___y_309_ = v___x_325_;
goto v___jp_306_;
}
}
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_del_object(v___x_270_);
v___x_335_ = lean_nat_add(v___x_274_, v_size_276_);
lean_dec(v_size_276_);
v___x_336_ = lean_nat_add(v___x_335_, v_size_275_);
lean_dec(v___x_335_);
v___x_337_ = lean_nat_add(v___x_274_, v_size_275_);
v___x_338_ = lean_nat_add(v___x_337_, v_size_293_);
lean_dec(v___x_337_);
lean_inc_ref(v_r_268_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 4, v_r_268_);
lean_ctor_set(v___x_290_, 3, v_r_280_);
lean_ctor_set(v___x_290_, 2, v_v_266_);
lean_ctor_set(v___x_290_, 1, v_k_265_);
lean_ctor_set(v___x_290_, 0, v___x_338_);
v___x_340_ = v___x_290_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_r_280_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_r_268_);
v___x_340_ = v_reuseFailAlloc_353_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_isSharedCheck_347_ = !lean_is_exclusive(v_r_268_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; lean_object* v_unused_349_; lean_object* v_unused_350_; lean_object* v_unused_351_; lean_object* v_unused_352_; 
v_unused_348_ = lean_ctor_get(v_r_268_, 4);
lean_dec(v_unused_348_);
v_unused_349_ = lean_ctor_get(v_r_268_, 3);
lean_dec(v_unused_349_);
v_unused_350_ = lean_ctor_get(v_r_268_, 2);
lean_dec(v_unused_350_);
v_unused_351_ = lean_ctor_get(v_r_268_, 1);
lean_dec(v_unused_351_);
v_unused_352_ = lean_ctor_get(v_r_268_, 0);
lean_dec(v_unused_352_);
v___x_342_ = v_r_268_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_r_268_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 4, v___x_340_);
lean_ctor_set(v___x_342_, 3, v_l_279_);
lean_ctor_set(v___x_342_, 2, v_v_278_);
lean_ctor_set(v___x_342_, 1, v_k_277_);
lean_ctor_set(v___x_342_, 0, v___x_336_);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_k_277_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_v_278_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_l_279_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v___x_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_360_; 
v_l_360_ = lean_ctor_get(v_impl_273_, 3);
lean_inc(v_l_360_);
if (lean_obj_tag(v_l_360_) == 0)
{
lean_object* v_r_361_; lean_object* v_k_362_; lean_object* v_v_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_374_; 
v_r_361_ = lean_ctor_get(v_impl_273_, 4);
v_k_362_ = lean_ctor_get(v_impl_273_, 1);
v_v_363_ = lean_ctor_get(v_impl_273_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; 
v_unused_375_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_376_);
v___x_365_ = v_impl_273_;
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_r_361_);
lean_inc(v_v_363_);
lean_inc(v_k_362_);
lean_dec(v_impl_273_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_374_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_361_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 3, v_r_361_);
lean_ctor_set(v___x_365_, 2, v_v_266_);
lean_ctor_set(v___x_365_, 1, v_k_265_);
lean_ctor_set(v___x_365_, 0, v___x_274_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_r_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_r_361_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v___x_369_);
lean_ctor_set(v___x_270_, 3, v_l_360_);
lean_ctor_set(v___x_270_, 2, v_v_363_);
lean_ctor_set(v___x_270_, 1, v_k_362_);
lean_ctor_set(v___x_270_, 0, v___x_367_);
v___x_371_ = v___x_270_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_k_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_v_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_l_360_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v___x_369_);
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
else
{
lean_object* v_r_377_; 
v_r_377_ = lean_ctor_get(v_impl_273_, 4);
lean_inc(v_r_377_);
if (lean_obj_tag(v_r_377_) == 0)
{
lean_object* v_k_378_; lean_object* v_v_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_402_; 
v_k_378_ = lean_ctor_get(v_impl_273_, 1);
v_v_379_ = lean_ctor_get(v_impl_273_, 2);
v_isSharedCheck_402_ = !lean_is_exclusive(v_impl_273_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; lean_object* v_unused_404_; lean_object* v_unused_405_; 
v_unused_403_ = lean_ctor_get(v_impl_273_, 4);
lean_dec(v_unused_403_);
v_unused_404_ = lean_ctor_get(v_impl_273_, 3);
lean_dec(v_unused_404_);
v_unused_405_ = lean_ctor_get(v_impl_273_, 0);
lean_dec(v_unused_405_);
v___x_381_ = v_impl_273_;
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_v_379_);
lean_inc(v_k_378_);
lean_dec(v_impl_273_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_k_383_; lean_object* v_v_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_398_; 
v_k_383_ = lean_ctor_get(v_r_377_, 1);
v_v_384_ = lean_ctor_get(v_r_377_, 2);
v_isSharedCheck_398_ = !lean_is_exclusive(v_r_377_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; lean_object* v_unused_400_; lean_object* v_unused_401_; 
v_unused_399_ = lean_ctor_get(v_r_377_, 4);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_r_377_, 3);
lean_dec(v_unused_400_);
v_unused_401_ = lean_ctor_get(v_r_377_, 0);
lean_dec(v_unused_401_);
v___x_386_ = v_r_377_;
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_v_384_);
lean_inc(v_k_383_);
lean_dec(v_r_377_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_398_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_unsigned_to_nat(3u);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 4, v_l_360_);
lean_ctor_set(v___x_386_, 3, v_l_360_);
lean_ctor_set(v___x_386_, 2, v_v_379_);
lean_ctor_set(v___x_386_, 1, v_k_378_);
lean_ctor_set(v___x_386_, 0, v___x_274_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_k_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_v_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_l_360_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_l_360_);
v___x_390_ = v_reuseFailAlloc_397_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 4, v_l_360_);
lean_ctor_set(v___x_381_, 2, v_v_266_);
lean_ctor_set(v___x_381_, 1, v_k_265_);
lean_ctor_set(v___x_381_, 0, v___x_274_);
v___x_392_ = v___x_381_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_l_360_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_l_360_);
v___x_392_ = v_reuseFailAlloc_396_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_394_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v___x_392_);
lean_ctor_set(v___x_270_, 3, v___x_390_);
lean_ctor_set(v___x_270_, 2, v_v_384_);
lean_ctor_set(v___x_270_, 1, v_k_383_);
lean_ctor_set(v___x_270_, 0, v___x_388_);
v___x_394_ = v___x_270_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_k_383_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_v_384_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(2u);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_r_377_);
lean_ctor_set(v___x_270_, 3, v_impl_273_);
lean_ctor_set(v___x_270_, 0, v___x_406_);
v___x_408_ = v___x_270_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_impl_273_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_r_377_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
case 1:
{
lean_object* v___x_411_; 
lean_dec(v_v_266_);
lean_dec(v_k_265_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 2, v_v_262_);
lean_ctor_set(v___x_270_, 1, v_k_261_);
v___x_411_ = v___x_270_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_size_264_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_k_261_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_v_262_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_l_267_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_r_268_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
default: 
{
lean_object* v_impl_413_; lean_object* v___x_414_; 
lean_dec(v_size_264_);
v_impl_413_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_k_261_, v_v_262_, v_r_268_);
v___x_414_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_267_) == 0)
{
lean_object* v_size_415_; lean_object* v_size_416_; lean_object* v_k_417_; lean_object* v_v_418_; lean_object* v_l_419_; lean_object* v_r_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_size_415_ = lean_ctor_get(v_l_267_, 0);
v_size_416_ = lean_ctor_get(v_impl_413_, 0);
lean_inc(v_size_416_);
v_k_417_ = lean_ctor_get(v_impl_413_, 1);
lean_inc(v_k_417_);
v_v_418_ = lean_ctor_get(v_impl_413_, 2);
lean_inc(v_v_418_);
v_l_419_ = lean_ctor_get(v_impl_413_, 3);
lean_inc(v_l_419_);
v_r_420_ = lean_ctor_get(v_impl_413_, 4);
lean_inc(v_r_420_);
v___x_421_ = lean_unsigned_to_nat(3u);
v___x_422_ = lean_nat_mul(v___x_421_, v_size_415_);
v___x_423_ = lean_nat_dec_lt(v___x_422_, v_size_416_);
lean_dec(v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec(v_r_420_);
lean_dec(v_l_419_);
lean_dec(v_v_418_);
lean_dec(v_k_417_);
v___x_424_ = lean_nat_add(v___x_414_, v_size_415_);
v___x_425_ = lean_nat_add(v___x_424_, v_size_416_);
lean_dec(v_size_416_);
lean_dec(v___x_424_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_impl_413_);
lean_ctor_set(v___x_270_, 0, v___x_425_);
v___x_427_ = v___x_270_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_l_267_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_impl_413_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
else
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_492_; 
v_isSharedCheck_492_ = !lean_is_exclusive(v_impl_413_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_493_ = lean_ctor_get(v_impl_413_, 4);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_impl_413_, 3);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_impl_413_, 2);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v_impl_413_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_impl_413_, 0);
lean_dec(v_unused_497_);
v___x_430_ = v_impl_413_;
v_isShared_431_ = v_isSharedCheck_492_;
goto v_resetjp_429_;
}
else
{
lean_dec(v_impl_413_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_492_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_size_432_; lean_object* v_k_433_; lean_object* v_v_434_; lean_object* v_l_435_; lean_object* v_r_436_; lean_object* v_size_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_size_432_ = lean_ctor_get(v_l_419_, 0);
v_k_433_ = lean_ctor_get(v_l_419_, 1);
v_v_434_ = lean_ctor_get(v_l_419_, 2);
v_l_435_ = lean_ctor_get(v_l_419_, 3);
v_r_436_ = lean_ctor_get(v_l_419_, 4);
v_size_437_ = lean_ctor_get(v_r_420_, 0);
v___x_438_ = lean_unsigned_to_nat(2u);
v___x_439_ = lean_nat_mul(v___x_438_, v_size_437_);
v___x_440_ = lean_nat_dec_lt(v_size_432_, v___x_439_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_468_; 
lean_inc(v_r_436_);
lean_inc(v_l_435_);
lean_inc(v_v_434_);
lean_inc(v_k_433_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_l_419_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_469_ = lean_ctor_get(v_l_419_, 4);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_l_419_, 3);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_l_419_, 2);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_l_419_, 1);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_l_419_, 0);
lean_dec(v_unused_473_);
v___x_442_ = v_l_419_;
v_isShared_443_ = v_isSharedCheck_468_;
goto v_resetjp_441_;
}
else
{
lean_dec(v_l_419_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_468_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___y_447_; lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_458_; 
v___x_444_ = lean_nat_add(v___x_414_, v_size_415_);
v___x_445_ = lean_nat_add(v___x_444_, v_size_416_);
lean_dec(v_size_416_);
if (lean_obj_tag(v_l_435_) == 0)
{
lean_object* v_size_466_; 
v_size_466_ = lean_ctor_get(v_l_435_, 0);
lean_inc(v_size_466_);
v___y_458_ = v_size_466_;
goto v___jp_457_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___y_458_ = v___x_467_;
goto v___jp_457_;
}
v___jp_446_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_nat_add(v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec(v___y_448_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 4, v_r_420_);
lean_ctor_set(v___x_442_, 3, v_r_436_);
lean_ctor_set(v___x_442_, 2, v_v_418_);
lean_ctor_set(v___x_442_, 1, v_k_417_);
lean_ctor_set(v___x_442_, 0, v___x_450_);
v___x_452_ = v___x_442_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_k_417_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_v_418_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_r_436_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_r_420_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_454_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 4, v___x_452_);
lean_ctor_set(v___x_430_, 3, v___y_447_);
lean_ctor_set(v___x_430_, 2, v_v_434_);
lean_ctor_set(v___x_430_, 1, v_k_433_);
lean_ctor_set(v___x_430_, 0, v___x_445_);
v___x_454_ = v___x_430_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_k_433_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_v_434_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v___y_447_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_nat_add(v___x_444_, v___y_458_);
lean_dec(v___y_458_);
lean_dec(v___x_444_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_l_435_);
lean_ctor_set(v___x_270_, 0, v___x_459_);
v___x_461_ = v___x_270_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_l_267_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_l_435_);
v___x_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = lean_nat_add(v___x_414_, v_size_437_);
if (lean_obj_tag(v_r_436_) == 0)
{
lean_object* v_size_463_; 
v_size_463_ = lean_ctor_get(v_r_436_, 0);
lean_inc(v_size_463_);
v___y_447_ = v___x_461_;
v___y_448_ = v___x_462_;
v___y_449_ = v_size_463_;
goto v___jp_446_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___y_447_ = v___x_461_;
v___y_448_ = v___x_462_;
v___y_449_ = v___x_464_;
goto v___jp_446_;
}
}
}
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
lean_del_object(v___x_270_);
v___x_474_ = lean_nat_add(v___x_414_, v_size_415_);
v___x_475_ = lean_nat_add(v___x_474_, v_size_416_);
lean_dec(v_size_416_);
v___x_476_ = lean_nat_add(v___x_474_, v_size_432_);
lean_dec(v___x_474_);
lean_inc_ref(v_l_267_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 4, v_l_419_);
lean_ctor_set(v___x_430_, 3, v_l_267_);
lean_ctor_set(v___x_430_, 2, v_v_266_);
lean_ctor_set(v___x_430_, 1, v_k_265_);
lean_ctor_set(v___x_430_, 0, v___x_476_);
v___x_478_ = v___x_430_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_l_267_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_l_419_);
v___x_478_ = v_reuseFailAlloc_491_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_isSharedCheck_485_ = !lean_is_exclusive(v_l_267_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; lean_object* v_unused_487_; lean_object* v_unused_488_; lean_object* v_unused_489_; lean_object* v_unused_490_; 
v_unused_486_ = lean_ctor_get(v_l_267_, 4);
lean_dec(v_unused_486_);
v_unused_487_ = lean_ctor_get(v_l_267_, 3);
lean_dec(v_unused_487_);
v_unused_488_ = lean_ctor_get(v_l_267_, 2);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_l_267_, 1);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_l_267_, 0);
lean_dec(v_unused_490_);
v___x_480_ = v_l_267_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_l_267_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v_r_420_);
lean_ctor_set(v___x_480_, 3, v___x_478_);
lean_ctor_set(v___x_480_, 2, v_v_418_);
lean_ctor_set(v___x_480_, 1, v_k_417_);
lean_ctor_set(v___x_480_, 0, v___x_475_);
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_417_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_v_418_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_r_420_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_498_; 
v_l_498_ = lean_ctor_get(v_impl_413_, 3);
lean_inc(v_l_498_);
if (lean_obj_tag(v_l_498_) == 0)
{
lean_object* v_r_499_; lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_524_; 
v_r_499_ = lean_ctor_get(v_impl_413_, 4);
v_k_500_ = lean_ctor_get(v_impl_413_, 1);
v_v_501_ = lean_ctor_get(v_impl_413_, 2);
v_isSharedCheck_524_ = !lean_is_exclusive(v_impl_413_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; lean_object* v_unused_526_; 
v_unused_525_ = lean_ctor_get(v_impl_413_, 3);
lean_dec(v_unused_525_);
v_unused_526_ = lean_ctor_get(v_impl_413_, 0);
lean_dec(v_unused_526_);
v___x_503_ = v_impl_413_;
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_r_499_);
lean_inc(v_v_501_);
lean_inc(v_k_500_);
lean_dec(v_impl_413_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_k_505_; lean_object* v_v_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_520_; 
v_k_505_ = lean_ctor_get(v_l_498_, 1);
v_v_506_ = lean_ctor_get(v_l_498_, 2);
v_isSharedCheck_520_ = !lean_is_exclusive(v_l_498_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; lean_object* v_unused_522_; lean_object* v_unused_523_; 
v_unused_521_ = lean_ctor_get(v_l_498_, 4);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_l_498_, 3);
lean_dec(v_unused_522_);
v_unused_523_ = lean_ctor_get(v_l_498_, 0);
lean_dec(v_unused_523_);
v___x_508_ = v_l_498_;
v_isShared_509_ = v_isSharedCheck_520_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_v_506_);
lean_inc(v_k_505_);
lean_dec(v_l_498_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_520_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_499_, 2);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v_r_499_);
lean_ctor_set(v___x_508_, 3, v_r_499_);
lean_ctor_set(v___x_508_, 2, v_v_266_);
lean_ctor_set(v___x_508_, 1, v_k_265_);
lean_ctor_set(v___x_508_, 0, v___x_414_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_r_499_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_r_499_);
v___x_512_ = v_reuseFailAlloc_519_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
lean_inc(v_r_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v_r_499_);
lean_ctor_set(v___x_503_, 0, v___x_414_);
v___x_514_ = v___x_503_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_k_500_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_v_501_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_r_499_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_r_499_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v___x_514_);
lean_ctor_set(v___x_270_, 3, v___x_512_);
lean_ctor_set(v___x_270_, 2, v_v_506_);
lean_ctor_set(v___x_270_, 1, v_k_505_);
lean_ctor_set(v___x_270_, 0, v___x_510_);
v___x_516_ = v___x_270_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_k_505_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_v_506_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v___x_514_);
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
else
{
lean_object* v_r_527_; 
v_r_527_ = lean_ctor_get(v_impl_413_, 4);
lean_inc(v_r_527_);
if (lean_obj_tag(v_r_527_) == 0)
{
lean_object* v_k_528_; lean_object* v_v_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_540_; 
v_k_528_ = lean_ctor_get(v_impl_413_, 1);
v_v_529_ = lean_ctor_get(v_impl_413_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_impl_413_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; lean_object* v_unused_542_; lean_object* v_unused_543_; 
v_unused_541_ = lean_ctor_get(v_impl_413_, 4);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_impl_413_, 3);
lean_dec(v_unused_542_);
v_unused_543_ = lean_ctor_get(v_impl_413_, 0);
lean_dec(v_unused_543_);
v___x_531_ = v_impl_413_;
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_v_529_);
lean_inc(v_k_528_);
lean_dec(v_impl_413_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_unsigned_to_nat(3u);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 4, v_l_498_);
lean_ctor_set(v___x_531_, 2, v_v_266_);
lean_ctor_set(v___x_531_, 1, v_k_265_);
lean_ctor_set(v___x_531_, 0, v___x_414_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_l_498_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v_l_498_);
v___x_535_ = v_reuseFailAlloc_539_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_r_527_);
lean_ctor_set(v___x_270_, 3, v___x_535_);
lean_ctor_set(v___x_270_, 2, v_v_529_);
lean_ctor_set(v___x_270_, 1, v_k_528_);
lean_ctor_set(v___x_270_, 0, v___x_533_);
v___x_537_ = v___x_270_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_r_527_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(2u);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 4, v_impl_413_);
lean_ctor_set(v___x_270_, 3, v_r_527_);
lean_ctor_set(v___x_270_, 0, v___x_544_);
v___x_546_ = v___x_270_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_r_527_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_impl_413_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
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
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v_k_261_);
lean_ctor_set(v___x_550_, 2, v_v_262_);
lean_ctor_set(v___x_550_, 3, v_t_263_);
lean_ctor_set(v___x_550_, 4, v_t_263_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_551_, lean_object* v_self_552_){
_start:
{
lean_object* v_root_553_; lean_object* v_lakeEnv_554_; lean_object* v_lakeConfig_555_; lean_object* v_lakeCache_556_; lean_object* v_lakeArgs_x3f_557_; lean_object* v_packages_558_; lean_object* v_packageMap_559_; lean_object* v_facetConfigs_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_570_; 
v_root_553_ = lean_ctor_get(v_self_552_, 0);
v_lakeEnv_554_ = lean_ctor_get(v_self_552_, 1);
v_lakeConfig_555_ = lean_ctor_get(v_self_552_, 2);
v_lakeCache_556_ = lean_ctor_get(v_self_552_, 3);
v_lakeArgs_x3f_557_ = lean_ctor_get(v_self_552_, 4);
v_packages_558_ = lean_ctor_get(v_self_552_, 5);
v_packageMap_559_ = lean_ctor_get(v_self_552_, 6);
v_facetConfigs_560_ = lean_ctor_get(v_self_552_, 7);
v_isSharedCheck_570_ = !lean_is_exclusive(v_self_552_);
if (v_isSharedCheck_570_ == 0)
{
v___x_562_ = v_self_552_;
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_facetConfigs_560_);
lean_inc(v_packageMap_559_);
lean_inc(v_packages_558_);
lean_inc(v_lakeArgs_x3f_557_);
lean_inc(v_lakeCache_556_);
lean_inc(v_lakeConfig_555_);
lean_inc(v_lakeEnv_554_);
lean_inc(v_root_553_);
lean_dec(v_self_552_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_570_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_keyName_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v_keyName_564_ = lean_ctor_get(v_pkg_551_, 2);
lean_inc(v_keyName_564_);
lean_inc_ref(v_pkg_551_);
v___x_565_ = lean_array_push(v_packages_558_, v_pkg_551_);
v___x_566_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_keyName_564_, v_pkg_551_, v_packageMap_559_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 6, v___x_566_);
lean_ctor_set(v___x_562_, 5, v___x_565_);
v___x_568_ = v___x_562_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_root_553_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_lakeEnv_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_lakeConfig_555_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_lakeCache_556_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_lakeArgs_x3f_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 5, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_569_, 6, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_569_, 7, v_facetConfigs_560_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0(lean_object* v_00_u03b2_571_, lean_object* v_k_572_, lean_object* v_v_573_, lean_object* v_t_574_, lean_object* v_hl_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_k_572_, v_v_573_, v_t_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_578_, lean_object* v_self_579_){
_start:
{
lean_object* v_packageMap_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_packageMap_580_ = lean_ctor_get(v_self_579_, 6);
lean_inc(v_packageMap_580_);
lean_dec_ref(v_self_579_);
v___x_581_ = ((lean_object*)(l_Lake_Workspace_findPackageByKey_x3f___closed__0));
v___x_582_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_581_, v_packageMap_580_, v_keyName_578_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_583_, lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v_a_586_, lean_object* v_x_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_baseName_589_; uint8_t v___x_590_; 
v_baseName_589_ = lean_ctor_get(v_a_586_, 1);
v___x_590_ = lean_name_eq(v_baseName_589_, v_name_583_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec_ref(v_a_586_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_584_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec_ref(v___x_584_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_a_586_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_585_);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_596_, lean_object* v___x_597_, lean_object* v___x_598_, lean_object* v_a_599_, lean_object* v_x_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_596_, v___x_597_, v___x_598_, v_a_599_, v_x_600_, v___y_601_);
lean_dec_ref(v___y_601_);
lean_dec(v_name_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_625_, lean_object* v_self_626_){
_start:
{
lean_object* v_packages_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___f_632_; size_t v_sz_633_; size_t v___x_634_; lean_object* v___x_635_; lean_object* v_fst_636_; 
v_packages_627_ = lean_ctor_get(v_self_626_, 5);
lean_inc_ref(v_packages_627_);
lean_dec_ref(v_self_626_);
v___x_628_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__9));
v___x_629_ = lean_box(0);
v___x_630_ = lean_box(0);
v___x_631_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__10));
v___f_632_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_632_, 0, v_name_625_);
lean_closure_set(v___f_632_, 1, v___x_631_);
lean_closure_set(v___f_632_, 2, v___x_630_);
v_sz_633_ = lean_array_size(v_packages_627_);
v___x_634_ = ((size_t)0ULL);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_628_, v_packages_627_, v___f_632_, v_sz_633_, v___x_634_, v___x_631_);
v_fst_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_fst_636_);
lean_dec(v___x_635_);
if (lean_obj_tag(v_fst_636_) == 0)
{
return v___x_629_;
}
else
{
lean_object* v_val_637_; 
v_val_637_ = lean_ctor_get(v_fst_636_, 0);
lean_inc(v_val_637_);
lean_dec_ref(v_fst_636_);
return v_val_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_638_, lean_object* v_self_639_){
_start:
{
lean_object* v_packageMap_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_packageMap_640_ = lean_ctor_get(v_self_639_, 6);
lean_inc(v_packageMap_640_);
lean_dec_ref(v_self_639_);
v___x_641_ = ((lean_object*)(l_Lake_Workspace_findPackageByKey_x3f___closed__0));
v___x_642_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_641_, v_packageMap_640_, v_name_638_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_646_, lean_object* v_as_647_, size_t v_sz_648_, size_t v_i_649_, lean_object* v_b_650_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_651_ == 0)
{
lean_inc_ref(v_b_650_);
return v_b_650_;
}
else
{
lean_object* v_a_652_; lean_object* v_scripts_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_652_ = lean_array_uget_borrowed(v_as_647_, v_i_649_);
v_scripts_653_ = lean_ctor_get(v_a_652_, 16);
v___x_654_ = lean_box(0);
v___x_655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_653_, v_script_646_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_654_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; size_t v___x_659_; size_t v___x_660_; 
lean_dec(v___x_655_);
v___x_658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_add(v_i_649_, v___x_659_);
v_i_649_ = v___x_660_;
v_b_650_ = v___x_658_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_662_, lean_object* v_as_663_, lean_object* v_sz_664_, lean_object* v_i_665_, lean_object* v_b_666_){
_start:
{
size_t v_sz_boxed_667_; size_t v_i_boxed_668_; lean_object* v_res_669_; 
v_sz_boxed_667_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v_i_boxed_668_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_662_, v_as_663_, v_sz_boxed_667_, v_i_boxed_668_, v_b_666_);
lean_dec_ref(v_b_666_);
lean_dec_ref(v_as_663_);
lean_dec(v_script_662_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_670_, lean_object* v_self_671_){
_start:
{
lean_object* v_packages_672_; lean_object* v___x_673_; lean_object* v___x_674_; size_t v_sz_675_; size_t v___x_676_; lean_object* v___x_677_; lean_object* v_fst_678_; 
v_packages_672_ = lean_ctor_get(v_self_671_, 5);
v___x_673_ = lean_box(0);
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_675_ = lean_array_size(v_packages_672_);
v___x_676_ = ((size_t)0ULL);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_670_, v_packages_672_, v_sz_675_, v___x_676_, v___x_674_);
v_fst_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_fst_678_);
lean_dec_ref(v___x_677_);
if (lean_obj_tag(v_fst_678_) == 0)
{
return v___x_673_;
}
else
{
lean_object* v_val_679_; 
v_val_679_ = lean_ctor_get(v_fst_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref(v_fst_678_);
return v_val_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_680_, lean_object* v_self_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lake_Workspace_findScript_x3f(v_script_680_, v_self_681_);
lean_dec_ref(v_self_681_);
lean_dec(v_script_680_);
return v_res_682_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_683_, lean_object* v_as_684_, size_t v_i_685_, size_t v_stop_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_eq(v_i_685_, v_stop_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_array_uget_borrowed(v_as_684_, v_i_685_);
v___x_689_ = l_Lake_Package_isLocalModule(v_mod_683_, v___x_688_);
if (v___x_689_ == 0)
{
size_t v___x_690_; size_t v___x_691_; 
v___x_690_ = ((size_t)1ULL);
v___x_691_ = lean_usize_add(v_i_685_, v___x_690_);
v_i_685_ = v___x_691_;
goto _start;
}
else
{
return v___x_689_;
}
}
else
{
uint8_t v___x_693_; 
v___x_693_ = 0;
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_694_, lean_object* v_as_695_, lean_object* v_i_696_, lean_object* v_stop_697_){
_start:
{
size_t v_i_boxed_698_; size_t v_stop_boxed_699_; uint8_t v_res_700_; lean_object* v_r_701_; 
v_i_boxed_698_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_stop_boxed_699_ = lean_unbox_usize(v_stop_697_);
lean_dec(v_stop_697_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_694_, v_as_695_, v_i_boxed_698_, v_stop_boxed_699_);
lean_dec_ref(v_as_695_);
lean_dec(v_mod_694_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_702_, lean_object* v_self_703_){
_start:
{
lean_object* v_packages_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_packages_704_ = lean_ctor_get(v_self_703_, 5);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_array_get_size(v_packages_704_);
v___x_707_ = lean_nat_dec_lt(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
return v___x_707_;
}
else
{
if (v___x_707_ == 0)
{
return v___x_707_;
}
else
{
size_t v___x_708_; size_t v___x_709_; uint8_t v___x_710_; 
v___x_708_ = ((size_t)0ULL);
v___x_709_ = lean_usize_of_nat(v___x_706_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_702_, v_packages_704_, v___x_708_, v___x_709_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_711_, lean_object* v_self_712_){
_start:
{
uint8_t v_res_713_; lean_object* v_r_714_; 
v_res_713_ = l_Lake_Workspace_isLocalModule(v_mod_711_, v_self_712_);
lean_dec_ref(v_self_712_);
lean_dec(v_mod_711_);
v_r_714_ = lean_box(v_res_713_);
return v_r_714_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_715_, lean_object* v_as_716_, size_t v_i_717_, size_t v_stop_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_eq(v_i_717_, v_stop_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = lean_array_uget_borrowed(v_as_716_, v_i_717_);
v___x_721_ = l_Lake_Package_isBuildableModule(v_mod_715_, v___x_720_);
if (v___x_721_ == 0)
{
size_t v___x_722_; size_t v___x_723_; 
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_717_, v___x_722_);
v_i_717_ = v___x_723_;
goto _start;
}
else
{
return v___x_721_;
}
}
else
{
uint8_t v___x_725_; 
v___x_725_ = 0;
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_726_, lean_object* v_as_727_, lean_object* v_i_728_, lean_object* v_stop_729_){
_start:
{
size_t v_i_boxed_730_; size_t v_stop_boxed_731_; uint8_t v_res_732_; lean_object* v_r_733_; 
v_i_boxed_730_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_stop_boxed_731_ = lean_unbox_usize(v_stop_729_);
lean_dec(v_stop_729_);
v_res_732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_726_, v_as_727_, v_i_boxed_730_, v_stop_boxed_731_);
lean_dec_ref(v_as_727_);
lean_dec(v_mod_726_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_734_, lean_object* v_self_735_){
_start:
{
lean_object* v_packages_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_packages_736_ = lean_ctor_get(v_self_735_, 5);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_array_get_size(v_packages_736_);
v___x_739_ = lean_nat_dec_lt(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
return v___x_739_;
}
else
{
if (v___x_739_ == 0)
{
return v___x_739_;
}
else
{
size_t v___x_740_; size_t v___x_741_; uint8_t v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_738_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_734_, v_packages_736_, v___x_740_, v___x_741_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_743_, lean_object* v_self_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Lake_Workspace_isBuildableModule(v_mod_743_, v_self_744_);
lean_dec_ref(v_self_744_);
lean_dec(v_mod_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_750_, lean_object* v_as_751_, size_t v_sz_752_, size_t v_i_753_, lean_object* v_b_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_lt(v_i_753_, v_sz_752_);
if (v___x_755_ == 0)
{
lean_dec(v_mod_750_);
lean_inc_ref(v_b_754_);
return v_b_754_;
}
else
{
lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_758_; 
v___x_756_ = lean_box(0);
v_a_757_ = lean_array_uget_borrowed(v_as_751_, v_i_753_);
lean_inc(v_a_757_);
lean_inc(v_mod_750_);
v___x_758_ = l_Lake_Package_findModule_x3f(v_mod_750_, v_a_757_);
if (lean_obj_tag(v___x_758_) == 1)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec(v_mod_750_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
lean_ctor_set(v___x_760_, 1, v___x_756_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; size_t v___x_762_; size_t v___x_763_; 
lean_dec(v___x_758_);
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_753_, v___x_762_);
v_i_753_ = v___x_763_;
v_b_754_ = v___x_761_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_765_, lean_object* v_as_766_, lean_object* v_sz_767_, lean_object* v_i_768_, lean_object* v_b_769_){
_start:
{
size_t v_sz_boxed_770_; size_t v_i_boxed_771_; lean_object* v_res_772_; 
v_sz_boxed_770_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_771_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_765_, v_as_766_, v_sz_boxed_770_, v_i_boxed_771_, v_b_769_);
lean_dec_ref(v_b_769_);
lean_dec_ref(v_as_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_773_, lean_object* v_self_774_){
_start:
{
lean_object* v_packages_775_; lean_object* v___x_776_; lean_object* v___x_777_; size_t v_sz_778_; size_t v___x_779_; lean_object* v___x_780_; lean_object* v_fst_781_; 
v_packages_775_ = lean_ctor_get(v_self_774_, 5);
v___x_776_ = lean_box(0);
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_778_ = lean_array_size(v_packages_775_);
v___x_779_ = ((size_t)0ULL);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_773_, v_packages_775_, v_sz_778_, v___x_779_, v___x_777_);
v_fst_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_fst_781_);
lean_dec_ref(v___x_780_);
if (lean_obj_tag(v_fst_781_) == 0)
{
return v___x_776_;
}
else
{
lean_object* v_val_782_; 
v_val_782_ = lean_ctor_get(v_fst_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref(v_fst_781_);
return v_val_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_783_, lean_object* v_self_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_Workspace_findModule_x3f(v_mod_783_, v_self_784_);
lean_dec_ref(v_self_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_786_, lean_object* v_as_787_, size_t v_i_788_, size_t v_stop_789_, lean_object* v_b_790_){
_start:
{
lean_object* v___y_792_; uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_eq(v_i_788_, v_stop_789_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_array_uget_borrowed(v_as_787_, v_i_788_);
lean_inc(v___x_797_);
lean_inc(v_mod_786_);
v___x_798_ = l_Lake_Package_findModule_x3f(v_mod_786_, v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
v___y_792_ = v_b_790_;
goto v___jp_791_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_800_; 
v_val_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = lean_array_push(v_b_790_, v_val_799_);
v___y_792_ = v___x_800_;
goto v___jp_791_;
}
}
else
{
lean_dec(v_mod_786_);
return v_b_790_;
}
v___jp_791_:
{
size_t v___x_793_; size_t v___x_794_; 
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_add(v_i_788_, v___x_793_);
v_i_788_ = v___x_794_;
v_b_790_ = v___y_792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_801_, lean_object* v_as_802_, lean_object* v_i_803_, lean_object* v_stop_804_, lean_object* v_b_805_){
_start:
{
size_t v_i_boxed_806_; size_t v_stop_boxed_807_; lean_object* v_res_808_; 
v_i_boxed_806_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_stop_boxed_807_ = lean_unbox_usize(v_stop_804_);
lean_dec(v_stop_804_);
v_res_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_801_, v_as_802_, v_i_boxed_806_, v_stop_boxed_807_, v_b_805_);
lean_dec_ref(v_as_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_811_, lean_object* v_as_812_, lean_object* v_start_813_, lean_object* v_stop_814_){
_start:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_816_ = lean_nat_dec_lt(v_start_813_, v_stop_814_);
if (v___x_816_ == 0)
{
lean_dec(v_mod_811_);
return v___x_815_;
}
else
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = lean_array_get_size(v_as_812_);
v___x_818_ = lean_nat_dec_le(v_stop_814_, v___x_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = lean_nat_dec_lt(v_start_813_, v___x_817_);
if (v___x_819_ == 0)
{
lean_dec(v_mod_811_);
return v___x_815_;
}
else
{
size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_usize_of_nat(v_start_813_);
v___x_821_ = lean_usize_of_nat(v___x_817_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_811_, v_as_812_, v___x_820_, v___x_821_, v___x_815_);
return v___x_822_;
}
}
else
{
size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_usize_of_nat(v_start_813_);
v___x_824_ = lean_usize_of_nat(v_stop_814_);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_811_, v_as_812_, v___x_823_, v___x_824_, v___x_815_);
return v___x_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_826_, lean_object* v_as_827_, lean_object* v_start_828_, lean_object* v_stop_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_826_, v_as_827_, v_start_828_, v_stop_829_);
lean_dec(v_stop_829_);
lean_dec(v_start_828_);
lean_dec_ref(v_as_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_831_, lean_object* v_self_832_){
_start:
{
lean_object* v_packages_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_packages_833_ = lean_ctor_get(v_self_832_, 5);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_array_get_size(v_packages_833_);
v___x_836_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_831_, v_packages_833_, v___x_834_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_837_, lean_object* v_self_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_Workspace_findModules(v_mod_837_, v_self_838_);
lean_dec_ref(v_self_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_840_, lean_object* v_as_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_845_ == 0)
{
lean_dec(v_mod_840_);
lean_inc_ref(v_b_844_);
return v_b_844_;
}
else
{
lean_object* v___x_846_; lean_object* v_a_847_; lean_object* v___x_848_; 
v___x_846_ = lean_box(0);
v_a_847_ = lean_array_uget_borrowed(v_as_841_, v_i_843_);
lean_inc(v_a_847_);
lean_inc(v_mod_840_);
v___x_848_ = l_Lake_Package_findTargetModule_x3f(v_mod_840_, v_a_847_);
if (lean_obj_tag(v___x_848_) == 1)
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_mod_840_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
lean_ctor_set(v___x_850_, 1, v___x_846_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; size_t v___x_852_; size_t v___x_853_; 
lean_dec(v___x_848_);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_852_ = ((size_t)1ULL);
v___x_853_ = lean_usize_add(v_i_843_, v___x_852_);
v_i_843_ = v___x_853_;
v_b_844_ = v___x_851_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_855_, lean_object* v_as_856_, lean_object* v_sz_857_, lean_object* v_i_858_, lean_object* v_b_859_){
_start:
{
size_t v_sz_boxed_860_; size_t v_i_boxed_861_; lean_object* v_res_862_; 
v_sz_boxed_860_ = lean_unbox_usize(v_sz_857_);
lean_dec(v_sz_857_);
v_i_boxed_861_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_855_, v_as_856_, v_sz_boxed_860_, v_i_boxed_861_, v_b_859_);
lean_dec_ref(v_b_859_);
lean_dec_ref(v_as_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_863_, lean_object* v_self_864_){
_start:
{
lean_object* v_packages_865_; lean_object* v___x_866_; lean_object* v___x_867_; size_t v_sz_868_; size_t v___x_869_; lean_object* v___x_870_; lean_object* v_fst_871_; 
v_packages_865_ = lean_ctor_get(v_self_864_, 5);
v___x_866_ = lean_box(0);
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_868_ = lean_array_size(v_packages_865_);
v___x_869_ = ((size_t)0ULL);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_863_, v_packages_865_, v_sz_868_, v___x_869_, v___x_867_);
v_fst_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_fst_871_);
lean_dec_ref(v___x_870_);
if (lean_obj_tag(v_fst_871_) == 0)
{
return v___x_866_;
}
else
{
lean_object* v_val_872_; 
v_val_872_ = lean_ctor_get(v_fst_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref(v_fst_871_);
return v_val_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_873_, lean_object* v_self_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_873_, v_self_874_);
lean_dec_ref(v_self_874_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_876_, lean_object* v_as_877_, size_t v_sz_878_, size_t v_i_879_, lean_object* v_b_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_881_ == 0)
{
lean_dec_ref(v_path_876_);
lean_inc_ref(v_b_880_);
return v_b_880_;
}
else
{
lean_object* v___x_882_; lean_object* v_a_883_; lean_object* v___x_884_; 
v___x_882_ = lean_box(0);
v_a_883_ = lean_array_uget_borrowed(v_as_877_, v_i_879_);
lean_inc(v_a_883_);
lean_inc_ref(v_path_876_);
v___x_884_ = l_Lake_Package_findModuleBySrc_x3f(v_path_876_, v_a_883_);
if (lean_obj_tag(v___x_884_) == 1)
{
lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec_ref(v_path_876_);
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_882_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; 
lean_dec(v___x_884_);
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_add(v_i_879_, v___x_888_);
v_i_879_ = v___x_889_;
v_b_880_ = v___x_887_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_891_, lean_object* v_as_892_, lean_object* v_sz_893_, lean_object* v_i_894_, lean_object* v_b_895_){
_start:
{
size_t v_sz_boxed_896_; size_t v_i_boxed_897_; lean_object* v_res_898_; 
v_sz_boxed_896_ = lean_unbox_usize(v_sz_893_);
lean_dec(v_sz_893_);
v_i_boxed_897_ = lean_unbox_usize(v_i_894_);
lean_dec(v_i_894_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_891_, v_as_892_, v_sz_boxed_896_, v_i_boxed_897_, v_b_895_);
lean_dec_ref(v_b_895_);
lean_dec_ref(v_as_892_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_899_, lean_object* v_self_900_){
_start:
{
lean_object* v_packages_901_; lean_object* v___x_902_; lean_object* v___x_903_; size_t v_sz_904_; size_t v___x_905_; lean_object* v___x_906_; lean_object* v_fst_907_; 
v_packages_901_ = lean_ctor_get(v_self_900_, 5);
v___x_902_ = lean_box(0);
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_904_ = lean_array_size(v_packages_901_);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_899_, v_packages_901_, v_sz_904_, v___x_905_, v___x_903_);
v_fst_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_fst_907_);
lean_dec_ref(v___x_906_);
if (lean_obj_tag(v_fst_907_) == 0)
{
return v___x_902_;
}
else
{
lean_object* v_val_908_; 
v_val_908_ = lean_ctor_get(v_fst_907_, 0);
lean_inc(v_val_908_);
lean_dec_ref(v_fst_907_);
return v_val_908_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_909_, lean_object* v_self_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_909_, v_self_910_);
lean_dec_ref(v_self_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_915_, lean_object* v_as_916_, size_t v_sz_917_, size_t v_i_918_, lean_object* v_b_919_){
_start:
{
lean_object* v_a_921_; uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_lt(v_i_918_, v_sz_917_);
if (v___x_925_ == 0)
{
lean_inc_ref(v_b_919_);
return v_b_919_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_a_928_; lean_object* v___x_929_; 
v___x_926_ = lean_box(0);
v___x_927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_928_ = lean_array_uget_borrowed(v_as_916_, v_i_918_);
v___x_929_ = l_Lake_Package_findTargetDecl_x3f(v_name_915_, v_a_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
v_a_921_ = v___x_927_;
goto v___jp_920_;
}
else
{
lean_object* v_val_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_945_; 
v_val_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_945_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_val_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_945_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_name_934_; lean_object* v_kind_935_; lean_object* v_config_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_name_934_ = lean_ctor_get(v_val_930_, 1);
lean_inc(v_name_934_);
v_kind_935_ = lean_ctor_get(v_val_930_, 2);
lean_inc(v_kind_935_);
v_config_936_ = lean_ctor_get(v_val_930_, 3);
lean_inc(v_config_936_);
lean_dec(v_val_930_);
v___x_937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_938_ = lean_name_eq(v_kind_935_, v___x_937_);
lean_dec(v_kind_935_);
if (v___x_938_ == 0)
{
lean_dec(v_config_936_);
lean_dec(v_name_934_);
lean_del_object(v___x_932_);
v_a_921_ = v___x_927_;
goto v___jp_920_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_941_; 
lean_inc(v_a_928_);
v___x_939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_939_, 0, v_a_928_);
lean_ctor_set(v___x_939_, 1, v_name_934_);
lean_ctor_set(v___x_939_, 2, v_config_936_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_939_);
v___x_941_ = v___x_932_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_944_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_926_);
return v___x_943_;
}
}
}
}
}
v___jp_920_:
{
size_t v___x_922_; size_t v___x_923_; 
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_918_, v___x_922_);
v_i_918_ = v___x_923_;
v_b_919_ = v_a_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_946_, lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_){
_start:
{
size_t v_sz_boxed_951_; size_t v_i_boxed_952_; lean_object* v_res_953_; 
v_sz_boxed_951_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_952_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_946_, v_as_947_, v_sz_boxed_951_, v_i_boxed_952_, v_b_950_);
lean_dec_ref(v_b_950_);
lean_dec_ref(v_as_947_);
lean_dec(v_name_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_954_, lean_object* v_self_955_){
_start:
{
lean_object* v_packages_956_; lean_object* v___x_957_; lean_object* v___x_958_; size_t v_sz_959_; size_t v___x_960_; lean_object* v___x_961_; lean_object* v_fst_962_; 
v_packages_956_ = lean_ctor_get(v_self_955_, 5);
v___x_957_ = lean_box(0);
v___x_958_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_959_ = lean_array_size(v_packages_956_);
v___x_960_ = ((size_t)0ULL);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_954_, v_packages_956_, v_sz_959_, v___x_960_, v___x_958_);
v_fst_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_fst_962_);
lean_dec_ref(v___x_961_);
if (lean_obj_tag(v_fst_962_) == 0)
{
return v___x_957_;
}
else
{
lean_object* v_val_963_; 
v_val_963_ = lean_ctor_get(v_fst_962_, 0);
lean_inc(v_val_963_);
lean_dec_ref(v_fst_962_);
return v_val_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_964_, lean_object* v_self_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lake_Workspace_findLeanLib_x3f(v_name_964_, v_self_965_);
lean_dec_ref(v_self_965_);
lean_dec(v_name_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_967_, lean_object* v_as_968_, size_t v_sz_969_, size_t v_i_970_, lean_object* v_b_971_){
_start:
{
lean_object* v_a_973_; uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_lt(v_i_970_, v_sz_969_);
if (v___x_977_ == 0)
{
lean_inc_ref(v_b_971_);
return v_b_971_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_981_; 
v___x_978_ = lean_box(0);
v___x_979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_980_ = lean_array_uget_borrowed(v_as_968_, v_i_970_);
v___x_981_ = l_Lake_Package_findTargetDecl_x3f(v_name_967_, v_a_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
v_a_973_ = v___x_979_;
goto v___jp_972_;
}
else
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_997_; 
v_val_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_997_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_997_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_997_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_name_986_; lean_object* v_kind_987_; lean_object* v_config_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v_name_986_ = lean_ctor_get(v_val_982_, 1);
lean_inc(v_name_986_);
v_kind_987_ = lean_ctor_get(v_val_982_, 2);
lean_inc(v_kind_987_);
v_config_988_ = lean_ctor_get(v_val_982_, 3);
lean_inc(v_config_988_);
lean_dec(v_val_982_);
v___x_989_ = l_Lake_LeanExe_keyword;
v___x_990_ = lean_name_eq(v_kind_987_, v___x_989_);
lean_dec(v_kind_987_);
if (v___x_990_ == 0)
{
lean_dec(v_config_988_);
lean_dec(v_name_986_);
lean_del_object(v___x_984_);
v_a_973_ = v___x_979_;
goto v___jp_972_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_inc(v_a_980_);
v___x_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_991_, 0, v_a_980_);
lean_ctor_set(v___x_991_, 1, v_name_986_);
lean_ctor_set(v___x_991_, 2, v_config_988_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_991_);
v___x_993_ = v___x_984_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_996_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_978_);
return v___x_995_;
}
}
}
}
}
v___jp_972_:
{
size_t v___x_974_; size_t v___x_975_; 
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_add(v_i_970_, v___x_974_);
v_i_970_ = v___x_975_;
v_b_971_ = v_a_973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_998_, lean_object* v_as_999_, lean_object* v_sz_1000_, lean_object* v_i_1001_, lean_object* v_b_1002_){
_start:
{
size_t v_sz_boxed_1003_; size_t v_i_boxed_1004_; lean_object* v_res_1005_; 
v_sz_boxed_1003_ = lean_unbox_usize(v_sz_1000_);
lean_dec(v_sz_1000_);
v_i_boxed_1004_ = lean_unbox_usize(v_i_1001_);
lean_dec(v_i_1001_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_998_, v_as_999_, v_sz_boxed_1003_, v_i_boxed_1004_, v_b_1002_);
lean_dec_ref(v_b_1002_);
lean_dec_ref(v_as_999_);
lean_dec(v_name_998_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_1006_, lean_object* v_self_1007_){
_start:
{
lean_object* v_packages_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; size_t v_sz_1011_; size_t v___x_1012_; lean_object* v___x_1013_; lean_object* v_fst_1014_; 
v_packages_1008_ = lean_ctor_get(v_self_1007_, 5);
v___x_1009_ = lean_box(0);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_1011_ = lean_array_size(v_packages_1008_);
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_1006_, v_packages_1008_, v_sz_1011_, v___x_1012_, v___x_1010_);
v_fst_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_fst_1014_);
lean_dec_ref(v___x_1013_);
if (lean_obj_tag(v_fst_1014_) == 0)
{
return v___x_1009_;
}
else
{
lean_object* v_val_1015_; 
v_val_1015_ = lean_ctor_get(v_fst_1014_, 0);
lean_inc(v_val_1015_);
lean_dec_ref(v_fst_1014_);
return v_val_1015_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_1016_, lean_object* v_self_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lake_Workspace_findLeanExe_x3f(v_name_1016_, v_self_1017_);
lean_dec_ref(v_self_1017_);
lean_dec(v_name_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_1019_, lean_object* v_as_1020_, size_t v_sz_1021_, size_t v_i_1022_, lean_object* v_b_1023_){
_start:
{
lean_object* v_a_1025_; uint8_t v___x_1029_; 
v___x_1029_ = lean_usize_dec_lt(v_i_1022_, v_sz_1021_);
if (v___x_1029_ == 0)
{
lean_inc_ref(v_b_1023_);
return v_b_1023_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_a_1032_; lean_object* v___x_1033_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_1032_ = lean_array_uget_borrowed(v_as_1020_, v_i_1022_);
v___x_1033_ = l_Lake_Package_findTargetDecl_x3f(v_name_1019_, v_a_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
v_a_1025_ = v___x_1031_;
goto v___jp_1024_;
}
else
{
lean_object* v_val_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1049_; 
v_val_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1049_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_val_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1049_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_name_1038_; lean_object* v_kind_1039_; lean_object* v_config_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_name_1038_ = lean_ctor_get(v_val_1034_, 1);
lean_inc(v_name_1038_);
v_kind_1039_ = lean_ctor_get(v_val_1034_, 2);
lean_inc(v_kind_1039_);
v_config_1040_ = lean_ctor_get(v_val_1034_, 3);
lean_inc(v_config_1040_);
lean_dec(v_val_1034_);
v___x_1041_ = l_Lake_ExternLib_keyword;
v___x_1042_ = lean_name_eq(v_kind_1039_, v___x_1041_);
lean_dec(v_kind_1039_);
if (v___x_1042_ == 0)
{
lean_dec(v_config_1040_);
lean_dec(v_name_1038_);
lean_del_object(v___x_1036_);
v_a_1025_ = v___x_1031_;
goto v___jp_1024_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_inc(v_a_1032_);
v___x_1043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1043_, 0, v_a_1032_);
lean_ctor_set(v___x_1043_, 1, v_name_1038_);
lean_ctor_set(v___x_1043_, 2, v_config_1040_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1043_);
v___x_1045_ = v___x_1036_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1030_);
return v___x_1047_;
}
}
}
}
}
v___jp_1024_:
{
size_t v___x_1026_; size_t v___x_1027_; 
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1022_, v___x_1026_);
v_i_1022_ = v___x_1027_;
v_b_1023_ = v_a_1025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_1050_, lean_object* v_as_1051_, lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_b_1054_){
_start:
{
size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_1050_, v_as_1051_, v_sz_boxed_1055_, v_i_boxed_1056_, v_b_1054_);
lean_dec_ref(v_b_1054_);
lean_dec_ref(v_as_1051_);
lean_dec(v_name_1050_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_1058_, lean_object* v_self_1059_){
_start:
{
lean_object* v_packages_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; size_t v_sz_1063_; size_t v___x_1064_; lean_object* v___x_1065_; lean_object* v_fst_1066_; 
v_packages_1060_ = lean_ctor_get(v_self_1059_, 5);
v___x_1061_ = lean_box(0);
v___x_1062_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_1063_ = lean_array_size(v_packages_1060_);
v___x_1064_ = ((size_t)0ULL);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_1058_, v_packages_1060_, v_sz_1063_, v___x_1064_, v___x_1062_);
v_fst_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_fst_1066_);
lean_dec_ref(v___x_1065_);
if (lean_obj_tag(v_fst_1066_) == 0)
{
return v___x_1061_;
}
else
{
lean_object* v_val_1067_; 
v_val_1067_ = lean_ctor_get(v_fst_1066_, 0);
lean_inc(v_val_1067_);
lean_dec_ref(v_fst_1066_);
return v_val_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_1068_, lean_object* v_self_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lake_Workspace_findExternLib_x3f(v_name_1068_, v_self_1069_);
lean_dec_ref(v_self_1069_);
lean_dec(v_name_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_1071_, lean_object* v_f_1072_){
_start:
{
if (lean_obj_tag(v_a_1071_) == 0)
{
lean_object* v___x_1073_; 
lean_dec(v_f_1072_);
v___x_1073_ = lean_box(0);
return v___x_1073_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_val_1074_ = lean_ctor_get(v_a_1071_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_a_1071_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1076_ = v_a_1071_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_val_1074_);
lean_dec(v_a_1071_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_apply_1(v_f_1072_, v_val_1074_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_a_1085_, lean_object* v_f_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_1085_, v_f_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_a_1088_);
lean_ctor_set(v___x_1090_, 1, v_x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_1094_, lean_object* v_as_1095_, size_t v_sz_1096_, size_t v_i_1097_, lean_object* v_b_1098_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = lean_usize_dec_lt(v_i_1097_, v_sz_1096_);
if (v___x_1099_ == 0)
{
lean_inc_ref(v_b_1098_);
return v_b_1098_;
}
else
{
lean_object* v___x_1100_; lean_object* v_a_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1100_ = lean_box(0);
v_a_1101_ = lean_array_uget_borrowed(v_as_1095_, v_i_1097_);
lean_inc(v_a_1101_);
v___f_1102_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_1102_, 0, v_a_1101_);
v___x_1103_ = l_Lake_Package_findTargetConfig_x3f(v_name_1094_, v_a_1101_);
v___x_1104_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_1103_, v___f_1102_);
if (lean_obj_tag(v___x_1104_) == 1)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1100_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; 
lean_dec(v___x_1104_);
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1097_, v___x_1108_);
v_i_1097_ = v___x_1109_;
v_b_1098_ = v___x_1107_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_1111_, lean_object* v_as_1112_, lean_object* v_sz_1113_, lean_object* v_i_1114_, lean_object* v_b_1115_){
_start:
{
size_t v_sz_boxed_1116_; size_t v_i_boxed_1117_; lean_object* v_res_1118_; 
v_sz_boxed_1116_ = lean_unbox_usize(v_sz_1113_);
lean_dec(v_sz_1113_);
v_i_boxed_1117_ = lean_unbox_usize(v_i_1114_);
lean_dec(v_i_1114_);
v_res_1118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_1111_, v_as_1112_, v_sz_boxed_1116_, v_i_boxed_1117_, v_b_1115_);
lean_dec_ref(v_b_1115_);
lean_dec_ref(v_as_1112_);
lean_dec(v_name_1111_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_1119_, lean_object* v_self_1120_){
_start:
{
lean_object* v_packages_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; size_t v_sz_1124_; size_t v___x_1125_; lean_object* v___x_1126_; lean_object* v_fst_1127_; 
v_packages_1121_ = lean_ctor_get(v_self_1120_, 5);
v___x_1122_ = lean_box(0);
v___x_1123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_1124_ = lean_array_size(v_packages_1121_);
v___x_1125_ = ((size_t)0ULL);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_1119_, v_packages_1121_, v_sz_1124_, v___x_1125_, v___x_1123_);
v_fst_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_fst_1127_);
lean_dec_ref(v___x_1126_);
if (lean_obj_tag(v_fst_1127_) == 0)
{
return v___x_1122_;
}
else
{
lean_object* v_val_1128_; 
v_val_1128_ = lean_ctor_get(v_fst_1127_, 0);
lean_inc(v_val_1128_);
lean_dec_ref(v_fst_1127_);
return v_val_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_1129_, lean_object* v_self_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_1129_, v_self_1130_);
lean_dec_ref(v_self_1130_);
lean_dec(v_name_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_1132_, lean_object* v_x_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1132_);
lean_ctor_set(v___x_1134_, 1, v_x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_1135_, lean_object* v_as_1136_, size_t v_sz_1137_, size_t v_i_1138_, lean_object* v_b_1139_){
_start:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_usize_dec_lt(v_i_1138_, v_sz_1137_);
if (v___x_1140_ == 0)
{
lean_inc_ref(v_b_1139_);
return v_b_1139_;
}
else
{
lean_object* v___x_1141_; lean_object* v_a_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1141_ = lean_box(0);
v_a_1142_ = lean_array_uget_borrowed(v_as_1136_, v_i_1138_);
lean_inc(v_a_1142_);
v___f_1143_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1143_, 0, v_a_1142_);
v___x_1144_ = l_Lake_Package_findTargetDecl_x3f(v_name_1135_, v_a_1142_);
v___x_1145_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_1144_, v___f_1143_);
if (lean_obj_tag(v___x_1145_) == 1)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1141_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; 
lean_dec(v___x_1145_);
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1138_, v___x_1149_);
v_i_1138_ = v___x_1150_;
v_b_1139_ = v___x_1148_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_1152_, lean_object* v_as_1153_, lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_b_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_1152_, v_as_1153_, v_sz_boxed_1157_, v_i_boxed_1158_, v_b_1156_);
lean_dec_ref(v_b_1156_);
lean_dec_ref(v_as_1153_);
lean_dec(v_name_1152_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_1160_, lean_object* v_self_1161_){
_start:
{
lean_object* v_packages_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; size_t v_sz_1165_; size_t v___x_1166_; lean_object* v___x_1167_; lean_object* v_fst_1168_; 
v_packages_1162_ = lean_ctor_get(v_self_1161_, 5);
v___x_1163_ = lean_box(0);
v___x_1164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_1165_ = lean_array_size(v_packages_1162_);
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_1160_, v_packages_1162_, v_sz_1165_, v___x_1166_, v___x_1164_);
v_fst_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_fst_1168_);
lean_dec_ref(v___x_1167_);
if (lean_obj_tag(v_fst_1168_) == 0)
{
return v___x_1163_;
}
else
{
lean_object* v_val_1169_; 
v_val_1169_ = lean_ctor_get(v_fst_1168_, 0);
lean_inc(v_val_1169_);
lean_dec_ref(v_fst_1168_);
return v_val_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_1170_, lean_object* v_self_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_1170_, v_self_1171_);
lean_dec_ref(v_self_1171_);
lean_dec(v_name_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_1173_, lean_object* v_cfg_1174_, lean_object* v_self_1175_){
_start:
{
lean_object* v_root_1176_; lean_object* v_lakeEnv_1177_; lean_object* v_lakeConfig_1178_; lean_object* v_lakeCache_1179_; lean_object* v_lakeArgs_x3f_1180_; lean_object* v_packages_1181_; lean_object* v_packageMap_1182_; lean_object* v_facetConfigs_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
v_root_1176_ = lean_ctor_get(v_self_1175_, 0);
v_lakeEnv_1177_ = lean_ctor_get(v_self_1175_, 1);
v_lakeConfig_1178_ = lean_ctor_get(v_self_1175_, 2);
v_lakeCache_1179_ = lean_ctor_get(v_self_1175_, 3);
v_lakeArgs_x3f_1180_ = lean_ctor_get(v_self_1175_, 4);
v_packages_1181_ = lean_ctor_get(v_self_1175_, 5);
v_packageMap_1182_ = lean_ctor_get(v_self_1175_, 6);
v_facetConfigs_1183_ = lean_ctor_get(v_self_1175_, 7);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_self_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v_self_1175_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_facetConfigs_1183_);
lean_inc(v_packageMap_1182_);
lean_inc(v_packages_1181_);
lean_inc(v_lakeArgs_x3f_1180_);
lean_inc(v_lakeCache_1179_);
lean_inc(v_lakeConfig_1178_);
lean_inc(v_lakeEnv_1177_);
lean_inc(v_root_1176_);
lean_dec(v_self_1175_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_name_1173_, v_cfg_1174_, v_facetConfigs_1183_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 7, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_root_1176_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_lakeEnv_1177_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_lakeConfig_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_lakeCache_1179_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_lakeArgs_x3f_1180_);
lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_packages_1181_);
lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_packageMap_1182_);
lean_ctor_set(v_reuseFailAlloc_1190_, 7, v___x_1187_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(lean_object* v_t_1192_, lean_object* v_k_1193_){
_start:
{
if (lean_obj_tag(v_t_1192_) == 0)
{
lean_object* v_k_1194_; lean_object* v_v_1195_; lean_object* v_l_1196_; lean_object* v_r_1197_; uint8_t v___x_1198_; 
v_k_1194_ = lean_ctor_get(v_t_1192_, 1);
v_v_1195_ = lean_ctor_get(v_t_1192_, 2);
v_l_1196_ = lean_ctor_get(v_t_1192_, 3);
v_r_1197_ = lean_ctor_get(v_t_1192_, 4);
v___x_1198_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1193_, v_k_1194_);
switch(v___x_1198_)
{
case 0:
{
v_t_1192_ = v_l_1196_;
goto _start;
}
case 1:
{
lean_object* v___x_1200_; 
lean_inc(v_v_1195_);
v___x_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1200_, 0, v_v_1195_);
return v___x_1200_;
}
default: 
{
v_t_1192_ = v_r_1197_;
goto _start;
}
}
}
else
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg___boxed(lean_object* v_t_1203_, lean_object* v_k_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(v_t_1203_, v_k_1204_);
lean_dec(v_k_1204_);
lean_dec(v_t_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_1206_, lean_object* v_self_1207_){
_start:
{
lean_object* v_facetConfigs_1208_; lean_object* v___x_1209_; 
v_facetConfigs_1208_ = lean_ctor_get(v_self_1207_, 7);
v___x_1209_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(v_facetConfigs_1208_, v_name_1206_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_1210_, lean_object* v_self_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1210_, v_self_1211_);
lean_dec_ref(v_self_1211_);
lean_dec(v_name_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0(lean_object* v_00_u03b2_1213_, lean_object* v_inst_1214_, lean_object* v_t_1215_, lean_object* v_k_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(v_t_1215_, v_k_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___boxed(lean_object* v_00_u03b2_1218_, lean_object* v_inst_1219_, lean_object* v_t_1220_, lean_object* v_k_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0(v_00_u03b2_1218_, v_inst_1219_, v_t_1220_, v_k_1221_);
lean_dec(v_k_1221_);
lean_dec(v_t_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_1223_, lean_object* v_cfg_1224_, lean_object* v_self_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lake_Workspace_addFacetConfig(v_name_1223_, v_cfg_1224_, v_self_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_1227_, lean_object* v_self_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1227_, v_self_1228_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_box(0);
return v___x_1230_;
}
else
{
lean_object* v_val_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_val_1231_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1231_);
lean_dec_ref(v___x_1229_);
v___x_1232_ = l_Lake_Module_keyword;
v___x_1233_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1232_, v_val_1231_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1234_, lean_object* v_self_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1234_, v_self_1235_);
lean_dec_ref(v_self_1235_);
lean_dec(v_name_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1237_, lean_object* v_cfg_1238_, lean_object* v_self_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lake_Workspace_addFacetConfig(v_name_1237_, v_cfg_1238_, v_self_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1241_, lean_object* v_self_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1241_, v_self_1242_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
else
{
lean_object* v_val_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_val_1245_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v___x_1243_);
v___x_1246_ = l_Lake_Package_keyword;
v___x_1247_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1246_, v_val_1245_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1248_, lean_object* v_self_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1248_, v_self_1249_);
lean_dec_ref(v_self_1249_);
lean_dec(v_name_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1251_, lean_object* v_cfg_1252_, lean_object* v_self_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lake_Workspace_addFacetConfig(v_name_1251_, v_cfg_1252_, v_self_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1255_, lean_object* v_self_1256_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1255_, v_self_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_box(0);
return v___x_1258_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_val_1259_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_val_1259_);
lean_dec_ref(v___x_1257_);
v___x_1260_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1261_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1260_, v_val_1259_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1262_, lean_object* v_self_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1262_, v_self_1263_);
lean_dec_ref(v_self_1263_);
lean_dec(v_name_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1265_, size_t v_i_1266_, size_t v_stop_1267_, lean_object* v_b_1268_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_usize_dec_eq(v_i_1266_, v_stop_1267_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v_config_1271_; lean_object* v_dir_1272_; lean_object* v_buildDir_1273_; lean_object* v_binDir_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; 
v___x_1270_ = lean_array_uget_borrowed(v_as_1265_, v_i_1266_);
v_config_1271_ = lean_ctor_get(v___x_1270_, 6);
v_dir_1272_ = lean_ctor_get(v___x_1270_, 4);
v_buildDir_1273_ = lean_ctor_get(v_config_1271_, 5);
v_binDir_1274_ = lean_ctor_get(v_config_1271_, 8);
lean_inc_ref(v_buildDir_1273_);
v___x_1275_ = l_System_FilePath_normalize(v_buildDir_1273_);
lean_inc_ref(v_dir_1272_);
v___x_1276_ = l_Lake_joinRelative(v_dir_1272_, v___x_1275_);
lean_inc_ref(v_binDir_1274_);
v___x_1277_ = l_System_FilePath_normalize(v_binDir_1274_);
v___x_1278_ = l_Lake_joinRelative(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
lean_ctor_set(v___x_1279_, 1, v_b_1268_);
v___x_1280_ = ((size_t)1ULL);
v___x_1281_ = lean_usize_add(v_i_1266_, v___x_1280_);
v_i_1266_ = v___x_1281_;
v_b_1268_ = v___x_1279_;
goto _start;
}
else
{
return v_b_1268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1283_, lean_object* v_i_1284_, lean_object* v_stop_1285_, lean_object* v_b_1286_){
_start:
{
size_t v_i_boxed_1287_; size_t v_stop_boxed_1288_; lean_object* v_res_1289_; 
v_i_boxed_1287_ = lean_unbox_usize(v_i_1284_);
lean_dec(v_i_1284_);
v_stop_boxed_1288_ = lean_unbox_usize(v_stop_1285_);
lean_dec(v_stop_1285_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1283_, v_i_boxed_1287_, v_stop_boxed_1288_, v_b_1286_);
lean_dec_ref(v_as_1283_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1290_){
_start:
{
lean_object* v_packages_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_packages_1291_ = lean_ctor_get(v_self_1290_, 5);
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_array_get_size(v_packages_1291_);
v___x_1295_ = lean_nat_dec_lt(v___x_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
return v___x_1292_;
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_nat_dec_le(v___x_1294_, v___x_1294_);
if (v___x_1296_ == 0)
{
if (v___x_1295_ == 0)
{
return v___x_1292_;
}
else
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_of_nat(v___x_1294_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1291_, v___x_1297_, v___x_1298_, v___x_1292_);
return v___x_1299_;
}
}
else
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = lean_usize_of_nat(v___x_1294_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1291_, v___x_1300_, v___x_1301_, v___x_1292_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lake_Workspace_binPath(v_self_1303_);
lean_dec_ref(v_self_1303_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1305_, size_t v_i_1306_, size_t v_stop_1307_, lean_object* v_b_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_usize_dec_eq(v_i_1306_, v_stop_1307_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v_config_1311_; lean_object* v_dir_1312_; lean_object* v_buildDir_1313_; lean_object* v_leanLibDir_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; 
v___x_1310_ = lean_array_uget_borrowed(v_as_1305_, v_i_1306_);
v_config_1311_ = lean_ctor_get(v___x_1310_, 6);
v_dir_1312_ = lean_ctor_get(v___x_1310_, 4);
v_buildDir_1313_ = lean_ctor_get(v_config_1311_, 5);
v_leanLibDir_1314_ = lean_ctor_get(v_config_1311_, 6);
lean_inc_ref(v_buildDir_1313_);
v___x_1315_ = l_System_FilePath_normalize(v_buildDir_1313_);
lean_inc_ref(v_dir_1312_);
v___x_1316_ = l_Lake_joinRelative(v_dir_1312_, v___x_1315_);
lean_inc_ref(v_leanLibDir_1314_);
v___x_1317_ = l_System_FilePath_normalize(v_leanLibDir_1314_);
v___x_1318_ = l_Lake_joinRelative(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v_b_1308_);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1306_, v___x_1320_);
v_i_1306_ = v___x_1321_;
v_b_1308_ = v___x_1319_;
goto _start;
}
else
{
return v_b_1308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1323_, lean_object* v_i_1324_, lean_object* v_stop_1325_, lean_object* v_b_1326_){
_start:
{
size_t v_i_boxed_1327_; size_t v_stop_boxed_1328_; lean_object* v_res_1329_; 
v_i_boxed_1327_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_stop_boxed_1328_ = lean_unbox_usize(v_stop_1325_);
lean_dec(v_stop_1325_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1323_, v_i_boxed_1327_, v_stop_boxed_1328_, v_b_1326_);
lean_dec_ref(v_as_1323_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1330_){
_start:
{
lean_object* v_packages_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_packages_1331_ = lean_ctor_get(v_self_1330_, 5);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_array_get_size(v_packages_1331_);
v___x_1335_ = lean_nat_dec_lt(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
return v___x_1332_;
}
else
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_nat_dec_le(v___x_1334_, v___x_1334_);
if (v___x_1336_ == 0)
{
if (v___x_1335_ == 0)
{
return v___x_1332_;
}
else
{
size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = lean_usize_of_nat(v___x_1334_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1331_, v___x_1337_, v___x_1338_, v___x_1332_);
return v___x_1339_;
}
}
else
{
size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = lean_usize_of_nat(v___x_1334_);
v___x_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1331_, v___x_1340_, v___x_1341_, v___x_1332_);
return v___x_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* v_self_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lake_Workspace_leanPath(v_self_1343_);
lean_dec_ref(v_self_1343_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1345_, lean_object* v_as_1346_, size_t v_i_1347_, size_t v_stop_1348_, lean_object* v_b_1349_){
_start:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_usize_dec_eq(v_i_1347_, v_stop_1348_);
if (v___x_1350_ == 0)
{
size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; lean_object* v_kind_1354_; lean_object* v_config_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_sub(v_i_1347_, v___x_1351_);
v___x_1353_ = lean_array_uget_borrowed(v_as_1346_, v___x_1352_);
v_kind_1354_ = lean_ctor_get(v___x_1353_, 2);
v_config_1355_ = lean_ctor_get(v___x_1353_, 3);
v___x_1356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1357_ = lean_name_eq(v_kind_1354_, v___x_1356_);
if (v___x_1357_ == 0)
{
v_i_1347_ = v___x_1352_;
goto _start;
}
else
{
lean_object* v_config_1359_; lean_object* v_dir_1360_; lean_object* v_srcDir_1361_; lean_object* v_srcDir_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_config_1359_ = lean_ctor_get(v_x2_1345_, 6);
v_dir_1360_ = lean_ctor_get(v_x2_1345_, 4);
v_srcDir_1361_ = lean_ctor_get(v_config_1359_, 4);
v_srcDir_1362_ = lean_ctor_get(v_config_1355_, 1);
lean_inc_ref(v_srcDir_1361_);
v___x_1363_ = l_System_FilePath_normalize(v_srcDir_1361_);
lean_inc_ref(v_dir_1360_);
v___x_1364_ = l_Lake_joinRelative(v_dir_1360_, v___x_1363_);
lean_inc_ref(v_srcDir_1362_);
v___x_1365_ = l_Lake_joinRelative(v___x_1364_, v_srcDir_1362_);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v_b_1349_);
v_i_1347_ = v___x_1352_;
v_b_1349_ = v___x_1366_;
goto _start;
}
}
else
{
lean_dec_ref(v_x2_1345_);
return v_b_1349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1368_, lean_object* v_as_1369_, lean_object* v_i_1370_, lean_object* v_stop_1371_, lean_object* v_b_1372_){
_start:
{
size_t v_i_boxed_1373_; size_t v_stop_boxed_1374_; lean_object* v_res_1375_; 
v_i_boxed_1373_ = lean_unbox_usize(v_i_1370_);
lean_dec(v_i_1370_);
v_stop_boxed_1374_ = lean_unbox_usize(v_stop_1371_);
lean_dec(v_stop_1371_);
v_res_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1368_, v_as_1369_, v_i_boxed_1373_, v_stop_boxed_1374_, v_b_1372_);
lean_dec_ref(v_as_1369_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1376_, size_t v_i_1377_, size_t v_stop_1378_, lean_object* v_b_1379_){
_start:
{
lean_object* v___y_1381_; uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_eq(v_i_1377_, v_stop_1378_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v_targetDecls_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1386_ = lean_array_uget_borrowed(v_as_1376_, v_i_1377_);
v_targetDecls_1387_ = lean_ctor_get(v___x_1386_, 13);
v___x_1388_ = lean_array_get_size(v_targetDecls_1387_);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_nat_dec_lt(v___x_1389_, v___x_1388_);
if (v___x_1390_ == 0)
{
v___y_1381_ = v_b_1379_;
goto v___jp_1380_;
}
else
{
size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_usize_of_nat(v___x_1388_);
v___x_1392_ = ((size_t)0ULL);
lean_inc(v___x_1386_);
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1386_, v_targetDecls_1387_, v___x_1391_, v___x_1392_, v_b_1379_);
v___y_1381_ = v___x_1393_;
goto v___jp_1380_;
}
}
else
{
return v_b_1379_;
}
v___jp_1380_:
{
size_t v___x_1382_; size_t v___x_1383_; 
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_add(v_i_1377_, v___x_1382_);
v_i_1377_ = v___x_1383_;
v_b_1379_ = v___y_1381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1394_, lean_object* v_i_1395_, lean_object* v_stop_1396_, lean_object* v_b_1397_){
_start:
{
size_t v_i_boxed_1398_; size_t v_stop_boxed_1399_; lean_object* v_res_1400_; 
v_i_boxed_1398_ = lean_unbox_usize(v_i_1395_);
lean_dec(v_i_1395_);
v_stop_boxed_1399_ = lean_unbox_usize(v_stop_1396_);
lean_dec(v_stop_1396_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1394_, v_i_boxed_1398_, v_stop_boxed_1399_, v_b_1397_);
lean_dec_ref(v_as_1394_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1401_){
_start:
{
lean_object* v_packages_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_packages_1402_ = lean_ctor_get(v_self_1401_, 5);
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_array_get_size(v_packages_1402_);
v___x_1406_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
return v___x_1403_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_le(v___x_1405_, v___x_1405_);
if (v___x_1407_ == 0)
{
if (v___x_1406_ == 0)
{
return v___x_1403_;
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1405_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1402_, v___x_1408_, v___x_1409_, v___x_1403_);
return v___x_1410_;
}
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1405_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1402_, v___x_1411_, v___x_1412_, v___x_1403_);
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lake_Workspace_leanSrcPath(v_self_1414_);
lean_dec_ref(v_self_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1416_, size_t v_i_1417_, size_t v_stop_1418_, lean_object* v_b_1419_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_usize_dec_eq(v_i_1417_, v_stop_1418_);
if (v___x_1420_ == 0)
{
size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v_config_1424_; lean_object* v_dir_1425_; lean_object* v_buildDir_1426_; lean_object* v_nativeLibDir_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_sub(v_i_1417_, v___x_1421_);
v___x_1423_ = lean_array_uget_borrowed(v_as_1416_, v___x_1422_);
v_config_1424_ = lean_ctor_get(v___x_1423_, 6);
v_dir_1425_ = lean_ctor_get(v___x_1423_, 4);
v_buildDir_1426_ = lean_ctor_get(v_config_1424_, 5);
v_nativeLibDir_1427_ = lean_ctor_get(v_config_1424_, 7);
lean_inc_ref(v_buildDir_1426_);
v___x_1428_ = l_System_FilePath_normalize(v_buildDir_1426_);
lean_inc_ref(v_dir_1425_);
v___x_1429_ = l_Lake_joinRelative(v_dir_1425_, v___x_1428_);
lean_inc_ref(v_nativeLibDir_1427_);
v___x_1430_ = l_System_FilePath_normalize(v_nativeLibDir_1427_);
v___x_1431_ = l_Lake_joinRelative(v___x_1429_, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v_b_1419_);
v_i_1417_ = v___x_1422_;
v_b_1419_ = v___x_1432_;
goto _start;
}
else
{
return v_b_1419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1434_, lean_object* v_i_1435_, lean_object* v_stop_1436_, lean_object* v_b_1437_){
_start:
{
size_t v_i_boxed_1438_; size_t v_stop_boxed_1439_; lean_object* v_res_1440_; 
v_i_boxed_1438_ = lean_unbox_usize(v_i_1435_);
lean_dec(v_i_1435_);
v_stop_boxed_1439_ = lean_unbox_usize(v_stop_1436_);
lean_dec(v_stop_1436_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1434_, v_i_boxed_1438_, v_stop_boxed_1439_, v_b_1437_);
lean_dec_ref(v_as_1434_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1441_){
_start:
{
lean_object* v_packages_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_packages_1442_ = lean_ctor_get(v_self_1441_, 5);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_array_get_size(v_packages_1442_);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_nat_dec_lt(v___x_1445_, v___x_1444_);
if (v___x_1446_ == 0)
{
return v___x_1443_;
}
else
{
size_t v___x_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_usize_of_nat(v___x_1444_);
v___x_1448_ = ((size_t)0ULL);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1442_, v___x_1447_, v___x_1448_, v___x_1443_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lake_Workspace_sharedLibPath(v_self_1450_);
lean_dec_ref(v_self_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1452_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = l_System_Platform_isWindows;
if (v___x_1453_ == 0)
{
lean_object* v_lakeEnv_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v_lakeEnv_1454_ = lean_ctor_get(v_self_1452_, 1);
v___x_1455_ = l_Lake_Workspace_binPath(v_self_1452_);
v___x_1456_ = l_Lake_Env_path(v_lakeEnv_1454_);
v___x_1457_ = l_List_appendTR___redArg(v___x_1455_, v___x_1456_);
return v___x_1457_;
}
else
{
lean_object* v_lakeEnv_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_lakeEnv_1458_ = lean_ctor_get(v_self_1452_, 1);
v___x_1459_ = l_Lake_Workspace_binPath(v_self_1452_);
v___x_1460_ = l_Lake_Workspace_sharedLibPath(v_self_1452_);
v___x_1461_ = l_List_appendTR___redArg(v___x_1459_, v___x_1460_);
v___x_1462_ = l_Lake_Env_path(v_lakeEnv_1458_);
v___x_1463_ = l_List_appendTR___redArg(v___x_1461_, v___x_1462_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lake_Workspace_augmentedPath(v_self_1464_);
lean_dec_ref(v_self_1464_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1466_){
_start:
{
lean_object* v_lakeEnv_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_lakeEnv_1467_ = lean_ctor_get(v_self_1466_, 1);
v___x_1468_ = l_Lake_Workspace_leanPath(v_self_1466_);
v___x_1469_ = l_Lake_Env_leanPath(v_lakeEnv_1467_);
v___x_1470_ = l_List_appendTR___redArg(v___x_1468_, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lake_Workspace_augmentedLeanPath(v_self_1471_);
lean_dec_ref(v_self_1471_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1473_){
_start:
{
lean_object* v_lakeEnv_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_lakeEnv_1474_ = lean_ctor_get(v_self_1473_, 1);
v___x_1475_ = l_Lake_Workspace_leanSrcPath(v_self_1473_);
v___x_1476_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1474_);
v___x_1477_ = l_List_appendTR___redArg(v___x_1475_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1478_);
lean_dec_ref(v_self_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1480_){
_start:
{
lean_object* v_lakeEnv_1481_; lean_object* v_lean_1482_; lean_object* v_initSharedLibPath_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_lakeEnv_1481_ = lean_ctor_get(v_self_1480_, 1);
v_lean_1482_ = lean_ctor_get(v_lakeEnv_1481_, 1);
v_initSharedLibPath_1483_ = lean_ctor_get(v_lakeEnv_1481_, 16);
lean_inc(v_initSharedLibPath_1483_);
v___x_1484_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1482_);
v___x_1485_ = l_Lake_Workspace_sharedLibPath(v_self_1480_);
lean_dec_ref(v_self_1480_);
v___x_1486_ = l_List_appendTR___redArg(v___x_1484_, v___x_1485_);
v___x_1487_ = l_List_appendTR___redArg(v___x_1486_, v_initSharedLibPath_1483_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1503_){
_start:
{
lean_object* v_lakeEnv_1504_; lean_object* v_root_1505_; lean_object* v_lakeCache_1506_; lean_object* v_enableArtifactCache_x3f_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___x_1540_; lean_object* v___y_1542_; uint8_t v_val_1561_; 
v_lakeEnv_1504_ = lean_ctor_get(v_self_1503_, 1);
v_root_1505_ = lean_ctor_get(v_self_1503_, 0);
v_lakeCache_1506_ = lean_ctor_get(v_self_1503_, 3);
v_enableArtifactCache_x3f_1507_ = lean_ctor_get(v_lakeEnv_1504_, 6);
lean_inc_ref(v_lakeEnv_1504_);
v___x_1508_ = l_Lake_Env_baseVars(v_lakeEnv_1504_);
v___x_1509_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1506_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_lakeCache_1506_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1540_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
if (lean_obj_tag(v_enableArtifactCache_x3f_1507_) == 0)
{
lean_object* v_config_1564_; lean_object* v_enableArtifactCache_x3f_1565_; 
v_config_1564_ = lean_ctor_get(v_root_1505_, 6);
v_enableArtifactCache_x3f_1565_ = lean_ctor_get(v_config_1564_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1565_) == 1)
{
lean_object* v_val_1566_; uint8_t v___x_1567_; 
v_val_1566_ = lean_ctor_get(v_enableArtifactCache_x3f_1565_, 0);
v___x_1567_ = lean_unbox(v_val_1566_);
v_val_1561_ = v___x_1567_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1568_; 
v___x_1568_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__11));
v___y_1542_ = v___x_1568_;
goto v___jp_1541_;
}
}
else
{
lean_object* v_val_1569_; uint8_t v___x_1570_; 
v_val_1569_ = lean_ctor_get(v_enableArtifactCache_x3f_1507_, 0);
v___x_1570_ = lean_unbox(v_val_1569_);
v_val_1561_ = v___x_1570_;
goto v___jp_1560_;
}
v___jp_1512_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_vars_1532_; uint8_t v___x_1533_; 
lean_inc_ref(v___y_1516_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___y_1516_);
lean_ctor_set(v___x_1518_, 1, v___y_1517_);
v___x_1519_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1520_ = l_Lake_Workspace_augmentedPath(v_self_1503_);
v___x_1521_ = l_System_SearchPath_toString(v___x_1520_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1519_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_unsigned_to_nat(6u);
v___x_1525_ = lean_mk_empty_array_with_capacity(v___x_1524_);
v___x_1526_ = lean_array_push(v___x_1525_, v___x_1511_);
v___x_1527_ = lean_array_push(v___x_1526_, v___y_1513_);
v___x_1528_ = lean_array_push(v___x_1527_, v___y_1514_);
v___x_1529_ = lean_array_push(v___x_1528_, v___y_1515_);
v___x_1530_ = lean_array_push(v___x_1529_, v___x_1518_);
v___x_1531_ = lean_array_push(v___x_1530_, v___x_1523_);
v_vars_1532_ = l_Array_append___redArg(v___x_1508_, v___x_1531_);
lean_dec_ref(v___x_1531_);
v___x_1533_ = l_System_Platform_isWindows;
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1534_ = l_Lake_sharedLibPathEnvVar;
v___x_1535_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1503_);
v___x_1536_ = l_System_SearchPath_toString(v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1534_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_array_push(v_vars_1532_, v___x_1538_);
return v___x_1539_;
}
else
{
lean_dec_ref(v_self_1503_);
return v_vars_1532_;
}
}
v___jp_1541_:
{
lean_object* v_config_1543_; uint8_t v_bootstrap_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_config_1543_ = lean_ctor_get(v_root_1505_, 6);
v_bootstrap_1544_ = lean_ctor_get_uint8(v_config_1543_, sizeof(void*)*26);
lean_inc(v___y_1542_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1540_);
lean_ctor_set(v___x_1545_, 1, v___y_1542_);
v___x_1546_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1547_ = l_Lake_Workspace_augmentedLeanPath(v_self_1503_);
v___x_1548_ = l_System_SearchPath_toString(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1546_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
v___x_1552_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1503_);
v___x_1553_ = l_System_SearchPath_toString(v___x_1552_);
v___x_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1551_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (v_bootstrap_1544_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = l_Lake_Env_leanGithash(v_lakeEnv_1504_);
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
v___y_1513_ = v___x_1545_;
v___y_1514_ = v___x_1550_;
v___y_1515_ = v___x_1555_;
v___y_1516_ = v___x_1556_;
v___y_1517_ = v___x_1558_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_box(0);
v___y_1513_ = v___x_1545_;
v___y_1514_ = v___x_1550_;
v___y_1515_ = v___x_1555_;
v___y_1516_ = v___x_1556_;
v___y_1517_ = v___x_1559_;
goto v___jp_1512_;
}
}
v___jp_1560_:
{
if (v_val_1561_ == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__7));
v___y_1542_ = v___x_1562_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__9));
v___y_1542_ = v___x_1563_;
goto v___jp_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1571_, size_t v_i_1572_, size_t v_stop_1573_, lean_object* v_b_1574_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_usize_dec_eq(v_i_1572_, v_stop_1573_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_array_uget_borrowed(v_as_1571_, v_i_1572_);
lean_inc(v___x_1577_);
v___x_1578_ = l_Lake_Package_clean(v___x_1577_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; size_t v___x_1580_; size_t v___x_1581_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = lean_usize_add(v_i_1572_, v___x_1580_);
v_i_1572_ = v___x_1581_;
v_b_1574_ = v_a_1579_;
goto _start;
}
else
{
return v___x_1578_;
}
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_b_1574_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1584_, lean_object* v_i_1585_, lean_object* v_stop_1586_, lean_object* v_b_1587_, lean_object* v___y_1588_){
_start:
{
size_t v_i_boxed_1589_; size_t v_stop_boxed_1590_; lean_object* v_res_1591_; 
v_i_boxed_1589_ = lean_unbox_usize(v_i_1585_);
lean_dec(v_i_1585_);
v_stop_boxed_1590_ = lean_unbox_usize(v_stop_1586_);
lean_dec(v_stop_1586_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1584_, v_i_boxed_1589_, v_stop_boxed_1590_, v_b_1587_);
lean_dec_ref(v_as_1584_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* v_self_1592_){
_start:
{
lean_object* v_packages_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_packages_1594_ = lean_ctor_get(v_self_1592_, 5);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_array_get_size(v_packages_1594_);
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_nat_dec_lt(v___x_1595_, v___x_1596_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
return v___x_1599_;
}
else
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_nat_dec_le(v___x_1596_, v___x_1596_);
if (v___x_1600_ == 0)
{
if (v___x_1598_ == 0)
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1597_);
return v___x_1601_;
}
else
{
size_t v___x_1602_; size_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = lean_usize_of_nat(v___x_1596_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1594_, v___x_1602_, v___x_1603_, v___x_1597_);
return v___x_1604_;
}
}
else
{
size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = lean_usize_of_nat(v___x_1596_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1594_, v___x_1605_, v___x_1606_, v___x_1597_);
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lake_Workspace_clean(v_self_1608_);
lean_dec_ref(v_self_1608_);
return v_res_1610_;
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

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
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(lean_object* v_a_1_){
_start:
{
lean_inc_ref(v_a_1_);
return v_a_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk___boxed(lean_object* v_a_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(v_a_2_);
lean_dec_ref(v_a_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(lean_object* v_a_6_){
_start:
{
lean_inc(v_a_6_);
return v_a_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet___boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(v_a_7_);
lean_dec(v_a_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(lean_object* v_inst_11_){
_start:
{
lean_inc_ref(v_inst_11_);
return v_inst_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace___boxed(lean_object* v_inst_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(v_inst_12_);
lean_dec_ref(v_inst_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(lean_object* v_self_19_, lean_object* v_as_20_, size_t v_i_21_, size_t v_stop_22_, lean_object* v_b_23_){
_start:
{
lean_object* v___y_25_; uint8_t v___x_32_; 
v___x_32_ = lean_usize_dec_eq(v_i_21_, v_stop_22_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_46_; 
v___x_33_ = lean_array_uget_borrowed(v_as_20_, v_i_21_);
v___x_46_ = l_Lake_Package_findTargetDecl_x3f(v___x_33_, v_self_19_);
if (lean_obj_tag(v___x_46_) == 0)
{
goto v___jp_34_;
}
else
{
lean_object* v_val_47_; lean_object* v_kind_48_; lean_object* v_config_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_val_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_val_47_);
lean_dec_ref(v___x_46_);
v_kind_48_ = lean_ctor_get(v_val_47_, 2);
lean_inc(v_kind_48_);
v_config_49_ = lean_ctor_get(v_val_47_, 3);
lean_inc(v_config_49_);
lean_dec(v_val_47_);
v___x_50_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_51_ = lean_name_eq(v_kind_48_, v___x_50_);
lean_dec(v_kind_48_);
if (v___x_51_ == 0)
{
lean_dec(v_config_49_);
goto v___jp_34_;
}
else
{
lean_object* v_roots_52_; lean_object* v___x_53_; 
v_roots_52_ = lean_ctor_get(v_config_49_, 2);
lean_inc_ref(v_roots_52_);
lean_dec(v_config_49_);
v___x_53_ = l_Array_append___redArg(v_b_23_, v_roots_52_);
lean_dec_ref(v_roots_52_);
v___y_25_ = v___x_53_;
goto v___jp_24_;
}
}
v___jp_34_:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lake_Package_findTargetDecl_x3f(v___x_33_, v_self_19_);
if (lean_obj_tag(v___x_35_) == 0)
{
goto v___jp_29_;
}
else
{
lean_object* v_val_36_; lean_object* v_kind_37_; lean_object* v_config_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_val_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_val_36_);
lean_dec_ref(v___x_35_);
v_kind_37_ = lean_ctor_get(v_val_36_, 2);
lean_inc(v_kind_37_);
v_config_38_ = lean_ctor_get(v_val_36_, 3);
lean_inc(v_config_38_);
lean_dec(v_val_36_);
v___x_39_ = l_Lake_LeanExe_keyword;
v___x_40_ = lean_name_eq(v_kind_37_, v___x_39_);
lean_dec(v_kind_37_);
if (v___x_40_ == 0)
{
lean_dec(v_config_38_);
goto v___jp_29_;
}
else
{
lean_object* v_root_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_root_41_ = lean_ctor_get(v_config_38_, 2);
lean_inc(v_root_41_);
lean_dec(v_config_38_);
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_mk_empty_array_with_capacity(v___x_42_);
v___x_44_ = lean_array_push(v___x_43_, v_root_41_);
v___x_45_ = l_Array_append___redArg(v_b_23_, v___x_44_);
lean_dec_ref(v___x_44_);
v___y_25_ = v___x_45_;
goto v___jp_24_;
}
}
}
}
else
{
return v_b_23_;
}
v___jp_24_:
{
size_t v___x_26_; size_t v___x_27_; 
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_add(v_i_21_, v___x_26_);
v_i_21_ = v___x_27_;
v_b_23_ = v___y_25_;
goto _start;
}
v___jp_29_:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0));
v___x_31_ = l_Array_append___redArg(v_b_23_, v___x_30_);
v___y_25_ = v___x_31_;
goto v___jp_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___boxed(lean_object* v_self_54_, lean_object* v_as_55_, lean_object* v_i_56_, lean_object* v_stop_57_, lean_object* v_b_58_){
_start:
{
size_t v_i_boxed_59_; size_t v_stop_boxed_60_; lean_object* v_res_61_; 
v_i_boxed_59_ = lean_unbox_usize(v_i_56_);
lean_dec(v_i_56_);
v_stop_boxed_60_ = lean_unbox_usize(v_stop_57_);
lean_dec(v_stop_57_);
v_res_61_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_54_, v_as_55_, v_i_boxed_59_, v_stop_boxed_60_, v_b_58_);
lean_dec_ref(v_as_55_);
lean_dec_ref(v_self_54_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots(lean_object* v_self_64_){
_start:
{
lean_object* v_defaultTargets_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_defaultTargets_65_ = lean_ctor_get(v_self_64_, 15);
v___x_66_ = lean_unsigned_to_nat(0u);
v___x_67_ = ((lean_object*)(l_Lake_Package_defaultTargetRoots___closed__0));
v___x_68_ = lean_array_get_size(v_defaultTargets_65_);
v___x_69_ = lean_nat_dec_lt(v___x_66_, v___x_68_);
if (v___x_69_ == 0)
{
return v___x_67_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = lean_nat_dec_le(v___x_68_, v___x_68_);
if (v___x_70_ == 0)
{
if (v___x_69_ == 0)
{
return v___x_67_;
}
else
{
size_t v___x_71_; size_t v___x_72_; lean_object* v___x_73_; 
v___x_71_ = ((size_t)0ULL);
v___x_72_ = lean_usize_of_nat(v___x_68_);
v___x_73_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_64_, v_defaultTargets_65_, v___x_71_, v___x_72_, v___x_67_);
return v___x_73_;
}
}
else
{
size_t v___x_74_; size_t v___x_75_; lean_object* v___x_76_; 
v___x_74_ = ((size_t)0ULL);
v___x_75_ = lean_usize_of_nat(v___x_68_);
v___x_76_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_64_, v_defaultTargets_65_, v___x_74_, v___x_75_, v___x_67_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots___boxed(lean_object* v_self_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lake_Package_defaultTargetRoots(v_self_77_);
lean_dec_ref(v_self_77_);
return v_res_78_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(lean_object* v_ws_79_){
_start:
{
lean_object* v_root_80_; lean_object* v_config_81_; uint8_t v_bootstrap_82_; 
v_root_80_ = lean_ctor_get(v_ws_79_, 0);
v_config_81_ = lean_ctor_get(v_root_80_, 6);
v_bootstrap_82_ = lean_ctor_get_uint8(v_config_81_, sizeof(void*)*26);
return v_bootstrap_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(lean_object* v_ws_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(v_ws_83_);
lean_dec_ref(v_ws_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object* v_self_86_){
_start:
{
lean_object* v_root_87_; lean_object* v_dir_88_; 
v_root_87_ = lean_ctor_get(v_self_86_, 0);
v_dir_88_ = lean_ctor_get(v_root_87_, 4);
lean_inc_ref(v_dir_88_);
return v_dir_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object* v_self_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lake_Workspace_dir(v_self_89_);
lean_dec_ref(v_self_89_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object* v_self_91_){
_start:
{
lean_object* v_root_92_; lean_object* v_config_93_; lean_object* v_toWorkspaceConfig_94_; 
v_root_92_ = lean_ctor_get(v_self_91_, 0);
v_config_93_ = lean_ctor_get(v_root_92_, 6);
v_toWorkspaceConfig_94_ = lean_ctor_get(v_config_93_, 0);
lean_inc_ref(v_toWorkspaceConfig_94_);
return v_toWorkspaceConfig_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object* v_self_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lake_Workspace_config(v_self_95_);
lean_dec_ref(v_self_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object* v_self_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lake_defaultLakeDir;
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object* v_self_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lake_Workspace_relLakeDir(v_self_99_);
lean_dec_ref(v_self_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object* v_self_101_){
_start:
{
lean_object* v_root_102_; lean_object* v_dir_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_root_102_ = lean_ctor_get(v_self_101_, 0);
lean_inc_ref(v_root_102_);
lean_dec_ref(v_self_101_);
v_dir_103_ = lean_ctor_get(v_root_102_, 4);
lean_inc_ref(v_dir_103_);
lean_dec_ref(v_root_102_);
v___x_104_ = l_Lake_defaultLakeDir;
v___x_105_ = l_Lake_joinRelative(v_dir_103_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f(lean_object* v_ws_106_){
_start:
{
lean_object* v_lakeEnv_107_; lean_object* v_enableArtifactCache_x3f_108_; 
v_lakeEnv_107_ = lean_ctor_get(v_ws_106_, 1);
v_enableArtifactCache_x3f_108_ = lean_ctor_get(v_lakeEnv_107_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_108_) == 0)
{
lean_object* v_root_109_; lean_object* v_config_110_; lean_object* v_enableArtifactCache_x3f_111_; 
v_root_109_ = lean_ctor_get(v_ws_106_, 0);
v_config_110_ = lean_ctor_get(v_root_109_, 6);
v_enableArtifactCache_x3f_111_ = lean_ctor_get(v_config_110_, 24);
lean_inc(v_enableArtifactCache_x3f_111_);
return v_enableArtifactCache_x3f_111_;
}
else
{
lean_inc_ref(v_enableArtifactCache_x3f_108_);
return v_enableArtifactCache_x3f_108_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f___boxed(lean_object* v_ws_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lake_Workspace_enableArtifactCache_x3f(v_ws_112_);
lean_dec_ref(v_ws_112_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_enableArtifactCache(lean_object* v_ws_114_){
_start:
{
lean_object* v_lakeEnv_115_; lean_object* v_enableArtifactCache_x3f_116_; 
v_lakeEnv_115_ = lean_ctor_get(v_ws_114_, 1);
v_enableArtifactCache_x3f_116_ = lean_ctor_get(v_lakeEnv_115_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_116_) == 0)
{
lean_object* v_root_117_; lean_object* v_config_118_; lean_object* v_enableArtifactCache_x3f_119_; 
v_root_117_ = lean_ctor_get(v_ws_114_, 0);
v_config_118_ = lean_ctor_get(v_root_117_, 6);
v_enableArtifactCache_x3f_119_ = lean_ctor_get(v_config_118_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
else
{
lean_object* v_val_121_; uint8_t v___x_122_; 
v_val_121_ = lean_ctor_get(v_enableArtifactCache_x3f_119_, 0);
v___x_122_ = lean_unbox(v_val_121_);
return v___x_122_;
}
}
else
{
lean_object* v_val_123_; uint8_t v___x_124_; 
v_val_123_ = lean_ctor_get(v_enableArtifactCache_x3f_116_, 0);
v___x_124_ = lean_unbox(v_val_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache___boxed(lean_object* v_ws_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Lake_Workspace_enableArtifactCache(v_ws_125_);
lean_dec_ref(v_ws_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object* v_ws_128_){
_start:
{
lean_object* v_lakeEnv_129_; lean_object* v_enableArtifactCache_x3f_130_; 
v_lakeEnv_129_ = lean_ctor_get(v_ws_128_, 1);
v_enableArtifactCache_x3f_130_ = lean_ctor_get(v_lakeEnv_129_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_130_) == 0)
{
lean_object* v_root_131_; lean_object* v_config_132_; lean_object* v_enableArtifactCache_x3f_133_; 
v_root_131_ = lean_ctor_get(v_ws_128_, 0);
v_config_132_ = lean_ctor_get(v_root_131_, 6);
v_enableArtifactCache_x3f_133_ = lean_ctor_get(v_config_132_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_133_) == 0)
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
else
{
lean_object* v_val_135_; uint8_t v___x_136_; 
v_val_135_ = lean_ctor_get(v_enableArtifactCache_x3f_133_, 0);
v___x_136_ = lean_unbox(v_val_135_);
return v___x_136_;
}
}
else
{
lean_object* v_val_137_; uint8_t v___x_138_; 
v_val_137_ = lean_ctor_get(v_enableArtifactCache_x3f_130_, 0);
v___x_138_ = lean_unbox(v_val_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheWritable___boxed(lean_object* v_ws_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_139_);
lean_dec_ref(v_ws_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheEnabled(lean_object* v_ws_142_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheEnabled___boxed(lean_object* v_ws_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Lake_Workspace_isRootArtifactCacheEnabled(v_ws_144_);
lean_dec_ref(v_ws_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f(lean_object* v_ws_147_){
_start:
{
lean_object* v_root_148_; lean_object* v_config_149_; lean_object* v_restoreAllArtifacts_x3f_150_; 
v_root_148_ = lean_ctor_get(v_ws_147_, 0);
v_config_149_ = lean_ctor_get(v_root_148_, 6);
v_restoreAllArtifacts_x3f_150_ = lean_ctor_get(v_config_149_, 25);
lean_inc(v_restoreAllArtifacts_x3f_150_);
return v_restoreAllArtifacts_x3f_150_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(lean_object* v_ws_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lake_Workspace_restoreAllArtifacts_x3f(v_ws_151_);
lean_dec_ref(v_ws_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain(lean_object* v_ws_153_){
_start:
{
lean_object* v_lakeEnv_154_; lean_object* v_toolchain_155_; 
v_lakeEnv_154_ = lean_ctor_get(v_ws_153_, 1);
v_toolchain_155_ = lean_ctor_get(v_lakeEnv_154_, 18);
lean_inc_ref(v_toolchain_155_);
return v_toolchain_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain___boxed(lean_object* v_ws_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lake_Workspace_cacheToolchain(v_ws_156_);
lean_dec_ref(v_ws_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService(lean_object* v_ws_158_){
_start:
{
lean_object* v_lakeConfig_159_; lean_object* v_defaultCacheService_160_; 
v_lakeConfig_159_ = lean_ctor_get(v_ws_158_, 2);
v_defaultCacheService_160_ = lean_ctor_get(v_lakeConfig_159_, 1);
lean_inc_ref(v_defaultCacheService_160_);
return v_defaultCacheService_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService___boxed(lean_object* v_ws_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_Workspace_defaultCacheService(v_ws_161_);
lean_dec_ref(v_ws_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f(lean_object* v_ws_163_){
_start:
{
lean_object* v_lakeConfig_164_; lean_object* v_defaultUploadCacheService_x3f_165_; 
v_lakeConfig_164_ = lean_ctor_get(v_ws_163_, 2);
v_defaultUploadCacheService_x3f_165_ = lean_ctor_get(v_lakeConfig_164_, 2);
lean_inc(v_defaultUploadCacheService_x3f_165_);
return v_defaultUploadCacheService_x3f_165_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(lean_object* v_ws_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lake_Workspace_defaultCacheUploadService_x3f(v_ws_166_);
lean_dec_ref(v_ws_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object* v_ws_168_, lean_object* v_service_169_){
_start:
{
lean_object* v_lakeConfig_170_; lean_object* v_cacheServices_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_lakeConfig_170_ = lean_ctor_get(v_ws_168_, 2);
v_cacheServices_171_ = lean_ctor_get(v_lakeConfig_170_, 3);
v___x_172_ = lean_box(0);
v___x_173_ = l_Lean_Name_str___override(v___x_172_, v_service_169_);
v___x_174_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_171_, v___x_173_);
lean_dec(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object* v_ws_175_, lean_object* v_service_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lake_Workspace_findCacheService_x3f(v_ws_175_, v_service_176_);
lean_dec_ref(v_ws_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* v_self_178_){
_start:
{
lean_object* v_root_179_; lean_object* v_config_180_; lean_object* v_toWorkspaceConfig_181_; lean_object* v___x_182_; 
v_root_179_ = lean_ctor_get(v_self_178_, 0);
lean_inc_ref(v_root_179_);
lean_dec_ref(v_self_178_);
v_config_180_ = lean_ctor_get(v_root_179_, 6);
lean_inc_ref(v_config_180_);
lean_dec_ref(v_root_179_);
v_toWorkspaceConfig_181_ = lean_ctor_get(v_config_180_, 0);
lean_inc_ref(v_toWorkspaceConfig_181_);
lean_dec_ref(v_config_180_);
v___x_182_ = l_System_FilePath_normalize(v_toWorkspaceConfig_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* v_self_183_){
_start:
{
lean_object* v_root_184_; lean_object* v_config_185_; lean_object* v_dir_186_; lean_object* v_toWorkspaceConfig_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_root_184_ = lean_ctor_get(v_self_183_, 0);
lean_inc_ref(v_root_184_);
lean_dec_ref(v_self_183_);
v_config_185_ = lean_ctor_get(v_root_184_, 6);
lean_inc_ref(v_config_185_);
v_dir_186_ = lean_ctor_get(v_root_184_, 4);
lean_inc_ref(v_dir_186_);
lean_dec_ref(v_root_184_);
v_toWorkspaceConfig_187_ = lean_ctor_get(v_config_185_, 0);
lean_inc_ref(v_toWorkspaceConfig_187_);
lean_dec_ref(v_config_185_);
v___x_188_ = l_System_FilePath_normalize(v_toWorkspaceConfig_187_);
v___x_189_ = l_Lake_joinRelative(v_dir_186_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object* v_self_190_){
_start:
{
lean_object* v_root_191_; lean_object* v_config_192_; lean_object* v_toLeanConfig_193_; lean_object* v_moreLeanArgs_194_; 
v_root_191_ = lean_ctor_get(v_self_190_, 0);
v_config_192_ = lean_ctor_get(v_root_191_, 6);
v_toLeanConfig_193_ = lean_ctor_get(v_config_192_, 1);
v_moreLeanArgs_194_ = lean_ctor_get(v_toLeanConfig_193_, 1);
lean_inc_ref(v_moreLeanArgs_194_);
return v_moreLeanArgs_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object* v_self_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lake_Workspace_leanArgs(v_self_195_);
lean_dec_ref(v_self_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* v_self_197_){
_start:
{
lean_object* v_root_198_; lean_object* v_config_199_; lean_object* v_toLeanConfig_200_; lean_object* v_leanOptions_201_; lean_object* v___x_202_; 
v_root_198_ = lean_ctor_get(v_self_197_, 0);
v_config_199_ = lean_ctor_get(v_root_198_, 6);
v_toLeanConfig_200_ = lean_ctor_get(v_config_199_, 1);
v_leanOptions_201_ = lean_ctor_get(v_toLeanConfig_200_, 0);
v___x_202_ = l_Lean_LeanOptions_ofArray(v_leanOptions_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* v_self_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lake_Workspace_leanOptions(v_self_203_);
lean_dec_ref(v_self_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* v_self_205_){
_start:
{
lean_object* v_root_206_; lean_object* v_config_207_; lean_object* v_toLeanConfig_208_; lean_object* v_leanOptions_209_; lean_object* v_moreServerOptions_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_root_206_ = lean_ctor_get(v_self_205_, 0);
v_config_207_ = lean_ctor_get(v_root_206_, 6);
v_toLeanConfig_208_ = lean_ctor_get(v_config_207_, 1);
v_leanOptions_209_ = lean_ctor_get(v_toLeanConfig_208_, 0);
v_moreServerOptions_210_ = lean_ctor_get(v_toLeanConfig_208_, 4);
v___x_211_ = l_Lean_LeanOptions_ofArray(v_leanOptions_209_);
v___x_212_ = l_Lean_LeanOptions_appendArray(v___x_211_, v_moreServerOptions_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* v_self_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lake_Workspace_serverOptions(v_self_213_);
lean_dec_ref(v_self_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object* v_self_215_){
_start:
{
lean_object* v_root_216_; lean_object* v___x_217_; 
v_root_216_ = lean_ctor_get(v_self_215_, 0);
v___x_217_ = l_Lake_Package_defaultTargetRoots(v_root_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object* v_self_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_Workspace_defaultTargetRoots(v_self_218_);
lean_dec_ref(v_self_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* v_self_220_){
_start:
{
lean_object* v_root_221_; lean_object* v_dir_222_; lean_object* v_relManifestFile_223_; lean_object* v___x_224_; 
v_root_221_ = lean_ctor_get(v_self_220_, 0);
lean_inc_ref(v_root_221_);
lean_dec_ref(v_self_220_);
v_dir_222_ = lean_ctor_get(v_root_221_, 4);
lean_inc_ref(v_dir_222_);
v_relManifestFile_223_ = lean_ctor_get(v_root_221_, 9);
lean_inc_ref(v_relManifestFile_223_);
lean_dec_ref(v_root_221_);
v___x_224_ = l_Lake_joinRelative(v_dir_222_, v_relManifestFile_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* v_self_226_){
_start:
{
lean_object* v_root_227_; lean_object* v_dir_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_root_227_ = lean_ctor_get(v_self_226_, 0);
lean_inc_ref(v_root_227_);
lean_dec_ref(v_self_226_);
v_dir_228_ = lean_ctor_get(v_root_227_, 4);
lean_inc_ref(v_dir_228_);
lean_dec_ref(v_root_227_);
v___x_229_ = l_Lake_defaultLakeDir;
v___x_230_ = l_Lake_joinRelative(v_dir_228_, v___x_229_);
v___x_231_ = ((lean_object*)(l_Lake_Workspace_packageOverridesFile___closed__0));
v___x_232_ = l_Lake_joinRelative(v___x_230_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(lean_object* v_k_233_, lean_object* v_v_234_, lean_object* v_t_235_){
_start:
{
if (lean_obj_tag(v_t_235_) == 0)
{
lean_object* v_size_236_; lean_object* v_k_237_; lean_object* v_v_238_; lean_object* v_l_239_; lean_object* v_r_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_520_; 
v_size_236_ = lean_ctor_get(v_t_235_, 0);
v_k_237_ = lean_ctor_get(v_t_235_, 1);
v_v_238_ = lean_ctor_get(v_t_235_, 2);
v_l_239_ = lean_ctor_get(v_t_235_, 3);
v_r_240_ = lean_ctor_get(v_t_235_, 4);
v_isSharedCheck_520_ = !lean_is_exclusive(v_t_235_);
if (v_isSharedCheck_520_ == 0)
{
v___x_242_ = v_t_235_;
v_isShared_243_ = v_isSharedCheck_520_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_r_240_);
lean_inc(v_l_239_);
lean_inc(v_v_238_);
lean_inc(v_k_237_);
lean_inc(v_size_236_);
lean_dec(v_t_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_520_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; 
v___x_244_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_233_, v_k_237_);
switch(v___x_244_)
{
case 0:
{
lean_object* v_impl_245_; lean_object* v___x_246_; 
lean_dec(v_size_236_);
v_impl_245_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_k_233_, v_v_234_, v_l_239_);
v___x_246_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_240_) == 0)
{
lean_object* v_size_247_; lean_object* v_size_248_; lean_object* v_k_249_; lean_object* v_v_250_; lean_object* v_l_251_; lean_object* v_r_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_size_247_ = lean_ctor_get(v_r_240_, 0);
v_size_248_ = lean_ctor_get(v_impl_245_, 0);
lean_inc(v_size_248_);
v_k_249_ = lean_ctor_get(v_impl_245_, 1);
lean_inc(v_k_249_);
v_v_250_ = lean_ctor_get(v_impl_245_, 2);
lean_inc(v_v_250_);
v_l_251_ = lean_ctor_get(v_impl_245_, 3);
lean_inc(v_l_251_);
v_r_252_ = lean_ctor_get(v_impl_245_, 4);
lean_inc(v_r_252_);
v___x_253_ = lean_unsigned_to_nat(3u);
v___x_254_ = lean_nat_mul(v___x_253_, v_size_247_);
v___x_255_ = lean_nat_dec_lt(v___x_254_, v_size_248_);
lean_dec(v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
lean_dec(v_r_252_);
lean_dec(v_l_251_);
lean_dec(v_v_250_);
lean_dec(v_k_249_);
v___x_256_ = lean_nat_add(v___x_246_, v_size_248_);
lean_dec(v_size_248_);
v___x_257_ = lean_nat_add(v___x_256_, v_size_247_);
lean_dec(v___x_256_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 3, v_impl_245_);
lean_ctor_set(v___x_242_, 0, v___x_257_);
v___x_259_ = v___x_242_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_impl_245_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_r_240_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_326_; 
v_isSharedCheck_326_ = !lean_is_exclusive(v_impl_245_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; lean_object* v_unused_328_; lean_object* v_unused_329_; lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_327_ = lean_ctor_get(v_impl_245_, 4);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_impl_245_, 3);
lean_dec(v_unused_328_);
v_unused_329_ = lean_ctor_get(v_impl_245_, 2);
lean_dec(v_unused_329_);
v_unused_330_ = lean_ctor_get(v_impl_245_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_impl_245_, 0);
lean_dec(v_unused_331_);
v___x_262_ = v_impl_245_;
v_isShared_263_ = v_isSharedCheck_326_;
goto v_resetjp_261_;
}
else
{
lean_dec(v_impl_245_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_326_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_size_264_; lean_object* v_size_265_; lean_object* v_k_266_; lean_object* v_v_267_; lean_object* v_l_268_; lean_object* v_r_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_size_264_ = lean_ctor_get(v_l_251_, 0);
v_size_265_ = lean_ctor_get(v_r_252_, 0);
v_k_266_ = lean_ctor_get(v_r_252_, 1);
v_v_267_ = lean_ctor_get(v_r_252_, 2);
v_l_268_ = lean_ctor_get(v_r_252_, 3);
v_r_269_ = lean_ctor_get(v_r_252_, 4);
v___x_270_ = lean_unsigned_to_nat(2u);
v___x_271_ = lean_nat_mul(v___x_270_, v_size_264_);
v___x_272_ = lean_nat_dec_lt(v_size_265_, v___x_271_);
lean_dec(v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_301_; 
lean_inc(v_r_269_);
lean_inc(v_l_268_);
lean_inc(v_v_267_);
lean_inc(v_k_266_);
v_isSharedCheck_301_ = !lean_is_exclusive(v_r_252_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; lean_object* v_unused_306_; 
v_unused_302_ = lean_ctor_get(v_r_252_, 4);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_r_252_, 3);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_r_252_, 2);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_r_252_, 1);
lean_dec(v_unused_305_);
v_unused_306_ = lean_ctor_get(v_r_252_, 0);
lean_dec(v_unused_306_);
v___x_274_ = v_r_252_;
v_isShared_275_ = v_isSharedCheck_301_;
goto v_resetjp_273_;
}
else
{
lean_dec(v_r_252_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_301_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___x_289_; lean_object* v___y_291_; 
v___x_276_ = lean_nat_add(v___x_246_, v_size_248_);
lean_dec(v_size_248_);
v___x_277_ = lean_nat_add(v___x_276_, v_size_247_);
lean_dec(v___x_276_);
v___x_289_ = lean_nat_add(v___x_246_, v_size_264_);
if (lean_obj_tag(v_l_268_) == 0)
{
lean_object* v_size_299_; 
v_size_299_ = lean_ctor_get(v_l_268_, 0);
lean_inc(v_size_299_);
v___y_291_ = v_size_299_;
goto v___jp_290_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___y_291_ = v___x_300_;
goto v___jp_290_;
}
v___jp_278_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_nat_add(v___y_279_, v___y_281_);
lean_dec(v___y_281_);
lean_dec(v___y_279_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 4, v_r_240_);
lean_ctor_set(v___x_274_, 3, v_r_269_);
lean_ctor_set(v___x_274_, 2, v_v_238_);
lean_ctor_set(v___x_274_, 1, v_k_237_);
lean_ctor_set(v___x_274_, 0, v___x_282_);
v___x_284_ = v___x_274_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_r_269_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_r_240_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_286_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 4, v___x_284_);
lean_ctor_set(v___x_262_, 3, v___y_280_);
lean_ctor_set(v___x_262_, 2, v_v_267_);
lean_ctor_set(v___x_262_, 1, v_k_266_);
lean_ctor_set(v___x_262_, 0, v___x_277_);
v___x_286_ = v___x_262_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_k_266_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_v_267_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v___y_280_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_nat_add(v___x_289_, v___y_291_);
lean_dec(v___y_291_);
lean_dec(v___x_289_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v_l_268_);
lean_ctor_set(v___x_242_, 3, v_l_251_);
lean_ctor_set(v___x_242_, 2, v_v_250_);
lean_ctor_set(v___x_242_, 1, v_k_249_);
lean_ctor_set(v___x_242_, 0, v___x_292_);
v___x_294_ = v___x_242_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v_k_249_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_v_250_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_l_251_);
lean_ctor_set(v_reuseFailAlloc_298_, 4, v_l_268_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = lean_nat_add(v___x_246_, v_size_247_);
if (lean_obj_tag(v_r_269_) == 0)
{
lean_object* v_size_296_; 
v_size_296_ = lean_ctor_get(v_r_269_, 0);
lean_inc(v_size_296_);
v___y_279_ = v___x_295_;
v___y_280_ = v___x_294_;
v___y_281_ = v_size_296_;
goto v___jp_278_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___y_279_ = v___x_295_;
v___y_280_ = v___x_294_;
v___y_281_ = v___x_297_;
goto v___jp_278_;
}
}
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
lean_del_object(v___x_242_);
v___x_307_ = lean_nat_add(v___x_246_, v_size_248_);
lean_dec(v_size_248_);
v___x_308_ = lean_nat_add(v___x_307_, v_size_247_);
lean_dec(v___x_307_);
v___x_309_ = lean_nat_add(v___x_246_, v_size_247_);
v___x_310_ = lean_nat_add(v___x_309_, v_size_265_);
lean_dec(v___x_309_);
lean_inc_ref(v_r_240_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 4, v_r_240_);
lean_ctor_set(v___x_262_, 3, v_r_252_);
lean_ctor_set(v___x_262_, 2, v_v_238_);
lean_ctor_set(v___x_262_, 1, v_k_237_);
lean_ctor_set(v___x_262_, 0, v___x_310_);
v___x_312_ = v___x_262_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_r_252_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_r_240_);
v___x_312_ = v_reuseFailAlloc_325_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_isSharedCheck_319_ = !lean_is_exclusive(v_r_240_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; 
v_unused_320_ = lean_ctor_get(v_r_240_, 4);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_r_240_, 3);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_r_240_, 2);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_r_240_, 1);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_r_240_, 0);
lean_dec(v_unused_324_);
v___x_314_ = v_r_240_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_dec(v_r_240_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 4, v___x_312_);
lean_ctor_set(v___x_314_, 3, v_l_251_);
lean_ctor_set(v___x_314_, 2, v_v_250_);
lean_ctor_set(v___x_314_, 1, v_k_249_);
lean_ctor_set(v___x_314_, 0, v___x_308_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_k_249_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_v_250_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_l_251_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v___x_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_332_; 
v_l_332_ = lean_ctor_get(v_impl_245_, 3);
lean_inc(v_l_332_);
if (lean_obj_tag(v_l_332_) == 0)
{
lean_object* v_r_333_; lean_object* v_k_334_; lean_object* v_v_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_346_; 
v_r_333_ = lean_ctor_get(v_impl_245_, 4);
v_k_334_ = lean_ctor_get(v_impl_245_, 1);
v_v_335_ = lean_ctor_get(v_impl_245_, 2);
v_isSharedCheck_346_ = !lean_is_exclusive(v_impl_245_);
if (v_isSharedCheck_346_ == 0)
{
lean_object* v_unused_347_; lean_object* v_unused_348_; 
v_unused_347_ = lean_ctor_get(v_impl_245_, 3);
lean_dec(v_unused_347_);
v_unused_348_ = lean_ctor_get(v_impl_245_, 0);
lean_dec(v_unused_348_);
v___x_337_ = v_impl_245_;
v_isShared_338_ = v_isSharedCheck_346_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_r_333_);
lean_inc(v_v_335_);
lean_inc(v_k_334_);
lean_dec(v_impl_245_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_346_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_333_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 3, v_r_333_);
lean_ctor_set(v___x_337_, 2, v_v_238_);
lean_ctor_set(v___x_337_, 1, v_k_237_);
lean_ctor_set(v___x_337_, 0, v___x_246_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_345_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_345_, 3, v_r_333_);
lean_ctor_set(v_reuseFailAlloc_345_, 4, v_r_333_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v___x_341_);
lean_ctor_set(v___x_242_, 3, v_l_332_);
lean_ctor_set(v___x_242_, 2, v_v_335_);
lean_ctor_set(v___x_242_, 1, v_k_334_);
lean_ctor_set(v___x_242_, 0, v___x_339_);
v___x_343_ = v___x_242_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_v_335_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_l_332_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_r_349_; 
v_r_349_ = lean_ctor_get(v_impl_245_, 4);
lean_inc(v_r_349_);
if (lean_obj_tag(v_r_349_) == 0)
{
lean_object* v_k_350_; lean_object* v_v_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_374_; 
v_k_350_ = lean_ctor_get(v_impl_245_, 1);
v_v_351_ = lean_ctor_get(v_impl_245_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v_impl_245_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_375_ = lean_ctor_get(v_impl_245_, 4);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v_impl_245_, 3);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v_impl_245_, 0);
lean_dec(v_unused_377_);
v___x_353_ = v_impl_245_;
v_isShared_354_ = v_isSharedCheck_374_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_v_351_);
lean_inc(v_k_350_);
lean_dec(v_impl_245_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_374_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_k_355_; lean_object* v_v_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_370_; 
v_k_355_ = lean_ctor_get(v_r_349_, 1);
v_v_356_ = lean_ctor_get(v_r_349_, 2);
v_isSharedCheck_370_ = !lean_is_exclusive(v_r_349_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_371_ = lean_ctor_get(v_r_349_, 4);
lean_dec(v_unused_371_);
v_unused_372_ = lean_ctor_get(v_r_349_, 3);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_r_349_, 0);
lean_dec(v_unused_373_);
v___x_358_ = v_r_349_;
v_isShared_359_ = v_isSharedCheck_370_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_v_356_);
lean_inc(v_k_355_);
lean_dec(v_r_349_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_370_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_unsigned_to_nat(3u);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 4, v_l_332_);
lean_ctor_set(v___x_358_, 3, v_l_332_);
lean_ctor_set(v___x_358_, 2, v_v_351_);
lean_ctor_set(v___x_358_, 1, v_k_350_);
lean_ctor_set(v___x_358_, 0, v___x_246_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_350_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_351_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_l_332_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_l_332_);
v___x_362_ = v_reuseFailAlloc_369_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_364_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 4, v_l_332_);
lean_ctor_set(v___x_353_, 2, v_v_238_);
lean_ctor_set(v___x_353_, 1, v_k_237_);
lean_ctor_set(v___x_353_, 0, v___x_246_);
v___x_364_ = v___x_353_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_l_332_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_l_332_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v___x_364_);
lean_ctor_set(v___x_242_, 3, v___x_362_);
lean_ctor_set(v___x_242_, 2, v_v_356_);
lean_ctor_set(v___x_242_, 1, v_k_355_);
lean_ctor_set(v___x_242_, 0, v___x_360_);
v___x_366_ = v___x_242_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_k_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_v_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_unsigned_to_nat(2u);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v_r_349_);
lean_ctor_set(v___x_242_, 3, v_impl_245_);
lean_ctor_set(v___x_242_, 0, v___x_378_);
v___x_380_ = v___x_242_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_impl_245_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_r_349_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
case 1:
{
lean_object* v___x_383_; 
lean_dec(v_v_238_);
lean_dec(v_k_237_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 2, v_v_234_);
lean_ctor_set(v___x_242_, 1, v_k_233_);
v___x_383_ = v___x_242_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_size_236_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_k_233_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_v_234_);
lean_ctor_set(v_reuseFailAlloc_384_, 3, v_l_239_);
lean_ctor_set(v_reuseFailAlloc_384_, 4, v_r_240_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
default: 
{
lean_object* v_impl_385_; lean_object* v___x_386_; 
lean_dec(v_size_236_);
v_impl_385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_k_233_, v_v_234_, v_r_240_);
v___x_386_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_239_) == 0)
{
lean_object* v_size_387_; lean_object* v_size_388_; lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_l_391_; lean_object* v_r_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_size_387_ = lean_ctor_get(v_l_239_, 0);
v_size_388_ = lean_ctor_get(v_impl_385_, 0);
lean_inc(v_size_388_);
v_k_389_ = lean_ctor_get(v_impl_385_, 1);
lean_inc(v_k_389_);
v_v_390_ = lean_ctor_get(v_impl_385_, 2);
lean_inc(v_v_390_);
v_l_391_ = lean_ctor_get(v_impl_385_, 3);
lean_inc(v_l_391_);
v_r_392_ = lean_ctor_get(v_impl_385_, 4);
lean_inc(v_r_392_);
v___x_393_ = lean_unsigned_to_nat(3u);
v___x_394_ = lean_nat_mul(v___x_393_, v_size_387_);
v___x_395_ = lean_nat_dec_lt(v___x_394_, v_size_388_);
lean_dec(v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
lean_dec(v_r_392_);
lean_dec(v_l_391_);
lean_dec(v_v_390_);
lean_dec(v_k_389_);
v___x_396_ = lean_nat_add(v___x_386_, v_size_387_);
v___x_397_ = lean_nat_add(v___x_396_, v_size_388_);
lean_dec(v_size_388_);
lean_dec(v___x_396_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v_impl_385_);
lean_ctor_set(v___x_242_, 0, v___x_397_);
v___x_399_ = v___x_242_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_l_239_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_impl_385_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v_impl_385_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; lean_object* v_unused_467_; lean_object* v_unused_468_; lean_object* v_unused_469_; 
v_unused_465_ = lean_ctor_get(v_impl_385_, 4);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_impl_385_, 3);
lean_dec(v_unused_466_);
v_unused_467_ = lean_ctor_get(v_impl_385_, 2);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_impl_385_, 1);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_impl_385_, 0);
lean_dec(v_unused_469_);
v___x_402_ = v_impl_385_;
v_isShared_403_ = v_isSharedCheck_464_;
goto v_resetjp_401_;
}
else
{
lean_dec(v_impl_385_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_464_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_size_404_; lean_object* v_k_405_; lean_object* v_v_406_; lean_object* v_l_407_; lean_object* v_r_408_; lean_object* v_size_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_size_404_ = lean_ctor_get(v_l_391_, 0);
v_k_405_ = lean_ctor_get(v_l_391_, 1);
v_v_406_ = lean_ctor_get(v_l_391_, 2);
v_l_407_ = lean_ctor_get(v_l_391_, 3);
v_r_408_ = lean_ctor_get(v_l_391_, 4);
v_size_409_ = lean_ctor_get(v_r_392_, 0);
v___x_410_ = lean_unsigned_to_nat(2u);
v___x_411_ = lean_nat_mul(v___x_410_, v_size_409_);
v___x_412_ = lean_nat_dec_lt(v_size_404_, v___x_411_);
lean_dec(v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_440_; 
lean_inc(v_r_408_);
lean_inc(v_l_407_);
lean_inc(v_v_406_);
lean_inc(v_k_405_);
v_isSharedCheck_440_ = !lean_is_exclusive(v_l_391_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_441_ = lean_ctor_get(v_l_391_, 4);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_l_391_, 3);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_l_391_, 2);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_l_391_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_l_391_, 0);
lean_dec(v_unused_445_);
v___x_414_ = v_l_391_;
v_isShared_415_ = v_isSharedCheck_440_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_l_391_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_440_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___y_419_; lean_object* v___y_420_; lean_object* v___y_421_; lean_object* v___y_430_; 
v___x_416_ = lean_nat_add(v___x_386_, v_size_387_);
v___x_417_ = lean_nat_add(v___x_416_, v_size_388_);
lean_dec(v_size_388_);
if (lean_obj_tag(v_l_407_) == 0)
{
lean_object* v_size_438_; 
v_size_438_ = lean_ctor_get(v_l_407_, 0);
lean_inc(v_size_438_);
v___y_430_ = v_size_438_;
goto v___jp_429_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___y_430_ = v___x_439_;
goto v___jp_429_;
}
v___jp_418_:
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_nat_add(v___y_419_, v___y_421_);
lean_dec(v___y_421_);
lean_dec(v___y_419_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 4, v_r_392_);
lean_ctor_set(v___x_414_, 3, v_r_408_);
lean_ctor_set(v___x_414_, 2, v_v_390_);
lean_ctor_set(v___x_414_, 1, v_k_389_);
lean_ctor_set(v___x_414_, 0, v___x_422_);
v___x_424_ = v___x_414_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_389_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_390_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_r_408_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_r_392_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v___x_424_);
lean_ctor_set(v___x_402_, 3, v___y_420_);
lean_ctor_set(v___x_402_, 2, v_v_406_);
lean_ctor_set(v___x_402_, 1, v_k_405_);
lean_ctor_set(v___x_402_, 0, v___x_417_);
v___x_426_ = v___x_402_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_k_405_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_v_406_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v___y_420_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_nat_add(v___x_416_, v___y_430_);
lean_dec(v___y_430_);
lean_dec(v___x_416_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v_l_407_);
lean_ctor_set(v___x_242_, 0, v___x_431_);
v___x_433_ = v___x_242_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_l_239_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_l_407_);
v___x_433_ = v_reuseFailAlloc_437_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
v___x_434_ = lean_nat_add(v___x_386_, v_size_409_);
if (lean_obj_tag(v_r_408_) == 0)
{
lean_object* v_size_435_; 
v_size_435_ = lean_ctor_get(v_r_408_, 0);
lean_inc(v_size_435_);
v___y_419_ = v___x_434_;
v___y_420_ = v___x_433_;
v___y_421_ = v_size_435_;
goto v___jp_418_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_unsigned_to_nat(0u);
v___y_419_ = v___x_434_;
v___y_420_ = v___x_433_;
v___y_421_ = v___x_436_;
goto v___jp_418_;
}
}
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
lean_del_object(v___x_242_);
v___x_446_ = lean_nat_add(v___x_386_, v_size_387_);
v___x_447_ = lean_nat_add(v___x_446_, v_size_388_);
lean_dec(v_size_388_);
v___x_448_ = lean_nat_add(v___x_446_, v_size_404_);
lean_dec(v___x_446_);
lean_inc_ref(v_l_239_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 4, v_l_391_);
lean_ctor_set(v___x_402_, 3, v_l_239_);
lean_ctor_set(v___x_402_, 2, v_v_238_);
lean_ctor_set(v___x_402_, 1, v_k_237_);
lean_ctor_set(v___x_402_, 0, v___x_448_);
v___x_450_ = v___x_402_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_l_239_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_l_391_);
v___x_450_ = v_reuseFailAlloc_463_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_isSharedCheck_457_ = !lean_is_exclusive(v_l_239_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; lean_object* v_unused_459_; lean_object* v_unused_460_; lean_object* v_unused_461_; lean_object* v_unused_462_; 
v_unused_458_ = lean_ctor_get(v_l_239_, 4);
lean_dec(v_unused_458_);
v_unused_459_ = lean_ctor_get(v_l_239_, 3);
lean_dec(v_unused_459_);
v_unused_460_ = lean_ctor_get(v_l_239_, 2);
lean_dec(v_unused_460_);
v_unused_461_ = lean_ctor_get(v_l_239_, 1);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_l_239_, 0);
lean_dec(v_unused_462_);
v___x_452_ = v_l_239_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_l_239_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v_r_392_);
lean_ctor_set(v___x_452_, 3, v___x_450_);
lean_ctor_set(v___x_452_, 2, v_v_390_);
lean_ctor_set(v___x_452_, 1, v_k_389_);
lean_ctor_set(v___x_452_, 0, v___x_447_);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_k_389_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_v_390_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_r_392_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_470_; 
v_l_470_ = lean_ctor_get(v_impl_385_, 3);
lean_inc(v_l_470_);
if (lean_obj_tag(v_l_470_) == 0)
{
lean_object* v_r_471_; lean_object* v_k_472_; lean_object* v_v_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_496_; 
v_r_471_ = lean_ctor_get(v_impl_385_, 4);
v_k_472_ = lean_ctor_get(v_impl_385_, 1);
v_v_473_ = lean_ctor_get(v_impl_385_, 2);
v_isSharedCheck_496_ = !lean_is_exclusive(v_impl_385_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; 
v_unused_497_ = lean_ctor_get(v_impl_385_, 3);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_impl_385_, 0);
lean_dec(v_unused_498_);
v___x_475_ = v_impl_385_;
v_isShared_476_ = v_isSharedCheck_496_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_r_471_);
lean_inc(v_v_473_);
lean_inc(v_k_472_);
lean_dec(v_impl_385_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_496_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v_k_477_; lean_object* v_v_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
v_k_477_ = lean_ctor_get(v_l_470_, 1);
v_v_478_ = lean_ctor_get(v_l_470_, 2);
v_isSharedCheck_492_ = !lean_is_exclusive(v_l_470_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_493_ = lean_ctor_get(v_l_470_, 4);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v_l_470_, 3);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_l_470_, 0);
lean_dec(v_unused_495_);
v___x_480_ = v_l_470_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_v_478_);
lean_inc(v_k_477_);
lean_dec(v_l_470_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_471_, 2);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 4, v_r_471_);
lean_ctor_set(v___x_480_, 3, v_r_471_);
lean_ctor_set(v___x_480_, 2, v_v_238_);
lean_ctor_set(v___x_480_, 1, v_k_237_);
lean_ctor_set(v___x_480_, 0, v___x_386_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_r_471_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_r_471_);
v___x_484_ = v_reuseFailAlloc_491_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
lean_inc(v_r_471_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 3, v_r_471_);
lean_ctor_set(v___x_475_, 0, v___x_386_);
v___x_486_ = v___x_475_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_k_472_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_v_473_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_r_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v_r_471_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v___x_486_);
lean_ctor_set(v___x_242_, 3, v___x_484_);
lean_ctor_set(v___x_242_, 2, v_v_478_);
lean_ctor_set(v___x_242_, 1, v_k_477_);
lean_ctor_set(v___x_242_, 0, v___x_482_);
v___x_488_ = v___x_242_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_k_477_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_v_478_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
}
else
{
lean_object* v_r_499_; 
v_r_499_ = lean_ctor_get(v_impl_385_, 4);
lean_inc(v_r_499_);
if (lean_obj_tag(v_r_499_) == 0)
{
lean_object* v_k_500_; lean_object* v_v_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_k_500_ = lean_ctor_get(v_impl_385_, 1);
v_v_501_ = lean_ctor_get(v_impl_385_, 2);
v_isSharedCheck_512_ = !lean_is_exclusive(v_impl_385_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; lean_object* v_unused_514_; lean_object* v_unused_515_; 
v_unused_513_ = lean_ctor_get(v_impl_385_, 4);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_impl_385_, 3);
lean_dec(v_unused_514_);
v_unused_515_ = lean_ctor_get(v_impl_385_, 0);
lean_dec(v_unused_515_);
v___x_503_ = v_impl_385_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_v_501_);
lean_inc(v_k_500_);
lean_dec(v_impl_385_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(3u);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v_l_470_);
lean_ctor_set(v___x_503_, 2, v_v_238_);
lean_ctor_set(v___x_503_, 1, v_k_237_);
lean_ctor_set(v___x_503_, 0, v___x_386_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_l_470_);
lean_ctor_set(v_reuseFailAlloc_511_, 4, v_l_470_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v_r_499_);
lean_ctor_set(v___x_242_, 3, v___x_507_);
lean_ctor_set(v___x_242_, 2, v_v_501_);
lean_ctor_set(v___x_242_, 1, v_k_500_);
lean_ctor_set(v___x_242_, 0, v___x_505_);
v___x_509_ = v___x_242_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_k_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_v_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v_r_499_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_unsigned_to_nat(2u);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v_impl_385_);
lean_ctor_set(v___x_242_, 3, v_r_499_);
lean_ctor_set(v___x_242_, 0, v___x_516_);
v___x_518_ = v___x_242_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_k_237_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_v_238_);
lean_ctor_set(v_reuseFailAlloc_519_, 3, v_r_499_);
lean_ctor_set(v_reuseFailAlloc_519_, 4, v_impl_385_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
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
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_k_233_);
lean_ctor_set(v___x_522_, 2, v_v_234_);
lean_ctor_set(v___x_522_, 3, v_t_235_);
lean_ctor_set(v___x_522_, 4, v_t_235_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_523_, lean_object* v_self_524_){
_start:
{
lean_object* v_root_525_; lean_object* v_lakeEnv_526_; lean_object* v_lakeConfig_527_; lean_object* v_lakeCache_528_; lean_object* v_lakeArgs_x3f_529_; lean_object* v_packages_530_; lean_object* v_packageMap_531_; lean_object* v_facetConfigs_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_542_; 
v_root_525_ = lean_ctor_get(v_self_524_, 0);
v_lakeEnv_526_ = lean_ctor_get(v_self_524_, 1);
v_lakeConfig_527_ = lean_ctor_get(v_self_524_, 2);
v_lakeCache_528_ = lean_ctor_get(v_self_524_, 3);
v_lakeArgs_x3f_529_ = lean_ctor_get(v_self_524_, 4);
v_packages_530_ = lean_ctor_get(v_self_524_, 5);
v_packageMap_531_ = lean_ctor_get(v_self_524_, 6);
v_facetConfigs_532_ = lean_ctor_get(v_self_524_, 7);
v_isSharedCheck_542_ = !lean_is_exclusive(v_self_524_);
if (v_isSharedCheck_542_ == 0)
{
v___x_534_ = v_self_524_;
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_facetConfigs_532_);
lean_inc(v_packageMap_531_);
lean_inc(v_packages_530_);
lean_inc(v_lakeArgs_x3f_529_);
lean_inc(v_lakeCache_528_);
lean_inc(v_lakeConfig_527_);
lean_inc(v_lakeEnv_526_);
lean_inc(v_root_525_);
lean_dec(v_self_524_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_keyName_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v_keyName_536_ = lean_ctor_get(v_pkg_523_, 2);
lean_inc(v_keyName_536_);
lean_inc_ref(v_pkg_523_);
v___x_537_ = lean_array_push(v_packages_530_, v_pkg_523_);
v___x_538_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_keyName_536_, v_pkg_523_, v_packageMap_531_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 6, v___x_538_);
lean_ctor_set(v___x_534_, 5, v___x_537_);
v___x_540_ = v___x_534_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_root_525_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_lakeEnv_526_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_lakeConfig_527_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_lakeCache_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 4, v_lakeArgs_x3f_529_);
lean_ctor_set(v_reuseFailAlloc_541_, 5, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_541_, 6, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_541_, 7, v_facetConfigs_532_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0(lean_object* v_00_u03b2_543_, lean_object* v_k_544_, lean_object* v_v_545_, lean_object* v_t_546_, lean_object* v_hl_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_k_544_, v_v_545_, v_t_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_550_, lean_object* v_self_551_){
_start:
{
lean_object* v_packageMap_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_packageMap_552_ = lean_ctor_get(v_self_551_, 6);
lean_inc(v_packageMap_552_);
lean_dec_ref(v_self_551_);
v___x_553_ = ((lean_object*)(l_Lake_Workspace_findPackageByKey_x3f___closed__0));
v___x_554_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_553_, v_packageMap_552_, v_keyName_550_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v_a_558_, lean_object* v_x_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_baseName_561_; uint8_t v___x_562_; 
v_baseName_561_ = lean_ctor_get(v_a_558_, 1);
v___x_562_ = lean_name_eq(v_baseName_561_, v_name_555_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec_ref(v_a_558_);
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_556_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v___x_556_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v_a_558_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_557_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_568_, lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v_a_571_, lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_568_, v___x_569_, v___x_570_, v_a_571_, v_x_572_, v___y_573_);
lean_dec_ref(v___y_573_);
lean_dec(v_name_568_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_597_, lean_object* v_self_598_){
_start:
{
lean_object* v_packages_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___f_604_; size_t v_sz_605_; size_t v___x_606_; lean_object* v___x_607_; lean_object* v_fst_608_; 
v_packages_599_ = lean_ctor_get(v_self_598_, 5);
lean_inc_ref(v_packages_599_);
lean_dec_ref(v_self_598_);
v___x_600_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__9));
v___x_601_ = lean_box(0);
v___x_602_ = lean_box(0);
v___x_603_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__10));
v___f_604_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_604_, 0, v_name_597_);
lean_closure_set(v___f_604_, 1, v___x_603_);
lean_closure_set(v___f_604_, 2, v___x_602_);
v_sz_605_ = lean_array_size(v_packages_599_);
v___x_606_ = ((size_t)0ULL);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_600_, v_packages_599_, v___f_604_, v_sz_605_, v___x_606_, v___x_603_);
v_fst_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_fst_608_);
lean_dec(v___x_607_);
if (lean_obj_tag(v_fst_608_) == 0)
{
return v___x_601_;
}
else
{
lean_object* v_val_609_; 
v_val_609_ = lean_ctor_get(v_fst_608_, 0);
lean_inc(v_val_609_);
lean_dec_ref(v_fst_608_);
return v_val_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_610_, lean_object* v_self_611_){
_start:
{
lean_object* v_packageMap_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_packageMap_612_ = lean_ctor_get(v_self_611_, 6);
lean_inc(v_packageMap_612_);
lean_dec_ref(v_self_611_);
v___x_613_ = ((lean_object*)(l_Lake_Workspace_findPackageByKey_x3f___closed__0));
v___x_614_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_613_, v_packageMap_612_, v_name_610_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_618_, lean_object* v_as_619_, size_t v_sz_620_, size_t v_i_621_, lean_object* v_b_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_623_ == 0)
{
return v_b_622_;
}
else
{
lean_object* v_a_624_; lean_object* v_scripts_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v_b_622_);
v_a_624_ = lean_array_uget_borrowed(v_as_619_, v_i_621_);
v_scripts_625_ = lean_ctor_get(v_a_624_, 16);
v___x_626_ = lean_box(0);
v___x_627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_625_, v_script_618_);
if (lean_obj_tag(v___x_627_) == 1)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_626_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; size_t v___x_631_; size_t v___x_632_; 
lean_dec(v___x_627_);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_621_, v___x_631_);
v_i_621_ = v___x_632_;
v_b_622_ = v___x_630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_634_, lean_object* v_as_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_b_638_){
_start:
{
size_t v_sz_boxed_639_; size_t v_i_boxed_640_; lean_object* v_res_641_; 
v_sz_boxed_639_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_640_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_634_, v_as_635_, v_sz_boxed_639_, v_i_boxed_640_, v_b_638_);
lean_dec_ref(v_as_635_);
lean_dec(v_script_634_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_642_, lean_object* v_self_643_){
_start:
{
lean_object* v_packages_644_; lean_object* v___x_645_; lean_object* v___x_646_; size_t v_sz_647_; size_t v___x_648_; lean_object* v___x_649_; lean_object* v_fst_650_; 
v_packages_644_ = lean_ctor_get(v_self_643_, 5);
v___x_645_ = lean_box(0);
v___x_646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_647_ = lean_array_size(v_packages_644_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_642_, v_packages_644_, v_sz_647_, v___x_648_, v___x_646_);
v_fst_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_fst_650_);
lean_dec_ref(v___x_649_);
if (lean_obj_tag(v_fst_650_) == 0)
{
return v___x_645_;
}
else
{
lean_object* v_val_651_; 
v_val_651_ = lean_ctor_get(v_fst_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref(v_fst_650_);
return v_val_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_652_, lean_object* v_self_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lake_Workspace_findScript_x3f(v_script_652_, v_self_653_);
lean_dec_ref(v_self_653_);
lean_dec(v_script_652_);
return v_res_654_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_655_, lean_object* v_as_656_, size_t v_i_657_, size_t v_stop_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_eq(v_i_657_, v_stop_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_array_uget_borrowed(v_as_656_, v_i_657_);
v___x_661_ = l_Lake_Package_isLocalModule(v_mod_655_, v___x_660_);
if (v___x_661_ == 0)
{
size_t v___x_662_; size_t v___x_663_; 
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_add(v_i_657_, v___x_662_);
v_i_657_ = v___x_663_;
goto _start;
}
else
{
return v___x_661_;
}
}
else
{
uint8_t v___x_665_; 
v___x_665_ = 0;
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_666_, lean_object* v_as_667_, lean_object* v_i_668_, lean_object* v_stop_669_){
_start:
{
size_t v_i_boxed_670_; size_t v_stop_boxed_671_; uint8_t v_res_672_; lean_object* v_r_673_; 
v_i_boxed_670_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_stop_boxed_671_ = lean_unbox_usize(v_stop_669_);
lean_dec(v_stop_669_);
v_res_672_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_666_, v_as_667_, v_i_boxed_670_, v_stop_boxed_671_);
lean_dec_ref(v_as_667_);
lean_dec(v_mod_666_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_674_, lean_object* v_self_675_){
_start:
{
lean_object* v_packages_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_packages_676_ = lean_ctor_get(v_self_675_, 5);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_array_get_size(v_packages_676_);
v___x_679_ = lean_nat_dec_lt(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
return v___x_679_;
}
else
{
if (v___x_679_ == 0)
{
return v___x_679_;
}
else
{
size_t v___x_680_; size_t v___x_681_; uint8_t v___x_682_; 
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_678_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_674_, v_packages_676_, v___x_680_, v___x_681_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_683_, lean_object* v_self_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lake_Workspace_isLocalModule(v_mod_683_, v_self_684_);
lean_dec_ref(v_self_684_);
lean_dec(v_mod_683_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_687_, lean_object* v_as_688_, size_t v_i_689_, size_t v_stop_690_){
_start:
{
uint8_t v___x_691_; 
v___x_691_ = lean_usize_dec_eq(v_i_689_, v_stop_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_array_uget_borrowed(v_as_688_, v_i_689_);
v___x_693_ = l_Lake_Package_isBuildableModule(v_mod_687_, v___x_692_);
if (v___x_693_ == 0)
{
size_t v___x_694_; size_t v___x_695_; 
v___x_694_ = ((size_t)1ULL);
v___x_695_ = lean_usize_add(v_i_689_, v___x_694_);
v_i_689_ = v___x_695_;
goto _start;
}
else
{
return v___x_693_;
}
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_698_, lean_object* v_as_699_, lean_object* v_i_700_, lean_object* v_stop_701_){
_start:
{
size_t v_i_boxed_702_; size_t v_stop_boxed_703_; uint8_t v_res_704_; lean_object* v_r_705_; 
v_i_boxed_702_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_stop_boxed_703_ = lean_unbox_usize(v_stop_701_);
lean_dec(v_stop_701_);
v_res_704_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_698_, v_as_699_, v_i_boxed_702_, v_stop_boxed_703_);
lean_dec_ref(v_as_699_);
lean_dec(v_mod_698_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_706_, lean_object* v_self_707_){
_start:
{
lean_object* v_packages_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_packages_708_ = lean_ctor_get(v_self_707_, 5);
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_array_get_size(v_packages_708_);
v___x_711_ = lean_nat_dec_lt(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
return v___x_711_;
}
else
{
if (v___x_711_ == 0)
{
return v___x_711_;
}
else
{
size_t v___x_712_; size_t v___x_713_; uint8_t v___x_714_; 
v___x_712_ = ((size_t)0ULL);
v___x_713_ = lean_usize_of_nat(v___x_710_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_706_, v_packages_708_, v___x_712_, v___x_713_);
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_715_, lean_object* v_self_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Lake_Workspace_isBuildableModule(v_mod_715_, v_self_716_);
lean_dec_ref(v_self_716_);
lean_dec(v_mod_715_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_722_, lean_object* v_as_723_, size_t v_sz_724_, size_t v_i_725_, lean_object* v_b_726_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_lt(v_i_725_, v_sz_724_);
if (v___x_727_ == 0)
{
lean_dec(v_mod_722_);
return v_b_726_;
}
else
{
lean_object* v___x_728_; lean_object* v_a_729_; lean_object* v___x_730_; 
lean_dec_ref(v_b_726_);
v___x_728_ = lean_box(0);
v_a_729_ = lean_array_uget_borrowed(v_as_723_, v_i_725_);
lean_inc(v_a_729_);
lean_inc(v_mod_722_);
v___x_730_ = l_Lake_Package_findModule_x3f(v_mod_722_, v_a_729_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v_mod_722_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v___x_728_);
return v___x_732_;
}
else
{
lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; 
lean_dec(v___x_730_);
v___x_733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_725_, v___x_734_);
v_i_725_ = v___x_735_;
v_b_726_ = v___x_733_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_737_, lean_object* v_as_738_, lean_object* v_sz_739_, lean_object* v_i_740_, lean_object* v_b_741_){
_start:
{
size_t v_sz_boxed_742_; size_t v_i_boxed_743_; lean_object* v_res_744_; 
v_sz_boxed_742_ = lean_unbox_usize(v_sz_739_);
lean_dec(v_sz_739_);
v_i_boxed_743_ = lean_unbox_usize(v_i_740_);
lean_dec(v_i_740_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_737_, v_as_738_, v_sz_boxed_742_, v_i_boxed_743_, v_b_741_);
lean_dec_ref(v_as_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_745_, lean_object* v_self_746_){
_start:
{
lean_object* v_packages_747_; lean_object* v___x_748_; lean_object* v___x_749_; size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; lean_object* v_fst_753_; 
v_packages_747_ = lean_ctor_get(v_self_746_, 5);
v___x_748_ = lean_box(0);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_750_ = lean_array_size(v_packages_747_);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_745_, v_packages_747_, v_sz_750_, v___x_751_, v___x_749_);
v_fst_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_fst_753_);
lean_dec_ref(v___x_752_);
if (lean_obj_tag(v_fst_753_) == 0)
{
return v___x_748_;
}
else
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v_fst_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref(v_fst_753_);
return v_val_754_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_755_, lean_object* v_self_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lake_Workspace_findModule_x3f(v_mod_755_, v_self_756_);
lean_dec_ref(v_self_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_758_, lean_object* v_as_759_, size_t v_i_760_, size_t v_stop_761_, lean_object* v_b_762_){
_start:
{
lean_object* v___y_764_; uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_eq(v_i_760_, v_stop_761_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_array_uget_borrowed(v_as_759_, v_i_760_);
lean_inc(v___x_769_);
lean_inc(v_mod_758_);
v___x_770_ = l_Lake_Package_findModule_x3f(v_mod_758_, v___x_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
v___y_764_ = v_b_762_;
goto v___jp_763_;
}
else
{
lean_object* v_val_771_; lean_object* v___x_772_; 
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = lean_array_push(v_b_762_, v_val_771_);
v___y_764_ = v___x_772_;
goto v___jp_763_;
}
}
else
{
lean_dec(v_mod_758_);
return v_b_762_;
}
v___jp_763_:
{
size_t v___x_765_; size_t v___x_766_; 
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_760_, v___x_765_);
v_i_760_ = v___x_766_;
v_b_762_ = v___y_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_773_, lean_object* v_as_774_, lean_object* v_i_775_, lean_object* v_stop_776_, lean_object* v_b_777_){
_start:
{
size_t v_i_boxed_778_; size_t v_stop_boxed_779_; lean_object* v_res_780_; 
v_i_boxed_778_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_stop_boxed_779_ = lean_unbox_usize(v_stop_776_);
lean_dec(v_stop_776_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_773_, v_as_774_, v_i_boxed_778_, v_stop_boxed_779_, v_b_777_);
lean_dec_ref(v_as_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_783_, lean_object* v_as_784_, lean_object* v_start_785_, lean_object* v_stop_786_){
_start:
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_788_ = lean_nat_dec_lt(v_start_785_, v_stop_786_);
if (v___x_788_ == 0)
{
lean_dec(v_mod_783_);
return v___x_787_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_array_get_size(v_as_784_);
v___x_790_ = lean_nat_dec_le(v_stop_786_, v___x_789_);
if (v___x_790_ == 0)
{
uint8_t v___x_791_; 
v___x_791_ = lean_nat_dec_lt(v_start_785_, v___x_789_);
if (v___x_791_ == 0)
{
lean_dec(v_mod_783_);
return v___x_787_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
v___x_792_ = lean_usize_of_nat(v_start_785_);
v___x_793_ = lean_usize_of_nat(v___x_789_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_783_, v_as_784_, v___x_792_, v___x_793_, v___x_787_);
return v___x_794_;
}
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = lean_usize_of_nat(v_start_785_);
v___x_796_ = lean_usize_of_nat(v_stop_786_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_783_, v_as_784_, v___x_795_, v___x_796_, v___x_787_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_798_, lean_object* v_as_799_, lean_object* v_start_800_, lean_object* v_stop_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_798_, v_as_799_, v_start_800_, v_stop_801_);
lean_dec(v_stop_801_);
lean_dec(v_start_800_);
lean_dec_ref(v_as_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_803_, lean_object* v_self_804_){
_start:
{
lean_object* v_packages_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_packages_805_ = lean_ctor_get(v_self_804_, 5);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_array_get_size(v_packages_805_);
v___x_808_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_803_, v_packages_805_, v___x_806_, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_809_, lean_object* v_self_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lake_Workspace_findModules(v_mod_809_, v_self_810_);
lean_dec_ref(v_self_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_812_, lean_object* v_as_813_, size_t v_sz_814_, size_t v_i_815_, lean_object* v_b_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_usize_dec_lt(v_i_815_, v_sz_814_);
if (v___x_817_ == 0)
{
lean_dec(v_mod_812_);
return v_b_816_;
}
else
{
lean_object* v___x_818_; lean_object* v_a_819_; lean_object* v___x_820_; 
lean_dec_ref(v_b_816_);
v___x_818_ = lean_box(0);
v_a_819_ = lean_array_uget_borrowed(v_as_813_, v_i_815_);
lean_inc(v_a_819_);
lean_inc(v_mod_812_);
v___x_820_ = l_Lake_Package_findTargetModule_x3f(v_mod_812_, v_a_819_);
if (lean_obj_tag(v___x_820_) == 1)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_mod_812_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_818_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; size_t v___x_824_; size_t v___x_825_; 
lean_dec(v___x_820_);
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_add(v_i_815_, v___x_824_);
v_i_815_ = v___x_825_;
v_b_816_ = v___x_823_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_827_, lean_object* v_as_828_, lean_object* v_sz_829_, lean_object* v_i_830_, lean_object* v_b_831_){
_start:
{
size_t v_sz_boxed_832_; size_t v_i_boxed_833_; lean_object* v_res_834_; 
v_sz_boxed_832_ = lean_unbox_usize(v_sz_829_);
lean_dec(v_sz_829_);
v_i_boxed_833_ = lean_unbox_usize(v_i_830_);
lean_dec(v_i_830_);
v_res_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_827_, v_as_828_, v_sz_boxed_832_, v_i_boxed_833_, v_b_831_);
lean_dec_ref(v_as_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_835_, lean_object* v_self_836_){
_start:
{
lean_object* v_packages_837_; lean_object* v___x_838_; lean_object* v___x_839_; size_t v_sz_840_; size_t v___x_841_; lean_object* v___x_842_; lean_object* v_fst_843_; 
v_packages_837_ = lean_ctor_get(v_self_836_, 5);
v___x_838_ = lean_box(0);
v___x_839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_840_ = lean_array_size(v_packages_837_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_835_, v_packages_837_, v_sz_840_, v___x_841_, v___x_839_);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_845_, lean_object* v_self_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_845_, v_self_846_);
lean_dec_ref(v_self_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_848_, lean_object* v_as_849_, size_t v_sz_850_, size_t v_i_851_, lean_object* v_b_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_853_ == 0)
{
lean_dec_ref(v_path_848_);
return v_b_852_;
}
else
{
lean_object* v___x_854_; lean_object* v_a_855_; lean_object* v___x_856_; 
lean_dec_ref(v_b_852_);
v___x_854_ = lean_box(0);
v_a_855_ = lean_array_uget_borrowed(v_as_849_, v_i_851_);
lean_inc(v_a_855_);
lean_inc_ref(v_path_848_);
v___x_856_ = l_Lake_Package_findModuleBySrc_x3f(v_path_848_, v_a_855_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_path_848_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_854_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; size_t v___x_860_; size_t v___x_861_; 
lean_dec(v___x_856_);
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_add(v_i_851_, v___x_860_);
v_i_851_ = v___x_861_;
v_b_852_ = v___x_859_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_863_, lean_object* v_as_864_, lean_object* v_sz_865_, lean_object* v_i_866_, lean_object* v_b_867_){
_start:
{
size_t v_sz_boxed_868_; size_t v_i_boxed_869_; lean_object* v_res_870_; 
v_sz_boxed_868_ = lean_unbox_usize(v_sz_865_);
lean_dec(v_sz_865_);
v_i_boxed_869_ = lean_unbox_usize(v_i_866_);
lean_dec(v_i_866_);
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_863_, v_as_864_, v_sz_boxed_868_, v_i_boxed_869_, v_b_867_);
lean_dec_ref(v_as_864_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_871_, lean_object* v_self_872_){
_start:
{
lean_object* v_packages_873_; lean_object* v___x_874_; lean_object* v___x_875_; size_t v_sz_876_; size_t v___x_877_; lean_object* v___x_878_; lean_object* v_fst_879_; 
v_packages_873_ = lean_ctor_get(v_self_872_, 5);
v___x_874_ = lean_box(0);
v___x_875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_876_ = lean_array_size(v_packages_873_);
v___x_877_ = ((size_t)0ULL);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_871_, v_packages_873_, v_sz_876_, v___x_877_, v___x_875_);
v_fst_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_fst_879_);
lean_dec_ref(v___x_878_);
if (lean_obj_tag(v_fst_879_) == 0)
{
return v___x_874_;
}
else
{
lean_object* v_val_880_; 
v_val_880_ = lean_ctor_get(v_fst_879_, 0);
lean_inc(v_val_880_);
lean_dec_ref(v_fst_879_);
return v_val_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_881_, lean_object* v_self_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_881_, v_self_882_);
lean_dec_ref(v_self_882_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_887_, lean_object* v_as_888_, size_t v_sz_889_, size_t v_i_890_, lean_object* v_b_891_){
_start:
{
lean_object* v_a_893_; uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_lt(v_i_890_, v_sz_889_);
if (v___x_897_ == 0)
{
return v_b_891_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_a_900_; lean_object* v___x_901_; 
lean_dec_ref(v_b_891_);
v___x_898_ = lean_box(0);
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_900_ = lean_array_uget_borrowed(v_as_888_, v_i_890_);
v___x_901_ = l_Lake_Package_findTargetDecl_x3f(v_name_887_, v_a_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
v_a_893_ = v___x_899_;
goto v___jp_892_;
}
else
{
lean_object* v_val_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_917_; 
v_val_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_917_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_917_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_val_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_917_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_name_906_; lean_object* v_kind_907_; lean_object* v_config_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_name_906_ = lean_ctor_get(v_val_902_, 1);
lean_inc(v_name_906_);
v_kind_907_ = lean_ctor_get(v_val_902_, 2);
lean_inc(v_kind_907_);
v_config_908_ = lean_ctor_get(v_val_902_, 3);
lean_inc(v_config_908_);
lean_dec(v_val_902_);
v___x_909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_910_ = lean_name_eq(v_kind_907_, v___x_909_);
lean_dec(v_kind_907_);
if (v___x_910_ == 0)
{
lean_dec(v_config_908_);
lean_dec(v_name_906_);
lean_del_object(v___x_904_);
v_a_893_ = v___x_899_;
goto v___jp_892_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_inc(v_a_900_);
v___x_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_911_, 0, v_a_900_);
lean_ctor_set(v___x_911_, 1, v_name_906_);
lean_ctor_set(v___x_911_, 2, v_config_908_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_911_);
v___x_913_ = v___x_904_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_916_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_898_);
return v___x_915_;
}
}
}
}
}
v___jp_892_:
{
size_t v___x_894_; size_t v___x_895_; 
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_890_, v___x_894_);
v_i_890_ = v___x_895_;
v_b_891_ = v_a_893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_918_, lean_object* v_as_919_, lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_b_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_918_, v_as_919_, v_sz_boxed_923_, v_i_boxed_924_, v_b_922_);
lean_dec_ref(v_as_919_);
lean_dec(v_name_918_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_926_, lean_object* v_self_927_){
_start:
{
lean_object* v_packages_928_; lean_object* v___x_929_; lean_object* v___x_930_; size_t v_sz_931_; size_t v___x_932_; lean_object* v___x_933_; lean_object* v_fst_934_; 
v_packages_928_ = lean_ctor_get(v_self_927_, 5);
v___x_929_ = lean_box(0);
v___x_930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_931_ = lean_array_size(v_packages_928_);
v___x_932_ = ((size_t)0ULL);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_926_, v_packages_928_, v_sz_931_, v___x_932_, v___x_930_);
v_fst_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_fst_934_);
lean_dec_ref(v___x_933_);
if (lean_obj_tag(v_fst_934_) == 0)
{
return v___x_929_;
}
else
{
lean_object* v_val_935_; 
v_val_935_ = lean_ctor_get(v_fst_934_, 0);
lean_inc(v_val_935_);
lean_dec_ref(v_fst_934_);
return v_val_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_936_, lean_object* v_self_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lake_Workspace_findLeanLib_x3f(v_name_936_, v_self_937_);
lean_dec_ref(v_self_937_);
lean_dec(v_name_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_939_, lean_object* v_as_940_, size_t v_sz_941_, size_t v_i_942_, lean_object* v_b_943_){
_start:
{
lean_object* v_a_945_; uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_lt(v_i_942_, v_sz_941_);
if (v___x_949_ == 0)
{
return v_b_943_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_a_952_; lean_object* v___x_953_; 
lean_dec_ref(v_b_943_);
v___x_950_ = lean_box(0);
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_952_ = lean_array_uget_borrowed(v_as_940_, v_i_942_);
v___x_953_ = l_Lake_Package_findTargetDecl_x3f(v_name_939_, v_a_952_);
if (lean_obj_tag(v___x_953_) == 0)
{
v_a_945_ = v___x_951_;
goto v___jp_944_;
}
else
{
lean_object* v_val_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_969_; 
v_val_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_969_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_969_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_val_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_969_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_name_958_; lean_object* v_kind_959_; lean_object* v_config_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_name_958_ = lean_ctor_get(v_val_954_, 1);
lean_inc(v_name_958_);
v_kind_959_ = lean_ctor_get(v_val_954_, 2);
lean_inc(v_kind_959_);
v_config_960_ = lean_ctor_get(v_val_954_, 3);
lean_inc(v_config_960_);
lean_dec(v_val_954_);
v___x_961_ = l_Lake_LeanExe_keyword;
v___x_962_ = lean_name_eq(v_kind_959_, v___x_961_);
lean_dec(v_kind_959_);
if (v___x_962_ == 0)
{
lean_dec(v_config_960_);
lean_dec(v_name_958_);
lean_del_object(v___x_956_);
v_a_945_ = v___x_951_;
goto v___jp_944_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_965_; 
lean_inc(v_a_952_);
v___x_963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_963_, 0, v_a_952_);
lean_ctor_set(v___x_963_, 1, v_name_958_);
lean_ctor_set(v___x_963_, 2, v_config_960_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_963_);
v___x_965_ = v___x_956_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_968_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_950_);
return v___x_967_;
}
}
}
}
}
v___jp_944_:
{
size_t v___x_946_; size_t v___x_947_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_942_, v___x_946_);
v_i_942_ = v___x_947_;
v_b_943_ = v_a_945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_970_, lean_object* v_as_971_, lean_object* v_sz_972_, lean_object* v_i_973_, lean_object* v_b_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_972_);
lean_dec(v_sz_972_);
v_i_boxed_976_ = lean_unbox_usize(v_i_973_);
lean_dec(v_i_973_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_970_, v_as_971_, v_sz_boxed_975_, v_i_boxed_976_, v_b_974_);
lean_dec_ref(v_as_971_);
lean_dec(v_name_970_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_978_, lean_object* v_self_979_){
_start:
{
lean_object* v_packages_980_; lean_object* v___x_981_; lean_object* v___x_982_; size_t v_sz_983_; size_t v___x_984_; lean_object* v___x_985_; lean_object* v_fst_986_; 
v_packages_980_ = lean_ctor_get(v_self_979_, 5);
v___x_981_ = lean_box(0);
v___x_982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_983_ = lean_array_size(v_packages_980_);
v___x_984_ = ((size_t)0ULL);
v___x_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_978_, v_packages_980_, v_sz_983_, v___x_984_, v___x_982_);
v_fst_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_fst_986_);
lean_dec_ref(v___x_985_);
if (lean_obj_tag(v_fst_986_) == 0)
{
return v___x_981_;
}
else
{
lean_object* v_val_987_; 
v_val_987_ = lean_ctor_get(v_fst_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref(v_fst_986_);
return v_val_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_988_, lean_object* v_self_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lake_Workspace_findLeanExe_x3f(v_name_988_, v_self_989_);
lean_dec_ref(v_self_989_);
lean_dec(v_name_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_991_, lean_object* v_as_992_, size_t v_sz_993_, size_t v_i_994_, lean_object* v_b_995_){
_start:
{
lean_object* v_a_997_; uint8_t v___x_1001_; 
v___x_1001_ = lean_usize_dec_lt(v_i_994_, v_sz_993_);
if (v___x_1001_ == 0)
{
return v_b_995_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_a_1004_; lean_object* v___x_1005_; 
lean_dec_ref(v_b_995_);
v___x_1002_ = lean_box(0);
v___x_1003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_1004_ = lean_array_uget_borrowed(v_as_992_, v_i_994_);
v___x_1005_ = l_Lake_Package_findTargetDecl_x3f(v_name_991_, v_a_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
v_a_997_ = v___x_1003_;
goto v___jp_996_;
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1021_; 
v_val_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1021_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_val_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1021_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_name_1010_; lean_object* v_kind_1011_; lean_object* v_config_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_name_1010_ = lean_ctor_get(v_val_1006_, 1);
lean_inc(v_name_1010_);
v_kind_1011_ = lean_ctor_get(v_val_1006_, 2);
lean_inc(v_kind_1011_);
v_config_1012_ = lean_ctor_get(v_val_1006_, 3);
lean_inc(v_config_1012_);
lean_dec(v_val_1006_);
v___x_1013_ = l_Lake_ExternLib_keyword;
v___x_1014_ = lean_name_eq(v_kind_1011_, v___x_1013_);
lean_dec(v_kind_1011_);
if (v___x_1014_ == 0)
{
lean_dec(v_config_1012_);
lean_dec(v_name_1010_);
lean_del_object(v___x_1008_);
v_a_997_ = v___x_1003_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_inc(v_a_1004_);
v___x_1015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1015_, 0, v_a_1004_);
lean_ctor_set(v___x_1015_, 1, v_name_1010_);
lean_ctor_set(v___x_1015_, 2, v_config_1012_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1015_);
v___x_1017_ = v___x_1008_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_1002_);
return v___x_1019_;
}
}
}
}
}
v___jp_996_:
{
size_t v___x_998_; size_t v___x_999_; 
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_add(v_i_994_, v___x_998_);
v_i_994_ = v___x_999_;
v_b_995_ = v_a_997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_1022_, lean_object* v_as_1023_, lean_object* v_sz_1024_, lean_object* v_i_1025_, lean_object* v_b_1026_){
_start:
{
size_t v_sz_boxed_1027_; size_t v_i_boxed_1028_; lean_object* v_res_1029_; 
v_sz_boxed_1027_ = lean_unbox_usize(v_sz_1024_);
lean_dec(v_sz_1024_);
v_i_boxed_1028_ = lean_unbox_usize(v_i_1025_);
lean_dec(v_i_1025_);
v_res_1029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_1022_, v_as_1023_, v_sz_boxed_1027_, v_i_boxed_1028_, v_b_1026_);
lean_dec_ref(v_as_1023_);
lean_dec(v_name_1022_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_1030_, lean_object* v_self_1031_){
_start:
{
lean_object* v_packages_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_1037_; lean_object* v_fst_1038_; 
v_packages_1032_ = lean_ctor_get(v_self_1031_, 5);
v___x_1033_ = lean_box(0);
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_1035_ = lean_array_size(v_packages_1032_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_1030_, v_packages_1032_, v_sz_1035_, v___x_1036_, v___x_1034_);
v_fst_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_fst_1038_);
lean_dec_ref(v___x_1037_);
if (lean_obj_tag(v_fst_1038_) == 0)
{
return v___x_1033_;
}
else
{
lean_object* v_val_1039_; 
v_val_1039_ = lean_ctor_get(v_fst_1038_, 0);
lean_inc(v_val_1039_);
lean_dec_ref(v_fst_1038_);
return v_val_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_1040_, lean_object* v_self_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lake_Workspace_findExternLib_x3f(v_name_1040_, v_self_1041_);
lean_dec_ref(v_self_1041_);
lean_dec(v_name_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_1043_, lean_object* v_f_1044_){
_start:
{
if (lean_obj_tag(v_a_1043_) == 0)
{
lean_object* v___x_1045_; 
lean_dec(v_f_1044_);
v___x_1045_ = lean_box(0);
return v___x_1045_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v_val_1046_ = lean_ctor_get(v_a_1043_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1048_ = v_a_1043_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_val_1046_);
lean_dec(v_a_1043_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1050_ = lean_apply_1(v_f_1044_, v_val_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
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
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_1055_, lean_object* v_00_u03b2_1056_, lean_object* v_a_1057_, lean_object* v_f_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_1057_, v_f_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_a_1060_);
lean_ctor_set(v___x_1062_, 1, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_1066_, lean_object* v_as_1067_, size_t v_sz_1068_, size_t v_i_1069_, lean_object* v_b_1070_){
_start:
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_usize_dec_lt(v_i_1069_, v_sz_1068_);
if (v___x_1071_ == 0)
{
return v_b_1070_;
}
else
{
lean_object* v___x_1072_; lean_object* v_a_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v_b_1070_);
v___x_1072_ = lean_box(0);
v_a_1073_ = lean_array_uget_borrowed(v_as_1067_, v_i_1069_);
lean_inc(v_a_1073_);
v___f_1074_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_1074_, 0, v_a_1073_);
v___x_1075_ = l_Lake_Package_findTargetConfig_x3f(v_name_1066_, v_a_1073_);
v___x_1076_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_1075_, v___f_1074_);
if (lean_obj_tag(v___x_1076_) == 1)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1072_);
return v___x_1078_;
}
else
{
lean_object* v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; 
lean_dec(v___x_1076_);
v___x_1079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_add(v_i_1069_, v___x_1080_);
v_i_1069_ = v___x_1081_;
v_b_1070_ = v___x_1079_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_1083_, lean_object* v_as_1084_, lean_object* v_sz_1085_, lean_object* v_i_1086_, lean_object* v_b_1087_){
_start:
{
size_t v_sz_boxed_1088_; size_t v_i_boxed_1089_; lean_object* v_res_1090_; 
v_sz_boxed_1088_ = lean_unbox_usize(v_sz_1085_);
lean_dec(v_sz_1085_);
v_i_boxed_1089_ = lean_unbox_usize(v_i_1086_);
lean_dec(v_i_1086_);
v_res_1090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_1083_, v_as_1084_, v_sz_boxed_1088_, v_i_boxed_1089_, v_b_1087_);
lean_dec_ref(v_as_1084_);
lean_dec(v_name_1083_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_1091_, lean_object* v_self_1092_){
_start:
{
lean_object* v_packages_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; size_t v_sz_1096_; size_t v___x_1097_; lean_object* v___x_1098_; lean_object* v_fst_1099_; 
v_packages_1093_ = lean_ctor_get(v_self_1092_, 5);
v___x_1094_ = lean_box(0);
v___x_1095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_1096_ = lean_array_size(v_packages_1093_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_1091_, v_packages_1093_, v_sz_1096_, v___x_1097_, v___x_1095_);
v_fst_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_fst_1099_);
lean_dec_ref(v___x_1098_);
if (lean_obj_tag(v_fst_1099_) == 0)
{
return v___x_1094_;
}
else
{
lean_object* v_val_1100_; 
v_val_1100_ = lean_ctor_get(v_fst_1099_, 0);
lean_inc(v_val_1100_);
lean_dec_ref(v_fst_1099_);
return v_val_1100_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_1101_, lean_object* v_self_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_1101_, v_self_1102_);
lean_dec_ref(v_self_1102_);
lean_dec(v_name_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_1104_, lean_object* v_x_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1104_);
lean_ctor_set(v___x_1106_, 1, v_x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_1107_, lean_object* v_as_1108_, size_t v_sz_1109_, size_t v_i_1110_, lean_object* v_b_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1110_, v_sz_1109_);
if (v___x_1112_ == 0)
{
return v_b_1111_;
}
else
{
lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v_b_1111_);
v___x_1113_ = lean_box(0);
v_a_1114_ = lean_array_uget_borrowed(v_as_1108_, v_i_1110_);
lean_inc(v_a_1114_);
v___f_1115_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1115_, 0, v_a_1114_);
v___x_1116_ = l_Lake_Package_findTargetDecl_x3f(v_name_1107_, v_a_1114_);
v___x_1117_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_1116_, v___f_1115_);
if (lean_obj_tag(v___x_1117_) == 1)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___x_1113_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; 
lean_dec(v___x_1117_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_1121_ = ((size_t)1ULL);
v___x_1122_ = lean_usize_add(v_i_1110_, v___x_1121_);
v_i_1110_ = v___x_1122_;
v_b_1111_ = v___x_1120_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_1124_, lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_){
_start:
{
size_t v_sz_boxed_1129_; size_t v_i_boxed_1130_; lean_object* v_res_1131_; 
v_sz_boxed_1129_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1130_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_1124_, v_as_1125_, v_sz_boxed_1129_, v_i_boxed_1130_, v_b_1128_);
lean_dec_ref(v_as_1125_);
lean_dec(v_name_1124_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_1132_, lean_object* v_self_1133_){
_start:
{
lean_object* v_packages_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; lean_object* v_fst_1140_; 
v_packages_1134_ = lean_ctor_get(v_self_1133_, 5);
v___x_1135_ = lean_box(0);
v___x_1136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_1137_ = lean_array_size(v_packages_1134_);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_1132_, v_packages_1134_, v_sz_1137_, v___x_1138_, v___x_1136_);
v_fst_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_fst_1140_);
lean_dec_ref(v___x_1139_);
if (lean_obj_tag(v_fst_1140_) == 0)
{
return v___x_1135_;
}
else
{
lean_object* v_val_1141_; 
v_val_1141_ = lean_ctor_get(v_fst_1140_, 0);
lean_inc(v_val_1141_);
lean_dec_ref(v_fst_1140_);
return v_val_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_1142_, lean_object* v_self_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_1142_, v_self_1143_);
lean_dec_ref(v_self_1143_);
lean_dec(v_name_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_1145_, lean_object* v_cfg_1146_, lean_object* v_self_1147_){
_start:
{
lean_object* v_root_1148_; lean_object* v_lakeEnv_1149_; lean_object* v_lakeConfig_1150_; lean_object* v_lakeCache_1151_; lean_object* v_lakeArgs_x3f_1152_; lean_object* v_packages_1153_; lean_object* v_packageMap_1154_; lean_object* v_facetConfigs_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v_root_1148_ = lean_ctor_get(v_self_1147_, 0);
v_lakeEnv_1149_ = lean_ctor_get(v_self_1147_, 1);
v_lakeConfig_1150_ = lean_ctor_get(v_self_1147_, 2);
v_lakeCache_1151_ = lean_ctor_get(v_self_1147_, 3);
v_lakeArgs_x3f_1152_ = lean_ctor_get(v_self_1147_, 4);
v_packages_1153_ = lean_ctor_get(v_self_1147_, 5);
v_packageMap_1154_ = lean_ctor_get(v_self_1147_, 6);
v_facetConfigs_1155_ = lean_ctor_get(v_self_1147_, 7);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_self_1147_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1157_ = v_self_1147_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_facetConfigs_1155_);
lean_inc(v_packageMap_1154_);
lean_inc(v_packages_1153_);
lean_inc(v_lakeArgs_x3f_1152_);
lean_inc(v_lakeCache_1151_);
lean_inc(v_lakeConfig_1150_);
lean_inc(v_lakeEnv_1149_);
lean_inc(v_root_1148_);
lean_dec(v_self_1147_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Workspace_addPackage_spec__0___redArg(v_name_1145_, v_cfg_1146_, v_facetConfigs_1155_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 7, v___x_1159_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_root_1148_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_lakeEnv_1149_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_lakeConfig_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_lakeCache_1151_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_lakeArgs_x3f_1152_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_packages_1153_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_packageMap_1154_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(lean_object* v_t_1164_, lean_object* v_k_1165_){
_start:
{
if (lean_obj_tag(v_t_1164_) == 0)
{
lean_object* v_k_1166_; lean_object* v_v_1167_; lean_object* v_l_1168_; lean_object* v_r_1169_; uint8_t v___x_1170_; 
v_k_1166_ = lean_ctor_get(v_t_1164_, 1);
v_v_1167_ = lean_ctor_get(v_t_1164_, 2);
v_l_1168_ = lean_ctor_get(v_t_1164_, 3);
v_r_1169_ = lean_ctor_get(v_t_1164_, 4);
v___x_1170_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1165_, v_k_1166_);
switch(v___x_1170_)
{
case 0:
{
v_t_1164_ = v_l_1168_;
goto _start;
}
case 1:
{
lean_object* v___x_1172_; 
lean_inc(v_v_1167_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_v_1167_);
return v___x_1172_;
}
default: 
{
v_t_1164_ = v_r_1169_;
goto _start;
}
}
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_box(0);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg___boxed(lean_object* v_t_1175_, lean_object* v_k_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(v_t_1175_, v_k_1176_);
lean_dec(v_k_1176_);
lean_dec(v_t_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_1178_, lean_object* v_self_1179_){
_start:
{
lean_object* v_facetConfigs_1180_; lean_object* v___x_1181_; 
v_facetConfigs_1180_ = lean_ctor_get(v_self_1179_, 7);
v___x_1181_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(v_facetConfigs_1180_, v_name_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_1182_, lean_object* v_self_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1182_, v_self_1183_);
lean_dec_ref(v_self_1183_);
lean_dec(v_name_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0(lean_object* v_00_u03b2_1185_, lean_object* v_inst_1186_, lean_object* v_t_1187_, lean_object* v_k_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___redArg(v_t_1187_, v_k_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0___boxed(lean_object* v_00_u03b2_1190_, lean_object* v_inst_1191_, lean_object* v_t_1192_, lean_object* v_k_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Workspace_findFacetConfig_x3f_spec__0(v_00_u03b2_1190_, v_inst_1191_, v_t_1192_, v_k_1193_);
lean_dec(v_k_1193_);
lean_dec(v_t_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_1195_, lean_object* v_cfg_1196_, lean_object* v_self_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lake_Workspace_addFacetConfig(v_name_1195_, v_cfg_1196_, v_self_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_1199_, lean_object* v_self_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1199_, v_self_1200_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
else
{
lean_object* v_val_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_val_1203_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_val_1203_);
lean_dec_ref(v___x_1201_);
v___x_1204_ = l_Lake_Module_keyword;
v___x_1205_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1204_, v_val_1203_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1206_, lean_object* v_self_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1206_, v_self_1207_);
lean_dec_ref(v_self_1207_);
lean_dec(v_name_1206_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1209_, lean_object* v_cfg_1210_, lean_object* v_self_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lake_Workspace_addFacetConfig(v_name_1209_, v_cfg_1210_, v_self_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1213_, lean_object* v_self_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1213_, v_self_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_box(0);
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_val_1217_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_val_1217_);
lean_dec_ref(v___x_1215_);
v___x_1218_ = l_Lake_Package_keyword;
v___x_1219_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1218_, v_val_1217_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1220_, lean_object* v_self_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1220_, v_self_1221_);
lean_dec_ref(v_self_1221_);
lean_dec(v_name_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1223_, lean_object* v_cfg_1224_, lean_object* v_self_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lake_Workspace_addFacetConfig(v_name_1223_, v_cfg_1224_, v_self_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1227_, lean_object* v_self_1228_){
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
v___x_1232_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1233_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1232_, v_val_1231_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1234_, lean_object* v_self_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1234_, v_self_1235_);
lean_dec_ref(v_self_1235_);
lean_dec(v_name_1234_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1237_, size_t v_i_1238_, size_t v_stop_1239_, lean_object* v_b_1240_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = lean_usize_dec_eq(v_i_1238_, v_stop_1239_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v_config_1243_; lean_object* v_dir_1244_; lean_object* v_buildDir_1245_; lean_object* v_binDir_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; size_t v___x_1252_; size_t v___x_1253_; 
v___x_1242_ = lean_array_uget_borrowed(v_as_1237_, v_i_1238_);
v_config_1243_ = lean_ctor_get(v___x_1242_, 6);
v_dir_1244_ = lean_ctor_get(v___x_1242_, 4);
v_buildDir_1245_ = lean_ctor_get(v_config_1243_, 5);
v_binDir_1246_ = lean_ctor_get(v_config_1243_, 8);
lean_inc_ref(v_buildDir_1245_);
v___x_1247_ = l_System_FilePath_normalize(v_buildDir_1245_);
lean_inc_ref(v_dir_1244_);
v___x_1248_ = l_Lake_joinRelative(v_dir_1244_, v___x_1247_);
lean_inc_ref(v_binDir_1246_);
v___x_1249_ = l_System_FilePath_normalize(v_binDir_1246_);
v___x_1250_ = l_Lake_joinRelative(v___x_1248_, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_b_1240_);
v___x_1252_ = ((size_t)1ULL);
v___x_1253_ = lean_usize_add(v_i_1238_, v___x_1252_);
v_i_1238_ = v___x_1253_;
v_b_1240_ = v___x_1251_;
goto _start;
}
else
{
return v_b_1240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1255_, lean_object* v_i_1256_, lean_object* v_stop_1257_, lean_object* v_b_1258_){
_start:
{
size_t v_i_boxed_1259_; size_t v_stop_boxed_1260_; lean_object* v_res_1261_; 
v_i_boxed_1259_ = lean_unbox_usize(v_i_1256_);
lean_dec(v_i_1256_);
v_stop_boxed_1260_ = lean_unbox_usize(v_stop_1257_);
lean_dec(v_stop_1257_);
v_res_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1255_, v_i_boxed_1259_, v_stop_boxed_1260_, v_b_1258_);
lean_dec_ref(v_as_1255_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1262_){
_start:
{
lean_object* v_packages_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_packages_1263_ = lean_ctor_get(v_self_1262_, 5);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_array_get_size(v_packages_1263_);
v___x_1267_ = lean_nat_dec_lt(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
return v___x_1264_;
}
else
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_le(v___x_1266_, v___x_1266_);
if (v___x_1268_ == 0)
{
if (v___x_1267_ == 0)
{
return v___x_1264_;
}
else
{
size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((size_t)0ULL);
v___x_1270_ = lean_usize_of_nat(v___x_1266_);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1263_, v___x_1269_, v___x_1270_, v___x_1264_);
return v___x_1271_;
}
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = lean_usize_of_nat(v___x_1266_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1263_, v___x_1272_, v___x_1273_, v___x_1264_);
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lake_Workspace_binPath(v_self_1275_);
lean_dec_ref(v_self_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1277_, size_t v_i_1278_, size_t v_stop_1279_, lean_object* v_b_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_eq(v_i_1278_, v_stop_1279_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v_config_1283_; lean_object* v_dir_1284_; lean_object* v_buildDir_1285_; lean_object* v_leanLibDir_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; 
v___x_1282_ = lean_array_uget_borrowed(v_as_1277_, v_i_1278_);
v_config_1283_ = lean_ctor_get(v___x_1282_, 6);
v_dir_1284_ = lean_ctor_get(v___x_1282_, 4);
v_buildDir_1285_ = lean_ctor_get(v_config_1283_, 5);
v_leanLibDir_1286_ = lean_ctor_get(v_config_1283_, 6);
lean_inc_ref(v_buildDir_1285_);
v___x_1287_ = l_System_FilePath_normalize(v_buildDir_1285_);
lean_inc_ref(v_dir_1284_);
v___x_1288_ = l_Lake_joinRelative(v_dir_1284_, v___x_1287_);
lean_inc_ref(v_leanLibDir_1286_);
v___x_1289_ = l_System_FilePath_normalize(v_leanLibDir_1286_);
v___x_1290_ = l_Lake_joinRelative(v___x_1288_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_b_1280_);
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_add(v_i_1278_, v___x_1292_);
v_i_1278_ = v___x_1293_;
v_b_1280_ = v___x_1291_;
goto _start;
}
else
{
return v_b_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1295_, lean_object* v_i_1296_, lean_object* v_stop_1297_, lean_object* v_b_1298_){
_start:
{
size_t v_i_boxed_1299_; size_t v_stop_boxed_1300_; lean_object* v_res_1301_; 
v_i_boxed_1299_ = lean_unbox_usize(v_i_1296_);
lean_dec(v_i_1296_);
v_stop_boxed_1300_ = lean_unbox_usize(v_stop_1297_);
lean_dec(v_stop_1297_);
v_res_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1295_, v_i_boxed_1299_, v_stop_boxed_1300_, v_b_1298_);
lean_dec_ref(v_as_1295_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1302_){
_start:
{
lean_object* v_packages_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_packages_1303_ = lean_ctor_get(v_self_1302_, 5);
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_array_get_size(v_packages_1303_);
v___x_1307_ = lean_nat_dec_lt(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
return v___x_1304_;
}
else
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_nat_dec_le(v___x_1306_, v___x_1306_);
if (v___x_1308_ == 0)
{
if (v___x_1307_ == 0)
{
return v___x_1304_;
}
else
{
size_t v___x_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = ((size_t)0ULL);
v___x_1310_ = lean_usize_of_nat(v___x_1306_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1303_, v___x_1309_, v___x_1310_, v___x_1304_);
return v___x_1311_;
}
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1306_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1303_, v___x_1312_, v___x_1313_, v___x_1304_);
return v___x_1314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* v_self_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_Workspace_leanPath(v_self_1315_);
lean_dec_ref(v_self_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1317_, lean_object* v_as_1318_, size_t v_i_1319_, size_t v_stop_1320_, lean_object* v_b_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_eq(v_i_1319_, v_stop_1320_);
if (v___x_1322_ == 0)
{
size_t v___x_1323_; size_t v___x_1324_; lean_object* v___x_1325_; lean_object* v_kind_1326_; lean_object* v_config_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1323_ = ((size_t)1ULL);
v___x_1324_ = lean_usize_sub(v_i_1319_, v___x_1323_);
v___x_1325_ = lean_array_uget_borrowed(v_as_1318_, v___x_1324_);
v_kind_1326_ = lean_ctor_get(v___x_1325_, 2);
v_config_1327_ = lean_ctor_get(v___x_1325_, 3);
v___x_1328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1329_ = lean_name_eq(v_kind_1326_, v___x_1328_);
if (v___x_1329_ == 0)
{
v_i_1319_ = v___x_1324_;
goto _start;
}
else
{
lean_object* v_config_1331_; lean_object* v_dir_1332_; lean_object* v_srcDir_1333_; lean_object* v_srcDir_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v_config_1331_ = lean_ctor_get(v_x2_1317_, 6);
v_dir_1332_ = lean_ctor_get(v_x2_1317_, 4);
v_srcDir_1333_ = lean_ctor_get(v_config_1331_, 4);
v_srcDir_1334_ = lean_ctor_get(v_config_1327_, 1);
lean_inc_ref(v_srcDir_1333_);
v___x_1335_ = l_System_FilePath_normalize(v_srcDir_1333_);
lean_inc_ref(v_dir_1332_);
v___x_1336_ = l_Lake_joinRelative(v_dir_1332_, v___x_1335_);
lean_inc_ref(v_srcDir_1334_);
v___x_1337_ = l_Lake_joinRelative(v___x_1336_, v_srcDir_1334_);
v___x_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v_b_1321_);
v_i_1319_ = v___x_1324_;
v_b_1321_ = v___x_1338_;
goto _start;
}
}
else
{
lean_dec_ref(v_x2_1317_);
return v_b_1321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1340_, lean_object* v_as_1341_, lean_object* v_i_1342_, lean_object* v_stop_1343_, lean_object* v_b_1344_){
_start:
{
size_t v_i_boxed_1345_; size_t v_stop_boxed_1346_; lean_object* v_res_1347_; 
v_i_boxed_1345_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_stop_boxed_1346_ = lean_unbox_usize(v_stop_1343_);
lean_dec(v_stop_1343_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1340_, v_as_1341_, v_i_boxed_1345_, v_stop_boxed_1346_, v_b_1344_);
lean_dec_ref(v_as_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1348_, size_t v_i_1349_, size_t v_stop_1350_, lean_object* v_b_1351_){
_start:
{
lean_object* v___y_1353_; uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_eq(v_i_1349_, v_stop_1350_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v_targetDecls_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1358_ = lean_array_uget_borrowed(v_as_1348_, v_i_1349_);
v_targetDecls_1359_ = lean_ctor_get(v___x_1358_, 13);
v___x_1360_ = lean_array_get_size(v_targetDecls_1359_);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_nat_dec_lt(v___x_1361_, v___x_1360_);
if (v___x_1362_ == 0)
{
v___y_1353_ = v_b_1351_;
goto v___jp_1352_;
}
else
{
size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_usize_of_nat(v___x_1360_);
v___x_1364_ = ((size_t)0ULL);
lean_inc(v___x_1358_);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1358_, v_targetDecls_1359_, v___x_1363_, v___x_1364_, v_b_1351_);
v___y_1353_ = v___x_1365_;
goto v___jp_1352_;
}
}
else
{
return v_b_1351_;
}
v___jp_1352_:
{
size_t v___x_1354_; size_t v___x_1355_; 
v___x_1354_ = ((size_t)1ULL);
v___x_1355_ = lean_usize_add(v_i_1349_, v___x_1354_);
v_i_1349_ = v___x_1355_;
v_b_1351_ = v___y_1353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1366_, lean_object* v_i_1367_, lean_object* v_stop_1368_, lean_object* v_b_1369_){
_start:
{
size_t v_i_boxed_1370_; size_t v_stop_boxed_1371_; lean_object* v_res_1372_; 
v_i_boxed_1370_ = lean_unbox_usize(v_i_1367_);
lean_dec(v_i_1367_);
v_stop_boxed_1371_ = lean_unbox_usize(v_stop_1368_);
lean_dec(v_stop_1368_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1366_, v_i_boxed_1370_, v_stop_boxed_1371_, v_b_1369_);
lean_dec_ref(v_as_1366_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1373_){
_start:
{
lean_object* v_packages_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_packages_1374_ = lean_ctor_get(v_self_1373_, 5);
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_array_get_size(v_packages_1374_);
v___x_1378_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
return v___x_1375_;
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_nat_dec_le(v___x_1377_, v___x_1377_);
if (v___x_1379_ == 0)
{
if (v___x_1378_ == 0)
{
return v___x_1375_;
}
else
{
size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = lean_usize_of_nat(v___x_1377_);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1374_, v___x_1380_, v___x_1381_, v___x_1375_);
return v___x_1382_;
}
}
else
{
size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = lean_usize_of_nat(v___x_1377_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1374_, v___x_1383_, v___x_1384_, v___x_1375_);
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lake_Workspace_leanSrcPath(v_self_1386_);
lean_dec_ref(v_self_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1388_, size_t v_i_1389_, size_t v_stop_1390_, lean_object* v_b_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_usize_dec_eq(v_i_1389_, v_stop_1390_);
if (v___x_1392_ == 0)
{
size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; lean_object* v_config_1396_; lean_object* v_dir_1397_; lean_object* v_buildDir_1398_; lean_object* v_nativeLibDir_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_sub(v_i_1389_, v___x_1393_);
v___x_1395_ = lean_array_uget_borrowed(v_as_1388_, v___x_1394_);
v_config_1396_ = lean_ctor_get(v___x_1395_, 6);
v_dir_1397_ = lean_ctor_get(v___x_1395_, 4);
v_buildDir_1398_ = lean_ctor_get(v_config_1396_, 5);
v_nativeLibDir_1399_ = lean_ctor_get(v_config_1396_, 7);
lean_inc_ref(v_buildDir_1398_);
v___x_1400_ = l_System_FilePath_normalize(v_buildDir_1398_);
lean_inc_ref(v_dir_1397_);
v___x_1401_ = l_Lake_joinRelative(v_dir_1397_, v___x_1400_);
lean_inc_ref(v_nativeLibDir_1399_);
v___x_1402_ = l_System_FilePath_normalize(v_nativeLibDir_1399_);
v___x_1403_ = l_Lake_joinRelative(v___x_1401_, v___x_1402_);
v___x_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v_b_1391_);
v_i_1389_ = v___x_1394_;
v_b_1391_ = v___x_1404_;
goto _start;
}
else
{
return v_b_1391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1406_, lean_object* v_i_1407_, lean_object* v_stop_1408_, lean_object* v_b_1409_){
_start:
{
size_t v_i_boxed_1410_; size_t v_stop_boxed_1411_; lean_object* v_res_1412_; 
v_i_boxed_1410_ = lean_unbox_usize(v_i_1407_);
lean_dec(v_i_1407_);
v_stop_boxed_1411_ = lean_unbox_usize(v_stop_1408_);
lean_dec(v_stop_1408_);
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1406_, v_i_boxed_1410_, v_stop_boxed_1411_, v_b_1409_);
lean_dec_ref(v_as_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1413_){
_start:
{
lean_object* v_packages_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_packages_1414_ = lean_ctor_get(v_self_1413_, 5);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_array_get_size(v_packages_1414_);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_nat_dec_lt(v___x_1417_, v___x_1416_);
if (v___x_1418_ == 0)
{
return v___x_1415_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_usize_of_nat(v___x_1416_);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1414_, v___x_1419_, v___x_1420_, v___x_1415_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lake_Workspace_sharedLibPath(v_self_1422_);
lean_dec_ref(v_self_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1424_){
_start:
{
uint8_t v___x_1425_; 
v___x_1425_ = l_System_Platform_isWindows;
if (v___x_1425_ == 0)
{
lean_object* v_lakeEnv_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_lakeEnv_1426_ = lean_ctor_get(v_self_1424_, 1);
v___x_1427_ = l_Lake_Workspace_binPath(v_self_1424_);
v___x_1428_ = l_Lake_Env_path(v_lakeEnv_1426_);
v___x_1429_ = l_List_appendTR___redArg(v___x_1427_, v___x_1428_);
return v___x_1429_;
}
else
{
lean_object* v_lakeEnv_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_lakeEnv_1430_ = lean_ctor_get(v_self_1424_, 1);
v___x_1431_ = l_Lake_Workspace_binPath(v_self_1424_);
v___x_1432_ = l_Lake_Workspace_sharedLibPath(v_self_1424_);
v___x_1433_ = l_List_appendTR___redArg(v___x_1431_, v___x_1432_);
v___x_1434_ = l_Lake_Env_path(v_lakeEnv_1430_);
v___x_1435_ = l_List_appendTR___redArg(v___x_1433_, v___x_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lake_Workspace_augmentedPath(v_self_1436_);
lean_dec_ref(v_self_1436_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1438_){
_start:
{
lean_object* v_lakeEnv_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_lakeEnv_1439_ = lean_ctor_get(v_self_1438_, 1);
v___x_1440_ = l_Lake_Workspace_leanPath(v_self_1438_);
v___x_1441_ = l_Lake_Env_leanPath(v_lakeEnv_1439_);
v___x_1442_ = l_List_appendTR___redArg(v___x_1440_, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lake_Workspace_augmentedLeanPath(v_self_1443_);
lean_dec_ref(v_self_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1445_){
_start:
{
lean_object* v_lakeEnv_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_lakeEnv_1446_ = lean_ctor_get(v_self_1445_, 1);
v___x_1447_ = l_Lake_Workspace_leanSrcPath(v_self_1445_);
v___x_1448_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1446_);
v___x_1449_ = l_List_appendTR___redArg(v___x_1447_, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1450_);
lean_dec_ref(v_self_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1452_){
_start:
{
lean_object* v_lakeEnv_1453_; lean_object* v_lean_1454_; lean_object* v_initSharedLibPath_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_lakeEnv_1453_ = lean_ctor_get(v_self_1452_, 1);
v_lean_1454_ = lean_ctor_get(v_lakeEnv_1453_, 1);
v_initSharedLibPath_1455_ = lean_ctor_get(v_lakeEnv_1453_, 16);
lean_inc(v_initSharedLibPath_1455_);
v___x_1456_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1454_);
v___x_1457_ = l_Lake_Workspace_sharedLibPath(v_self_1452_);
lean_dec_ref(v_self_1452_);
v___x_1458_ = l_List_appendTR___redArg(v___x_1456_, v___x_1457_);
v___x_1459_ = l_List_appendTR___redArg(v___x_1458_, v_initSharedLibPath_1455_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1475_){
_start:
{
lean_object* v_lakeEnv_1476_; lean_object* v_root_1477_; lean_object* v_lakeCache_1478_; lean_object* v_enableArtifactCache_x3f_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___x_1512_; lean_object* v___y_1514_; uint8_t v_val_1533_; 
v_lakeEnv_1476_ = lean_ctor_get(v_self_1475_, 1);
v_root_1477_ = lean_ctor_get(v_self_1475_, 0);
v_lakeCache_1478_ = lean_ctor_get(v_self_1475_, 3);
v_enableArtifactCache_x3f_1479_ = lean_ctor_get(v_lakeEnv_1476_, 6);
lean_inc_ref(v_lakeEnv_1476_);
v___x_1480_ = l_Lake_Env_baseVars(v_lakeEnv_1476_);
v___x_1481_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1478_);
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_lakeCache_1478_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1512_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
if (lean_obj_tag(v_enableArtifactCache_x3f_1479_) == 0)
{
lean_object* v_config_1536_; lean_object* v_enableArtifactCache_x3f_1537_; 
v_config_1536_ = lean_ctor_get(v_root_1477_, 6);
v_enableArtifactCache_x3f_1537_ = lean_ctor_get(v_config_1536_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1537_) == 1)
{
lean_object* v_val_1538_; uint8_t v___x_1539_; 
v_val_1538_ = lean_ctor_get(v_enableArtifactCache_x3f_1537_, 0);
v___x_1539_ = lean_unbox(v_val_1538_);
v_val_1533_ = v___x_1539_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__11));
v___y_1514_ = v___x_1540_;
goto v___jp_1513_;
}
}
else
{
lean_object* v_val_1541_; uint8_t v___x_1542_; 
v_val_1541_ = lean_ctor_get(v_enableArtifactCache_x3f_1479_, 0);
v___x_1542_ = lean_unbox(v_val_1541_);
v_val_1533_ = v___x_1542_;
goto v___jp_1532_;
}
v___jp_1484_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v_vars_1504_; uint8_t v___x_1505_; 
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1488_);
lean_ctor_set(v___x_1490_, 1, v___y_1489_);
v___x_1491_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1492_ = l_Lake_Workspace_augmentedPath(v_self_1475_);
v___x_1493_ = l_System_SearchPath_toString(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1491_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_unsigned_to_nat(6u);
v___x_1497_ = lean_mk_empty_array_with_capacity(v___x_1496_);
v___x_1498_ = lean_array_push(v___x_1497_, v___x_1483_);
v___x_1499_ = lean_array_push(v___x_1498_, v___y_1487_);
v___x_1500_ = lean_array_push(v___x_1499_, v___y_1486_);
v___x_1501_ = lean_array_push(v___x_1500_, v___y_1485_);
v___x_1502_ = lean_array_push(v___x_1501_, v___x_1490_);
v___x_1503_ = lean_array_push(v___x_1502_, v___x_1495_);
v_vars_1504_ = l_Array_append___redArg(v___x_1480_, v___x_1503_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = l_System_Platform_isWindows;
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1506_ = l_Lake_sharedLibPathEnvVar;
v___x_1507_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1475_);
v___x_1508_ = l_System_SearchPath_toString(v___x_1507_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1506_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_array_push(v_vars_1504_, v___x_1510_);
return v___x_1511_;
}
else
{
lean_dec_ref(v_self_1475_);
return v_vars_1504_;
}
}
v___jp_1513_:
{
lean_object* v_config_1515_; uint8_t v_bootstrap_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_config_1515_ = lean_ctor_get(v_root_1477_, 6);
v_bootstrap_1516_ = lean_ctor_get_uint8(v_config_1515_, sizeof(void*)*26);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1512_);
lean_ctor_set(v___x_1517_, 1, v___y_1514_);
v___x_1518_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1519_ = l_Lake_Workspace_augmentedLeanPath(v_self_1475_);
v___x_1520_ = l_System_SearchPath_toString(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1518_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
v___x_1524_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1475_);
v___x_1525_ = l_System_SearchPath_toString(v___x_1524_);
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
v___x_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1523_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (v_bootstrap_1516_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = l_Lake_Env_leanGithash(v_lakeEnv_1476_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___y_1485_ = v___x_1527_;
v___y_1486_ = v___x_1522_;
v___y_1487_ = v___x_1517_;
v___y_1488_ = v___x_1528_;
v___y_1489_ = v___x_1530_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_box(0);
v___y_1485_ = v___x_1527_;
v___y_1486_ = v___x_1522_;
v___y_1487_ = v___x_1517_;
v___y_1488_ = v___x_1528_;
v___y_1489_ = v___x_1531_;
goto v___jp_1484_;
}
}
v___jp_1532_:
{
if (v_val_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__7));
v___y_1514_ = v___x_1534_;
goto v___jp_1513_;
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__9));
v___y_1514_ = v___x_1535_;
goto v___jp_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1543_, size_t v_i_1544_, size_t v_stop_1545_, lean_object* v_b_1546_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_usize_dec_eq(v_i_1544_, v_stop_1545_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_array_uget_borrowed(v_as_1543_, v_i_1544_);
lean_inc(v___x_1549_);
v___x_1550_ = l_Lake_Package_clean(v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; size_t v___x_1552_; size_t v___x_1553_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = ((size_t)1ULL);
v___x_1553_ = lean_usize_add(v_i_1544_, v___x_1552_);
v_i_1544_ = v___x_1553_;
v_b_1546_ = v_a_1551_;
goto _start;
}
else
{
return v___x_1550_;
}
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v_b_1546_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1556_, lean_object* v_i_1557_, lean_object* v_stop_1558_, lean_object* v_b_1559_, lean_object* v___y_1560_){
_start:
{
size_t v_i_boxed_1561_; size_t v_stop_boxed_1562_; lean_object* v_res_1563_; 
v_i_boxed_1561_ = lean_unbox_usize(v_i_1557_);
lean_dec(v_i_1557_);
v_stop_boxed_1562_ = lean_unbox_usize(v_stop_1558_);
lean_dec(v_stop_1558_);
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1556_, v_i_boxed_1561_, v_stop_boxed_1562_, v_b_1559_);
lean_dec_ref(v_as_1556_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* v_self_1564_){
_start:
{
lean_object* v_packages_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_packages_1566_ = lean_ctor_get(v_self_1564_, 5);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_array_get_size(v_packages_1566_);
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_nat_dec_lt(v___x_1567_, v___x_1568_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
return v___x_1571_;
}
else
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_nat_dec_le(v___x_1568_, v___x_1568_);
if (v___x_1572_ == 0)
{
if (v___x_1570_ == 0)
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1569_);
return v___x_1573_;
}
else
{
size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = lean_usize_of_nat(v___x_1568_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1566_, v___x_1574_, v___x_1575_, v___x_1569_);
return v___x_1576_;
}
}
else
{
size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = lean_usize_of_nat(v___x_1568_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1566_, v___x_1577_, v___x_1578_, v___x_1569_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lake_Workspace_clean(v_self_1580_);
lean_dec_ref(v_self_1580_);
return v_res_1582_;
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

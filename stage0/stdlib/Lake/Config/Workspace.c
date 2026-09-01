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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
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
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lake_FacetConfigMap_get_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lake_Package_isBuildableModule(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Package_keyword;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object* v_self_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lake_defaultLakeDir;
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object* v_self_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lake_Workspace_relLakeDir(v_self_129_);
lean_dec_ref(v_self_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object* v_self_131_){
_start:
{
lean_object* v_packages_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_dir_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_packages_132_ = lean_ctor_get(v_self_131_, 4);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_fget_borrowed(v_packages_132_, v___x_133_);
v_dir_135_ = lean_ctor_get(v___x_134_, 4);
v___x_136_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_135_);
v___x_137_ = l_Lake_joinRelative(v_dir_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir___boxed(lean_object* v_self_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lake_Workspace_lakeDir(v_self_138_);
lean_dec_ref(v_self_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f(lean_object* v_ws_140_){
_start:
{
lean_object* v_lakeEnv_141_; lean_object* v_enableArtifactCache_x3f_142_; 
v_lakeEnv_141_ = lean_ctor_get(v_ws_140_, 0);
v_enableArtifactCache_x3f_142_ = lean_ctor_get(v_lakeEnv_141_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_142_) == 0)
{
lean_object* v_packages_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_config_146_; lean_object* v_enableArtifactCache_x3f_147_; 
v_packages_143_ = lean_ctor_get(v_ws_140_, 4);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_array_fget_borrowed(v_packages_143_, v___x_144_);
v_config_146_ = lean_ctor_get(v___x_145_, 6);
v_enableArtifactCache_x3f_147_ = lean_ctor_get(v_config_146_, 24);
lean_inc(v_enableArtifactCache_x3f_147_);
return v_enableArtifactCache_x3f_147_;
}
else
{
lean_inc_ref(v_enableArtifactCache_x3f_142_);
return v_enableArtifactCache_x3f_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f___boxed(lean_object* v_ws_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lake_Workspace_enableArtifactCache_x3f(v_ws_148_);
lean_dec_ref(v_ws_148_);
return v_res_149_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_enableArtifactCache(lean_object* v_ws_150_){
_start:
{
lean_object* v_lakeEnv_151_; lean_object* v_enableArtifactCache_x3f_152_; 
v_lakeEnv_151_ = lean_ctor_get(v_ws_150_, 0);
v_enableArtifactCache_x3f_152_ = lean_ctor_get(v_lakeEnv_151_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_152_) == 0)
{
lean_object* v_packages_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_config_156_; lean_object* v_enableArtifactCache_x3f_157_; 
v_packages_153_ = lean_ctor_get(v_ws_150_, 4);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_array_fget_borrowed(v_packages_153_, v___x_154_);
v_config_156_ = lean_ctor_get(v___x_155_, 6);
v_enableArtifactCache_x3f_157_ = lean_ctor_get(v_config_156_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
else
{
lean_object* v_val_159_; uint8_t v___x_160_; 
v_val_159_ = lean_ctor_get(v_enableArtifactCache_x3f_157_, 0);
v___x_160_ = lean_unbox(v_val_159_);
return v___x_160_;
}
}
else
{
lean_object* v_val_161_; uint8_t v___x_162_; 
v_val_161_ = lean_ctor_get(v_enableArtifactCache_x3f_152_, 0);
v___x_162_ = lean_unbox(v_val_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache___boxed(lean_object* v_ws_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Lake_Workspace_enableArtifactCache(v_ws_163_);
lean_dec_ref(v_ws_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object* v_ws_166_){
_start:
{
lean_object* v_lakeEnv_167_; lean_object* v_enableArtifactCache_x3f_168_; 
v_lakeEnv_167_ = lean_ctor_get(v_ws_166_, 0);
v_enableArtifactCache_x3f_168_ = lean_ctor_get(v_lakeEnv_167_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_168_) == 0)
{
lean_object* v_packages_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_config_172_; lean_object* v_enableArtifactCache_x3f_173_; 
v_packages_169_ = lean_ctor_get(v_ws_166_, 4);
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_array_fget_borrowed(v_packages_169_, v___x_170_);
v_config_172_ = lean_ctor_get(v___x_171_, 6);
v_enableArtifactCache_x3f_173_ = lean_ctor_get(v_config_172_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_173_) == 0)
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
else
{
lean_object* v_val_175_; uint8_t v___x_176_; 
v_val_175_ = lean_ctor_get(v_enableArtifactCache_x3f_173_, 0);
v___x_176_ = lean_unbox(v_val_175_);
return v___x_176_;
}
}
else
{
lean_object* v_val_177_; uint8_t v___x_178_; 
v_val_177_ = lean_ctor_get(v_enableArtifactCache_x3f_168_, 0);
v___x_178_ = lean_unbox(v_val_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheWritable___boxed(lean_object* v_ws_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_179_);
lean_dec_ref(v_ws_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isRootArtifactCacheEnabled(lean_object* v_ws_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheEnabled___boxed(lean_object* v_ws_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lake_Workspace_isRootArtifactCacheEnabled(v_ws_184_);
lean_dec_ref(v_ws_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f(lean_object* v_ws_187_){
_start:
{
lean_object* v_lakeEnv_188_; lean_object* v_restoreAllArtifacts_x3f_189_; 
v_lakeEnv_188_ = lean_ctor_get(v_ws_187_, 0);
v_restoreAllArtifacts_x3f_189_ = lean_ctor_get(v_lakeEnv_188_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_189_) == 0)
{
lean_object* v_packages_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_config_193_; lean_object* v_restoreAllArtifacts_x3f_194_; 
v_packages_190_ = lean_ctor_get(v_ws_187_, 4);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_array_fget_borrowed(v_packages_190_, v___x_191_);
v_config_193_ = lean_ctor_get(v___x_192_, 6);
v_restoreAllArtifacts_x3f_194_ = lean_ctor_get(v_config_193_, 25);
lean_inc(v_restoreAllArtifacts_x3f_194_);
return v_restoreAllArtifacts_x3f_194_;
}
else
{
lean_inc_ref(v_restoreAllArtifacts_x3f_189_);
return v_restoreAllArtifacts_x3f_189_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(lean_object* v_ws_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lake_Workspace_restoreAllArtifacts_x3f(v_ws_195_);
lean_dec_ref(v_ws_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain(lean_object* v_ws_197_){
_start:
{
lean_object* v_lakeEnv_198_; lean_object* v_toolchain_199_; 
v_lakeEnv_198_ = lean_ctor_get(v_ws_197_, 0);
v_toolchain_199_ = lean_ctor_get(v_lakeEnv_198_, 19);
lean_inc_ref(v_toolchain_199_);
return v_toolchain_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain___boxed(lean_object* v_ws_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_Workspace_cacheToolchain(v_ws_200_);
lean_dec_ref(v_ws_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService(lean_object* v_ws_202_){
_start:
{
lean_object* v_lakeConfig_203_; lean_object* v_defaultCacheService_204_; 
v_lakeConfig_203_ = lean_ctor_get(v_ws_202_, 1);
v_defaultCacheService_204_ = lean_ctor_get(v_lakeConfig_203_, 1);
lean_inc_ref(v_defaultCacheService_204_);
return v_defaultCacheService_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService___boxed(lean_object* v_ws_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_Workspace_defaultCacheService(v_ws_205_);
lean_dec_ref(v_ws_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f(lean_object* v_ws_207_){
_start:
{
lean_object* v_lakeConfig_208_; lean_object* v_defaultCacheUploadService_x3f_209_; 
v_lakeConfig_208_ = lean_ctor_get(v_ws_207_, 1);
v_defaultCacheUploadService_x3f_209_ = lean_ctor_get(v_lakeConfig_208_, 2);
lean_inc(v_defaultCacheUploadService_x3f_209_);
return v_defaultCacheUploadService_x3f_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(lean_object* v_ws_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lake_Workspace_defaultCacheUploadService_x3f(v_ws_210_);
lean_dec_ref(v_ws_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object* v_ws_212_, lean_object* v_service_213_){
_start:
{
lean_object* v_lakeConfig_214_; lean_object* v_cacheServices_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_lakeConfig_214_ = lean_ctor_get(v_ws_212_, 1);
v_cacheServices_215_ = lean_ctor_get(v_lakeConfig_214_, 3);
v___x_216_ = lean_box(0);
v___x_217_ = l_Lean_Name_str___override(v___x_216_, v_service_213_);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_215_, v___x_217_);
lean_dec(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object* v_ws_219_, lean_object* v_service_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lake_Workspace_findCacheService_x3f(v_ws_219_, v_service_220_);
lean_dec_ref(v_ws_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* v_self_222_){
_start:
{
lean_object* v_packages_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_config_226_; lean_object* v_toWorkspaceConfig_227_; lean_object* v___x_228_; 
v_packages_223_ = lean_ctor_get(v_self_222_, 4);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_array_fget_borrowed(v_packages_223_, v___x_224_);
v_config_226_ = lean_ctor_get(v___x_225_, 6);
v_toWorkspaceConfig_227_ = lean_ctor_get(v_config_226_, 0);
lean_inc_ref(v_toWorkspaceConfig_227_);
v___x_228_ = l_System_FilePath_normalize(v_toWorkspaceConfig_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir___boxed(lean_object* v_self_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lake_Workspace_relPkgsDir(v_self_229_);
lean_dec_ref(v_self_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* v_self_231_){
_start:
{
lean_object* v_packages_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_config_235_; lean_object* v_dir_236_; lean_object* v_toWorkspaceConfig_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_packages_232_ = lean_ctor_get(v_self_231_, 4);
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_array_fget_borrowed(v_packages_232_, v___x_233_);
v_config_235_ = lean_ctor_get(v___x_234_, 6);
v_dir_236_ = lean_ctor_get(v___x_234_, 4);
v_toWorkspaceConfig_237_ = lean_ctor_get(v_config_235_, 0);
lean_inc_ref(v_toWorkspaceConfig_237_);
v___x_238_ = l_System_FilePath_normalize(v_toWorkspaceConfig_237_);
lean_inc_ref(v_dir_236_);
v___x_239_ = l_Lake_joinRelative(v_dir_236_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir___boxed(lean_object* v_self_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_Workspace_pkgsDir(v_self_240_);
lean_dec_ref(v_self_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object* v_self_242_){
_start:
{
lean_object* v_packages_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_config_246_; lean_object* v_toLeanConfig_247_; lean_object* v_moreLeanArgs_248_; 
v_packages_243_ = lean_ctor_get(v_self_242_, 4);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_array_fget_borrowed(v_packages_243_, v___x_244_);
v_config_246_ = lean_ctor_get(v___x_245_, 6);
v_toLeanConfig_247_ = lean_ctor_get(v_config_246_, 1);
v_moreLeanArgs_248_ = lean_ctor_get(v_toLeanConfig_247_, 1);
lean_inc_ref(v_moreLeanArgs_248_);
return v_moreLeanArgs_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object* v_self_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lake_Workspace_leanArgs(v_self_249_);
lean_dec_ref(v_self_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* v_self_251_){
_start:
{
lean_object* v_packages_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_config_255_; lean_object* v_toLeanConfig_256_; lean_object* v_leanOptions_257_; lean_object* v___x_258_; 
v_packages_252_ = lean_ctor_get(v_self_251_, 4);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_array_fget_borrowed(v_packages_252_, v___x_253_);
v_config_255_ = lean_ctor_get(v___x_254_, 6);
v_toLeanConfig_256_ = lean_ctor_get(v_config_255_, 1);
v_leanOptions_257_ = lean_ctor_get(v_toLeanConfig_256_, 0);
v___x_258_ = l_Lean_LeanOptions_ofArray(v_leanOptions_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* v_self_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lake_Workspace_leanOptions(v_self_259_);
lean_dec_ref(v_self_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* v_self_261_){
_start:
{
lean_object* v_packages_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_config_265_; lean_object* v_toLeanConfig_266_; lean_object* v_leanOptions_267_; lean_object* v_moreServerOptions_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_packages_262_ = lean_ctor_get(v_self_261_, 4);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_array_fget_borrowed(v_packages_262_, v___x_263_);
v_config_265_ = lean_ctor_get(v___x_264_, 6);
v_toLeanConfig_266_ = lean_ctor_get(v_config_265_, 1);
v_leanOptions_267_ = lean_ctor_get(v_toLeanConfig_266_, 0);
v_moreServerOptions_268_ = lean_ctor_get(v_toLeanConfig_266_, 4);
v___x_269_ = l_Lean_LeanOptions_ofArray(v_leanOptions_267_);
v___x_270_ = l_Lean_LeanOptions_appendArray(v___x_269_, v_moreServerOptions_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* v_self_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lake_Workspace_serverOptions(v_self_271_);
lean_dec_ref(v_self_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object* v_self_273_){
_start:
{
lean_object* v_packages_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_packages_274_ = lean_ctor_get(v_self_273_, 4);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_array_fget_borrowed(v_packages_274_, v___x_275_);
v___x_277_ = l_Lake_Package_defaultTargetRoots(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object* v_self_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lake_Workspace_defaultTargetRoots(v_self_278_);
lean_dec_ref(v_self_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* v_self_280_){
_start:
{
lean_object* v_packages_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_dir_284_; lean_object* v_relManifestFile_285_; lean_object* v___x_286_; 
v_packages_281_ = lean_ctor_get(v_self_280_, 4);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_array_fget_borrowed(v_packages_281_, v___x_282_);
v_dir_284_ = lean_ctor_get(v___x_283_, 4);
v_relManifestFile_285_ = lean_ctor_get(v___x_283_, 9);
lean_inc_ref(v_relManifestFile_285_);
lean_inc_ref(v_dir_284_);
v___x_286_ = l_Lake_joinRelative(v_dir_284_, v_relManifestFile_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile___boxed(lean_object* v_self_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lake_Workspace_manifestFile(v_self_287_);
lean_dec_ref(v_self_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* v_self_290_){
_start:
{
lean_object* v_packages_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_dir_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_packages_291_ = lean_ctor_get(v_self_290_, 4);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_fget_borrowed(v_packages_291_, v___x_292_);
v_dir_294_ = lean_ctor_get(v___x_293_, 4);
v___x_295_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_294_);
v___x_296_ = l_Lake_joinRelative(v_dir_294_, v___x_295_);
v___x_297_ = ((lean_object*)(l_Lake_Workspace_packageOverridesFile___closed__0));
v___x_298_ = l_Lake_joinRelative(v___x_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile___boxed(lean_object* v_self_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lake_Workspace_packageOverridesFile(v_self_299_);
lean_dec_ref(v_self_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object* v_pkg_302_, lean_object* v_self_303_){
_start:
{
lean_object* v_lakeEnv_304_; lean_object* v_lakeConfig_305_; lean_object* v_lakeCache_306_; lean_object* v_lakeArgs_x3f_307_; lean_object* v_packages_308_; lean_object* v_packageMap_309_; lean_object* v_facetConfigs_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_321_; 
v_lakeEnv_304_ = lean_ctor_get(v_self_303_, 0);
v_lakeConfig_305_ = lean_ctor_get(v_self_303_, 1);
v_lakeCache_306_ = lean_ctor_get(v_self_303_, 2);
v_lakeArgs_x3f_307_ = lean_ctor_get(v_self_303_, 3);
v_packages_308_ = lean_ctor_get(v_self_303_, 4);
v_packageMap_309_ = lean_ctor_get(v_self_303_, 5);
v_facetConfigs_310_ = lean_ctor_get(v_self_303_, 6);
v_isSharedCheck_321_ = !lean_is_exclusive(v_self_303_);
if (v_isSharedCheck_321_ == 0)
{
v___x_312_ = v_self_303_;
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_facetConfigs_310_);
lean_inc(v_packageMap_309_);
lean_inc(v_packages_308_);
lean_inc(v_lakeArgs_x3f_307_);
lean_inc(v_lakeCache_306_);
lean_inc(v_lakeConfig_305_);
lean_inc(v_lakeEnv_304_);
lean_dec(v_self_303_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_321_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_keyName_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v_keyName_314_ = lean_ctor_get(v_pkg_302_, 2);
lean_inc(v_keyName_314_);
lean_inc_ref(v_pkg_302_);
v___x_315_ = lean_array_push(v_packages_308_, v_pkg_302_);
v___x_316_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_317_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_316_, v_keyName_314_, v_pkg_302_, v_packageMap_309_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 5, v___x_317_);
lean_ctor_set(v___x_312_, 4, v___x_315_);
v___x_319_ = v___x_312_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_lakeEnv_304_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_lakeConfig_305_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_lakeCache_306_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_lakeArgs_x3f_307_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_320_, 5, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_320_, 6, v_facetConfigs_310_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object* v_pkg_322_, lean_object* v_self_323_, lean_object* v_h__wsIdx_324_, lean_object* v_h__depIdxs_325_){
_start:
{
lean_object* v_lakeEnv_326_; lean_object* v_lakeConfig_327_; lean_object* v_lakeCache_328_; lean_object* v_lakeArgs_x3f_329_; lean_object* v_packages_330_; lean_object* v_packageMap_331_; lean_object* v_facetConfigs_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_343_; 
v_lakeEnv_326_ = lean_ctor_get(v_self_323_, 0);
v_lakeConfig_327_ = lean_ctor_get(v_self_323_, 1);
v_lakeCache_328_ = lean_ctor_get(v_self_323_, 2);
v_lakeArgs_x3f_329_ = lean_ctor_get(v_self_323_, 3);
v_packages_330_ = lean_ctor_get(v_self_323_, 4);
v_packageMap_331_ = lean_ctor_get(v_self_323_, 5);
v_facetConfigs_332_ = lean_ctor_get(v_self_323_, 6);
v_isSharedCheck_343_ = !lean_is_exclusive(v_self_323_);
if (v_isSharedCheck_343_ == 0)
{
v___x_334_ = v_self_323_;
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_facetConfigs_332_);
lean_inc(v_packageMap_331_);
lean_inc(v_packages_330_);
lean_inc(v_lakeArgs_x3f_329_);
lean_inc(v_lakeCache_328_);
lean_inc(v_lakeConfig_327_);
lean_inc(v_lakeEnv_326_);
lean_dec(v_self_323_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_keyName_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v_keyName_336_ = lean_ctor_get(v_pkg_322_, 2);
lean_inc(v_keyName_336_);
lean_inc_ref(v_pkg_322_);
v___x_337_ = lean_array_push(v_packages_330_, v_pkg_322_);
v___x_338_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_339_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_338_, v_keyName_336_, v_pkg_322_, v_packageMap_331_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 5, v___x_339_);
lean_ctor_set(v___x_334_, 4, v___x_337_);
v___x_341_ = v___x_334_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_lakeEnv_326_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_lakeConfig_327_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v_lakeCache_328_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v_lakeArgs_x3f_329_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_342_, 5, v___x_339_);
lean_ctor_set(v_reuseFailAlloc_342_, 6, v_facetConfigs_332_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_346_, lean_object* v_self_347_){
_start:
{
lean_object* v_lakeEnv_348_; lean_object* v_lakeConfig_349_; lean_object* v_lakeCache_350_; lean_object* v_lakeArgs_x3f_351_; lean_object* v_packages_352_; lean_object* v_packageMap_353_; lean_object* v_facetConfigs_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_397_; 
v_lakeEnv_348_ = lean_ctor_get(v_self_347_, 0);
v_lakeConfig_349_ = lean_ctor_get(v_self_347_, 1);
v_lakeCache_350_ = lean_ctor_get(v_self_347_, 2);
v_lakeArgs_x3f_351_ = lean_ctor_get(v_self_347_, 3);
v_packages_352_ = lean_ctor_get(v_self_347_, 4);
v_packageMap_353_ = lean_ctor_get(v_self_347_, 5);
v_facetConfigs_354_ = lean_ctor_get(v_self_347_, 6);
v_isSharedCheck_397_ = !lean_is_exclusive(v_self_347_);
if (v_isSharedCheck_397_ == 0)
{
v___x_356_ = v_self_347_;
v_isShared_357_ = v_isSharedCheck_397_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_facetConfigs_354_);
lean_inc(v_packageMap_353_);
lean_inc(v_packages_352_);
lean_inc(v_lakeArgs_x3f_351_);
lean_inc(v_lakeCache_350_);
lean_inc(v_lakeConfig_349_);
lean_inc(v_lakeEnv_348_);
lean_dec(v_self_347_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_397_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_baseName_358_; lean_object* v_keyName_359_; lean_object* v_origName_360_; lean_object* v_dir_361_; lean_object* v_relDir_362_; lean_object* v_config_363_; lean_object* v_configFile_364_; lean_object* v_relConfigFile_365_; lean_object* v_relManifestFile_366_; lean_object* v_scope_367_; lean_object* v_remoteUrl_368_; lean_object* v_depConfigs_369_; lean_object* v_depPkgs_370_; lean_object* v_targetDecls_371_; lean_object* v_targetDeclMap_372_; lean_object* v_defaultTargets_373_; lean_object* v_scripts_374_; lean_object* v_defaultScripts_375_; lean_object* v_postUpdateHooks_376_; lean_object* v_buildArchive_377_; lean_object* v_testDriver_378_; lean_object* v_lintDriver_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_394_; 
v_baseName_358_ = lean_ctor_get(v_pkg_346_, 1);
v_keyName_359_ = lean_ctor_get(v_pkg_346_, 2);
v_origName_360_ = lean_ctor_get(v_pkg_346_, 3);
v_dir_361_ = lean_ctor_get(v_pkg_346_, 4);
v_relDir_362_ = lean_ctor_get(v_pkg_346_, 5);
v_config_363_ = lean_ctor_get(v_pkg_346_, 6);
v_configFile_364_ = lean_ctor_get(v_pkg_346_, 7);
v_relConfigFile_365_ = lean_ctor_get(v_pkg_346_, 8);
v_relManifestFile_366_ = lean_ctor_get(v_pkg_346_, 9);
v_scope_367_ = lean_ctor_get(v_pkg_346_, 10);
v_remoteUrl_368_ = lean_ctor_get(v_pkg_346_, 11);
v_depConfigs_369_ = lean_ctor_get(v_pkg_346_, 12);
v_depPkgs_370_ = lean_ctor_get(v_pkg_346_, 14);
v_targetDecls_371_ = lean_ctor_get(v_pkg_346_, 15);
v_targetDeclMap_372_ = lean_ctor_get(v_pkg_346_, 16);
v_defaultTargets_373_ = lean_ctor_get(v_pkg_346_, 17);
v_scripts_374_ = lean_ctor_get(v_pkg_346_, 18);
v_defaultScripts_375_ = lean_ctor_get(v_pkg_346_, 19);
v_postUpdateHooks_376_ = lean_ctor_get(v_pkg_346_, 20);
v_buildArchive_377_ = lean_ctor_get(v_pkg_346_, 21);
v_testDriver_378_ = lean_ctor_get(v_pkg_346_, 22);
v_lintDriver_379_ = lean_ctor_get(v_pkg_346_, 23);
v_isSharedCheck_394_ = !lean_is_exclusive(v_pkg_346_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; lean_object* v_unused_396_; 
v_unused_395_ = lean_ctor_get(v_pkg_346_, 13);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_pkg_346_, 0);
lean_dec(v_unused_396_);
v___x_381_ = v_pkg_346_;
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_lintDriver_379_);
lean_inc(v_testDriver_378_);
lean_inc(v_buildArchive_377_);
lean_inc(v_postUpdateHooks_376_);
lean_inc(v_defaultScripts_375_);
lean_inc(v_scripts_374_);
lean_inc(v_defaultTargets_373_);
lean_inc(v_targetDeclMap_372_);
lean_inc(v_targetDecls_371_);
lean_inc(v_depPkgs_370_);
lean_inc(v_depConfigs_369_);
lean_inc(v_remoteUrl_368_);
lean_inc(v_scope_367_);
lean_inc(v_relManifestFile_366_);
lean_inc(v_relConfigFile_365_);
lean_inc(v_configFile_364_);
lean_inc(v_config_363_);
lean_inc(v_relDir_362_);
lean_inc(v_dir_361_);
lean_inc(v_origName_360_);
lean_inc(v_keyName_359_);
lean_inc(v_baseName_358_);
lean_dec(v_pkg_346_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_394_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_383_ = lean_array_get_size(v_packages_352_);
v___x_384_ = ((lean_object*)(l_Lake_Workspace_addPackage___closed__0));
lean_inc(v_keyName_359_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 13, v___x_384_);
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_baseName_358_);
lean_ctor_set(v_reuseFailAlloc_393_, 2, v_keyName_359_);
lean_ctor_set(v_reuseFailAlloc_393_, 3, v_origName_360_);
lean_ctor_set(v_reuseFailAlloc_393_, 4, v_dir_361_);
lean_ctor_set(v_reuseFailAlloc_393_, 5, v_relDir_362_);
lean_ctor_set(v_reuseFailAlloc_393_, 6, v_config_363_);
lean_ctor_set(v_reuseFailAlloc_393_, 7, v_configFile_364_);
lean_ctor_set(v_reuseFailAlloc_393_, 8, v_relConfigFile_365_);
lean_ctor_set(v_reuseFailAlloc_393_, 9, v_relManifestFile_366_);
lean_ctor_set(v_reuseFailAlloc_393_, 10, v_scope_367_);
lean_ctor_set(v_reuseFailAlloc_393_, 11, v_remoteUrl_368_);
lean_ctor_set(v_reuseFailAlloc_393_, 12, v_depConfigs_369_);
lean_ctor_set(v_reuseFailAlloc_393_, 13, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_393_, 14, v_depPkgs_370_);
lean_ctor_set(v_reuseFailAlloc_393_, 15, v_targetDecls_371_);
lean_ctor_set(v_reuseFailAlloc_393_, 16, v_targetDeclMap_372_);
lean_ctor_set(v_reuseFailAlloc_393_, 17, v_defaultTargets_373_);
lean_ctor_set(v_reuseFailAlloc_393_, 18, v_scripts_374_);
lean_ctor_set(v_reuseFailAlloc_393_, 19, v_defaultScripts_375_);
lean_ctor_set(v_reuseFailAlloc_393_, 20, v_postUpdateHooks_376_);
lean_ctor_set(v_reuseFailAlloc_393_, 21, v_buildArchive_377_);
lean_ctor_set(v_reuseFailAlloc_393_, 22, v_testDriver_378_);
lean_ctor_set(v_reuseFailAlloc_393_, 23, v_lintDriver_379_);
v___x_386_ = v_reuseFailAlloc_393_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
lean_inc_ref(v___x_386_);
v___x_387_ = lean_array_push(v_packages_352_, v___x_386_);
v___x_388_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_389_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_388_, v_keyName_359_, v___x_386_, v_packageMap_353_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 5, v___x_389_);
lean_ctor_set(v___x_356_, 4, v___x_387_);
v___x_391_ = v___x_356_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_lakeEnv_348_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_lakeConfig_349_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_lakeCache_350_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_lakeArgs_x3f_351_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_392_, 5, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_392_, 6, v_facetConfigs_354_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_398_, lean_object* v_self_399_){
_start:
{
lean_object* v_packageMap_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_packageMap_400_ = lean_ctor_get(v_self_399_, 5);
lean_inc(v_packageMap_400_);
lean_dec_ref(v_self_399_);
v___x_401_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_402_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_401_, v_packageMap_400_, v_keyName_398_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v_a_406_, lean_object* v_x_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_baseName_409_; uint8_t v___x_410_; 
v_baseName_409_ = lean_ctor_get(v_a_406_, 1);
v___x_410_ = lean_name_eq(v_baseName_409_, v_name_403_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v_a_406_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_404_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v___x_404_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v_a_406_);
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_405_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_416_, lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v_a_419_, lean_object* v_x_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_416_, v___x_417_, v___x_418_, v_a_419_, v_x_420_, v___y_421_);
lean_dec_ref(v___y_421_);
lean_dec(v_name_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_445_, lean_object* v_self_446_){
_start:
{
lean_object* v_packages_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___f_452_; size_t v_sz_453_; size_t v___x_454_; lean_object* v___x_455_; lean_object* v_fst_456_; 
v_packages_447_ = lean_ctor_get(v_self_446_, 4);
lean_inc_ref(v_packages_447_);
lean_dec_ref(v_self_446_);
v___x_448_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__9));
v___x_449_ = lean_box(0);
v___x_450_ = lean_box(0);
v___x_451_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__10));
v___f_452_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_452_, 0, v_name_445_);
lean_closure_set(v___f_452_, 1, v___x_451_);
lean_closure_set(v___f_452_, 2, v___x_450_);
v_sz_453_ = lean_array_size(v_packages_447_);
v___x_454_ = ((size_t)0ULL);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_448_, v_packages_447_, v___f_452_, v_sz_453_, v___x_454_, v___x_451_);
v_fst_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_fst_456_);
lean_dec(v___x_455_);
if (lean_obj_tag(v_fst_456_) == 0)
{
return v___x_449_;
}
else
{
lean_object* v_val_457_; 
v_val_457_ = lean_ctor_get(v_fst_456_, 0);
lean_inc(v_val_457_);
lean_dec_ref_known(v_fst_456_, 1);
return v_val_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_458_, lean_object* v_self_459_){
_start:
{
lean_object* v_packageMap_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_packageMap_460_ = lean_ctor_get(v_self_459_, 5);
lean_inc(v_packageMap_460_);
lean_dec_ref(v_self_459_);
v___x_461_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_462_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_461_, v_packageMap_460_, v_name_458_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_466_, lean_object* v_as_467_, size_t v_sz_468_, size_t v_i_469_, lean_object* v_b_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = lean_usize_dec_lt(v_i_469_, v_sz_468_);
if (v___x_471_ == 0)
{
lean_inc_ref(v_b_470_);
return v_b_470_;
}
else
{
lean_object* v_a_472_; lean_object* v_scripts_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_a_472_ = lean_array_uget_borrowed(v_as_467_, v_i_469_);
v_scripts_473_ = lean_ctor_get(v_a_472_, 18);
v___x_474_ = lean_box(0);
v___x_475_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_473_, v_script_466_);
if (lean_obj_tag(v___x_475_) == 1)
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_474_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; 
lean_dec(v___x_475_);
v___x_478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_add(v_i_469_, v___x_479_);
v_i_469_ = v___x_480_;
v_b_470_ = v___x_478_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_482_, lean_object* v_as_483_, lean_object* v_sz_484_, lean_object* v_i_485_, lean_object* v_b_486_){
_start:
{
size_t v_sz_boxed_487_; size_t v_i_boxed_488_; lean_object* v_res_489_; 
v_sz_boxed_487_ = lean_unbox_usize(v_sz_484_);
lean_dec(v_sz_484_);
v_i_boxed_488_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v_res_489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_482_, v_as_483_, v_sz_boxed_487_, v_i_boxed_488_, v_b_486_);
lean_dec_ref(v_b_486_);
lean_dec_ref(v_as_483_);
lean_dec(v_script_482_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_490_, lean_object* v_self_491_){
_start:
{
lean_object* v_packages_492_; lean_object* v___x_493_; lean_object* v___x_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; lean_object* v_fst_498_; 
v_packages_492_ = lean_ctor_get(v_self_491_, 4);
v___x_493_ = lean_box(0);
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_495_ = lean_array_size(v_packages_492_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_490_, v_packages_492_, v_sz_495_, v___x_496_, v___x_494_);
v_fst_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_fst_498_);
lean_dec_ref(v___x_497_);
if (lean_obj_tag(v_fst_498_) == 0)
{
return v___x_493_;
}
else
{
lean_object* v_val_499_; 
v_val_499_ = lean_ctor_get(v_fst_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v_fst_498_, 1);
return v_val_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_500_, lean_object* v_self_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lake_Workspace_findScript_x3f(v_script_500_, v_self_501_);
lean_dec_ref(v_self_501_);
lean_dec(v_script_500_);
return v_res_502_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_503_, lean_object* v_as_504_, size_t v_i_505_, size_t v_stop_506_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_eq(v_i_505_, v_stop_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_array_uget_borrowed(v_as_504_, v_i_505_);
v___x_509_ = l_Lake_Package_isLocalModule(v_mod_503_, v___x_508_);
if (v___x_509_ == 0)
{
size_t v___x_510_; size_t v___x_511_; 
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_add(v_i_505_, v___x_510_);
v_i_505_ = v___x_511_;
goto _start;
}
else
{
return v___x_509_;
}
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_514_, lean_object* v_as_515_, lean_object* v_i_516_, lean_object* v_stop_517_){
_start:
{
size_t v_i_boxed_518_; size_t v_stop_boxed_519_; uint8_t v_res_520_; lean_object* v_r_521_; 
v_i_boxed_518_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_stop_boxed_519_ = lean_unbox_usize(v_stop_517_);
lean_dec(v_stop_517_);
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_514_, v_as_515_, v_i_boxed_518_, v_stop_boxed_519_);
lean_dec_ref(v_as_515_);
lean_dec(v_mod_514_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_522_, lean_object* v_self_523_){
_start:
{
lean_object* v_packages_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_packages_524_ = lean_ctor_get(v_self_523_, 4);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_array_get_size(v_packages_524_);
v___x_527_ = lean_nat_dec_lt(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
return v___x_527_;
}
else
{
if (v___x_527_ == 0)
{
return v___x_527_;
}
else
{
size_t v___x_528_; size_t v___x_529_; uint8_t v___x_530_; 
v___x_528_ = ((size_t)0ULL);
v___x_529_ = lean_usize_of_nat(v___x_526_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_522_, v_packages_524_, v___x_528_, v___x_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_531_, lean_object* v_self_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_Lake_Workspace_isLocalModule(v_mod_531_, v_self_532_);
lean_dec_ref(v_self_532_);
lean_dec(v_mod_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_535_, lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
v___x_541_ = l_Lake_Package_isBuildableModule(v_mod_535_, v___x_540_);
if (v___x_541_ == 0)
{
size_t v___x_542_; size_t v___x_543_; 
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_add(v_i_537_, v___x_542_);
v_i_537_ = v___x_543_;
goto _start;
}
else
{
return v___x_541_;
}
}
else
{
uint8_t v___x_545_; 
v___x_545_ = 0;
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_546_, lean_object* v_as_547_, lean_object* v_i_548_, lean_object* v_stop_549_){
_start:
{
size_t v_i_boxed_550_; size_t v_stop_boxed_551_; uint8_t v_res_552_; lean_object* v_r_553_; 
v_i_boxed_550_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_stop_boxed_551_ = lean_unbox_usize(v_stop_549_);
lean_dec(v_stop_549_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_546_, v_as_547_, v_i_boxed_550_, v_stop_boxed_551_);
lean_dec_ref(v_as_547_);
lean_dec(v_mod_546_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_554_, lean_object* v_self_555_){
_start:
{
lean_object* v_packages_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_packages_556_ = lean_ctor_get(v_self_555_, 4);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_array_get_size(v_packages_556_);
v___x_559_ = lean_nat_dec_lt(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
return v___x_559_;
}
else
{
if (v___x_559_ == 0)
{
return v___x_559_;
}
else
{
size_t v___x_560_; size_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = ((size_t)0ULL);
v___x_561_ = lean_usize_of_nat(v___x_558_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_554_, v_packages_556_, v___x_560_, v___x_561_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_563_, lean_object* v_self_564_){
_start:
{
uint8_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = l_Lake_Workspace_isBuildableModule(v_mod_563_, v_self_564_);
lean_dec_ref(v_self_564_);
lean_dec(v_mod_563_);
v_r_566_ = lean_box(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_570_, lean_object* v_as_571_, size_t v_sz_572_, size_t v_i_573_, lean_object* v_b_574_){
_start:
{
uint8_t v___x_575_; 
v___x_575_ = lean_usize_dec_lt(v_i_573_, v_sz_572_);
if (v___x_575_ == 0)
{
lean_dec(v_mod_570_);
lean_inc_ref(v_b_574_);
return v_b_574_;
}
else
{
lean_object* v___x_576_; lean_object* v_a_577_; lean_object* v___x_578_; 
v___x_576_ = lean_box(0);
v_a_577_ = lean_array_uget_borrowed(v_as_571_, v_i_573_);
lean_inc(v_a_577_);
lean_inc(v_mod_570_);
v___x_578_ = l_Lake_Package_findModule_x3f(v_mod_570_, v_a_577_);
if (lean_obj_tag(v___x_578_) == 1)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_mod_570_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_576_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; 
lean_dec(v___x_578_);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_573_, v___x_582_);
v_i_573_ = v___x_583_;
v_b_574_ = v___x_581_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_585_, lean_object* v_as_586_, lean_object* v_sz_587_, lean_object* v_i_588_, lean_object* v_b_589_){
_start:
{
size_t v_sz_boxed_590_; size_t v_i_boxed_591_; lean_object* v_res_592_; 
v_sz_boxed_590_ = lean_unbox_usize(v_sz_587_);
lean_dec(v_sz_587_);
v_i_boxed_591_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_585_, v_as_586_, v_sz_boxed_590_, v_i_boxed_591_, v_b_589_);
lean_dec_ref(v_b_589_);
lean_dec_ref(v_as_586_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_593_, lean_object* v_self_594_){
_start:
{
lean_object* v_packages_595_; lean_object* v___x_596_; lean_object* v___x_597_; size_t v_sz_598_; size_t v___x_599_; lean_object* v___x_600_; lean_object* v_fst_601_; 
v_packages_595_ = lean_ctor_get(v_self_594_, 4);
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_598_ = lean_array_size(v_packages_595_);
v___x_599_ = ((size_t)0ULL);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_593_, v_packages_595_, v_sz_598_, v___x_599_, v___x_597_);
v_fst_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_fst_601_);
lean_dec_ref(v___x_600_);
if (lean_obj_tag(v_fst_601_) == 0)
{
return v___x_596_;
}
else
{
lean_object* v_val_602_; 
v_val_602_ = lean_ctor_get(v_fst_601_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_fst_601_, 1);
return v_val_602_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_603_, lean_object* v_self_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lake_Workspace_findModule_x3f(v_mod_603_, v_self_604_);
lean_dec_ref(v_self_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_606_, lean_object* v_as_607_, size_t v_i_608_, size_t v_stop_609_, lean_object* v_b_610_){
_start:
{
lean_object* v___y_612_; uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_eq(v_i_608_, v_stop_609_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_array_uget_borrowed(v_as_607_, v_i_608_);
lean_inc(v___x_617_);
lean_inc(v_mod_606_);
v___x_618_ = l_Lake_Package_findModule_x3f(v_mod_606_, v___x_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
v___y_612_ = v_b_610_;
goto v___jp_611_;
}
else
{
lean_object* v_val_619_; lean_object* v___x_620_; 
v_val_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = lean_array_push(v_b_610_, v_val_619_);
v___y_612_ = v___x_620_;
goto v___jp_611_;
}
}
else
{
lean_dec(v_mod_606_);
return v_b_610_;
}
v___jp_611_:
{
size_t v___x_613_; size_t v___x_614_; 
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_608_, v___x_613_);
v_i_608_ = v___x_614_;
v_b_610_ = v___y_612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_621_, lean_object* v_as_622_, lean_object* v_i_623_, lean_object* v_stop_624_, lean_object* v_b_625_){
_start:
{
size_t v_i_boxed_626_; size_t v_stop_boxed_627_; lean_object* v_res_628_; 
v_i_boxed_626_ = lean_unbox_usize(v_i_623_);
lean_dec(v_i_623_);
v_stop_boxed_627_ = lean_unbox_usize(v_stop_624_);
lean_dec(v_stop_624_);
v_res_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_621_, v_as_622_, v_i_boxed_626_, v_stop_boxed_627_, v_b_625_);
lean_dec_ref(v_as_622_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_631_, lean_object* v_as_632_, lean_object* v_start_633_, lean_object* v_stop_634_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_636_ = lean_nat_dec_lt(v_start_633_, v_stop_634_);
if (v___x_636_ == 0)
{
lean_dec(v_mod_631_);
return v___x_635_;
}
else
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_as_632_);
v___x_638_ = lean_nat_dec_le(v_stop_634_, v___x_637_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_lt(v_start_633_, v___x_637_);
if (v___x_639_ == 0)
{
lean_dec(v_mod_631_);
return v___x_635_;
}
else
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_usize_of_nat(v_start_633_);
v___x_641_ = lean_usize_of_nat(v___x_637_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_631_, v_as_632_, v___x_640_, v___x_641_, v___x_635_);
return v___x_642_;
}
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_usize_of_nat(v_start_633_);
v___x_644_ = lean_usize_of_nat(v_stop_634_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_631_, v_as_632_, v___x_643_, v___x_644_, v___x_635_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_646_, lean_object* v_as_647_, lean_object* v_start_648_, lean_object* v_stop_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_646_, v_as_647_, v_start_648_, v_stop_649_);
lean_dec(v_stop_649_);
lean_dec(v_start_648_);
lean_dec_ref(v_as_647_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_651_, lean_object* v_self_652_){
_start:
{
lean_object* v_packages_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_packages_653_ = lean_ctor_get(v_self_652_, 4);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_array_get_size(v_packages_653_);
v___x_656_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_651_, v_packages_653_, v___x_654_, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_657_, lean_object* v_self_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_Workspace_findModules(v_mod_657_, v_self_658_);
lean_dec_ref(v_self_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_660_, lean_object* v_as_661_, size_t v_sz_662_, size_t v_i_663_, lean_object* v_b_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = lean_usize_dec_lt(v_i_663_, v_sz_662_);
if (v___x_665_ == 0)
{
lean_dec(v_mod_660_);
lean_inc_ref(v_b_664_);
return v_b_664_;
}
else
{
lean_object* v___x_666_; lean_object* v_a_667_; lean_object* v___x_668_; 
v___x_666_ = lean_box(0);
v_a_667_ = lean_array_uget_borrowed(v_as_661_, v_i_663_);
lean_inc(v_a_667_);
lean_inc(v_mod_660_);
v___x_668_ = l_Lake_Package_findTargetModule_x3f(v_mod_660_, v_a_667_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v_mod_660_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_666_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; size_t v___x_672_; size_t v___x_673_; 
lean_dec(v___x_668_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_663_, v___x_672_);
v_i_663_ = v___x_673_;
v_b_664_ = v___x_671_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_675_, lean_object* v_as_676_, lean_object* v_sz_677_, lean_object* v_i_678_, lean_object* v_b_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_677_);
lean_dec(v_sz_677_);
v_i_boxed_681_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_675_, v_as_676_, v_sz_boxed_680_, v_i_boxed_681_, v_b_679_);
lean_dec_ref(v_b_679_);
lean_dec_ref(v_as_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_683_, lean_object* v_self_684_){
_start:
{
lean_object* v_packages_685_; lean_object* v___x_686_; lean_object* v___x_687_; size_t v_sz_688_; size_t v___x_689_; lean_object* v___x_690_; lean_object* v_fst_691_; 
v_packages_685_ = lean_ctor_get(v_self_684_, 4);
v___x_686_ = lean_box(0);
v___x_687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_688_ = lean_array_size(v_packages_685_);
v___x_689_ = ((size_t)0ULL);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_683_, v_packages_685_, v_sz_688_, v___x_689_, v___x_687_);
v_fst_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_fst_691_);
lean_dec_ref(v___x_690_);
if (lean_obj_tag(v_fst_691_) == 0)
{
return v___x_686_;
}
else
{
lean_object* v_val_692_; 
v_val_692_ = lean_ctor_get(v_fst_691_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_fst_691_, 1);
return v_val_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_693_, lean_object* v_self_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_693_, v_self_694_);
lean_dec_ref(v_self_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_696_, lean_object* v_as_697_, size_t v_sz_698_, size_t v_i_699_, lean_object* v_b_700_){
_start:
{
uint8_t v___x_701_; 
v___x_701_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_701_ == 0)
{
lean_dec_ref(v_path_696_);
lean_inc_ref(v_b_700_);
return v_b_700_;
}
else
{
lean_object* v___x_702_; lean_object* v_a_703_; lean_object* v___x_704_; 
v___x_702_ = lean_box(0);
v_a_703_ = lean_array_uget_borrowed(v_as_697_, v_i_699_);
lean_inc(v_a_703_);
lean_inc_ref(v_path_696_);
v___x_704_ = l_Lake_Package_findModuleBySrc_x3f(v_path_696_, v_a_703_);
if (lean_obj_tag(v___x_704_) == 1)
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref(v_path_696_);
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_702_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; size_t v___x_708_; size_t v___x_709_; 
lean_dec(v___x_704_);
v___x_707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_699_, v___x_708_);
v_i_699_ = v___x_709_;
v_b_700_ = v___x_707_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_711_, lean_object* v_as_712_, lean_object* v_sz_713_, lean_object* v_i_714_, lean_object* v_b_715_){
_start:
{
size_t v_sz_boxed_716_; size_t v_i_boxed_717_; lean_object* v_res_718_; 
v_sz_boxed_716_ = lean_unbox_usize(v_sz_713_);
lean_dec(v_sz_713_);
v_i_boxed_717_ = lean_unbox_usize(v_i_714_);
lean_dec(v_i_714_);
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_711_, v_as_712_, v_sz_boxed_716_, v_i_boxed_717_, v_b_715_);
lean_dec_ref(v_b_715_);
lean_dec_ref(v_as_712_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_719_, lean_object* v_self_720_){
_start:
{
lean_object* v_packages_721_; lean_object* v___x_722_; lean_object* v___x_723_; size_t v_sz_724_; size_t v___x_725_; lean_object* v___x_726_; lean_object* v_fst_727_; 
v_packages_721_ = lean_ctor_get(v_self_720_, 4);
v___x_722_ = lean_box(0);
v___x_723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_724_ = lean_array_size(v_packages_721_);
v___x_725_ = ((size_t)0ULL);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_719_, v_packages_721_, v_sz_724_, v___x_725_, v___x_723_);
v_fst_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_fst_727_);
lean_dec_ref(v___x_726_);
if (lean_obj_tag(v_fst_727_) == 0)
{
return v___x_722_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v_fst_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v_fst_727_, 1);
return v_val_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_729_, lean_object* v_self_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_729_, v_self_730_);
lean_dec_ref(v_self_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_735_, lean_object* v_as_736_, size_t v_sz_737_, size_t v_i_738_, lean_object* v_b_739_){
_start:
{
lean_object* v_a_741_; uint8_t v___x_745_; 
v___x_745_ = lean_usize_dec_lt(v_i_738_, v_sz_737_);
if (v___x_745_ == 0)
{
lean_inc_ref(v_b_739_);
return v_b_739_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_749_; 
v___x_746_ = lean_box(0);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_748_ = lean_array_uget_borrowed(v_as_736_, v_i_738_);
v___x_749_ = l_Lake_Package_findTargetDecl_x3f(v_name_735_, v_a_748_);
if (lean_obj_tag(v___x_749_) == 0)
{
v_a_741_ = v___x_747_;
goto v___jp_740_;
}
else
{
lean_object* v_val_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_765_; 
v_val_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_765_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_765_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_val_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_765_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_name_754_; lean_object* v_kind_755_; lean_object* v_config_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_name_754_ = lean_ctor_get(v_val_750_, 1);
lean_inc(v_name_754_);
v_kind_755_ = lean_ctor_get(v_val_750_, 2);
lean_inc(v_kind_755_);
v_config_756_ = lean_ctor_get(v_val_750_, 3);
lean_inc(v_config_756_);
lean_dec(v_val_750_);
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_758_ = lean_name_eq(v_kind_755_, v___x_757_);
lean_dec(v_kind_755_);
if (v___x_758_ == 0)
{
lean_dec(v_config_756_);
lean_dec(v_name_754_);
lean_del_object(v___x_752_);
v_a_741_ = v___x_747_;
goto v___jp_740_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_761_; 
lean_inc(v_a_748_);
v___x_759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_759_, 0, v_a_748_);
lean_ctor_set(v___x_759_, 1, v_name_754_);
lean_ctor_set(v___x_759_, 2, v_config_756_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_759_);
v___x_761_ = v___x_752_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_764_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v___x_746_);
return v___x_763_;
}
}
}
}
}
v___jp_740_:
{
size_t v___x_742_; size_t v___x_743_; 
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_738_, v___x_742_);
v_i_738_ = v___x_743_;
v_b_739_ = v_a_741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_766_, lean_object* v_as_767_, lean_object* v_sz_768_, lean_object* v_i_769_, lean_object* v_b_770_){
_start:
{
size_t v_sz_boxed_771_; size_t v_i_boxed_772_; lean_object* v_res_773_; 
v_sz_boxed_771_ = lean_unbox_usize(v_sz_768_);
lean_dec(v_sz_768_);
v_i_boxed_772_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_766_, v_as_767_, v_sz_boxed_771_, v_i_boxed_772_, v_b_770_);
lean_dec_ref(v_b_770_);
lean_dec_ref(v_as_767_);
lean_dec(v_name_766_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_774_, lean_object* v_self_775_){
_start:
{
lean_object* v_packages_776_; lean_object* v___x_777_; lean_object* v___x_778_; size_t v_sz_779_; size_t v___x_780_; lean_object* v___x_781_; lean_object* v_fst_782_; 
v_packages_776_ = lean_ctor_get(v_self_775_, 4);
v___x_777_ = lean_box(0);
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_779_ = lean_array_size(v_packages_776_);
v___x_780_ = ((size_t)0ULL);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_774_, v_packages_776_, v_sz_779_, v___x_780_, v___x_778_);
v_fst_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_fst_782_);
lean_dec_ref(v___x_781_);
if (lean_obj_tag(v_fst_782_) == 0)
{
return v___x_777_;
}
else
{
lean_object* v_val_783_; 
v_val_783_ = lean_ctor_get(v_fst_782_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v_fst_782_, 1);
return v_val_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_784_, lean_object* v_self_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lake_Workspace_findLeanLib_x3f(v_name_784_, v_self_785_);
lean_dec_ref(v_self_785_);
lean_dec(v_name_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_787_, lean_object* v_as_788_, size_t v_sz_789_, size_t v_i_790_, lean_object* v_b_791_){
_start:
{
lean_object* v_a_793_; uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_790_, v_sz_789_);
if (v___x_797_ == 0)
{
lean_inc_ref(v_b_791_);
return v_b_791_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_a_800_; lean_object* v___x_801_; 
v___x_798_ = lean_box(0);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_800_ = lean_array_uget_borrowed(v_as_788_, v_i_790_);
v___x_801_ = l_Lake_Package_findTargetDecl_x3f(v_name_787_, v_a_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
v_a_793_ = v___x_799_;
goto v___jp_792_;
}
else
{
lean_object* v_val_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_817_; 
v_val_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_817_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_817_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_val_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_817_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_name_806_; lean_object* v_kind_807_; lean_object* v_config_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_name_806_ = lean_ctor_get(v_val_802_, 1);
lean_inc(v_name_806_);
v_kind_807_ = lean_ctor_get(v_val_802_, 2);
lean_inc(v_kind_807_);
v_config_808_ = lean_ctor_get(v_val_802_, 3);
lean_inc(v_config_808_);
lean_dec(v_val_802_);
v___x_809_ = l_Lake_LeanExe_keyword;
v___x_810_ = lean_name_eq(v_kind_807_, v___x_809_);
lean_dec(v_kind_807_);
if (v___x_810_ == 0)
{
lean_dec(v_config_808_);
lean_dec(v_name_806_);
lean_del_object(v___x_804_);
v_a_793_ = v___x_799_;
goto v___jp_792_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_a_800_);
v___x_811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_811_, 0, v_a_800_);
lean_ctor_set(v___x_811_, 1, v_name_806_);
lean_ctor_set(v___x_811_, 2, v_config_808_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_811_);
v___x_813_ = v___x_804_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_816_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_798_);
return v___x_815_;
}
}
}
}
}
v___jp_792_:
{
size_t v___x_794_; size_t v___x_795_; 
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_790_, v___x_794_);
v_i_790_ = v___x_795_;
v_b_791_ = v_a_793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_818_, lean_object* v_as_819_, lean_object* v_sz_820_, lean_object* v_i_821_, lean_object* v_b_822_){
_start:
{
size_t v_sz_boxed_823_; size_t v_i_boxed_824_; lean_object* v_res_825_; 
v_sz_boxed_823_ = lean_unbox_usize(v_sz_820_);
lean_dec(v_sz_820_);
v_i_boxed_824_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_818_, v_as_819_, v_sz_boxed_823_, v_i_boxed_824_, v_b_822_);
lean_dec_ref(v_b_822_);
lean_dec_ref(v_as_819_);
lean_dec(v_name_818_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_826_, lean_object* v_self_827_){
_start:
{
lean_object* v_packages_828_; lean_object* v___x_829_; lean_object* v___x_830_; size_t v_sz_831_; size_t v___x_832_; lean_object* v___x_833_; lean_object* v_fst_834_; 
v_packages_828_ = lean_ctor_get(v_self_827_, 4);
v___x_829_ = lean_box(0);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_831_ = lean_array_size(v_packages_828_);
v___x_832_ = ((size_t)0ULL);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_826_, v_packages_828_, v_sz_831_, v___x_832_, v___x_830_);
v_fst_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_fst_834_);
lean_dec_ref(v___x_833_);
if (lean_obj_tag(v_fst_834_) == 0)
{
return v___x_829_;
}
else
{
lean_object* v_val_835_; 
v_val_835_ = lean_ctor_get(v_fst_834_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_fst_834_, 1);
return v_val_835_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_836_, lean_object* v_self_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lake_Workspace_findLeanExe_x3f(v_name_836_, v_self_837_);
lean_dec_ref(v_self_837_);
lean_dec(v_name_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_839_, lean_object* v_as_840_, size_t v_sz_841_, size_t v_i_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_a_845_; uint8_t v___x_849_; 
v___x_849_ = lean_usize_dec_lt(v_i_842_, v_sz_841_);
if (v___x_849_ == 0)
{
lean_inc_ref(v_b_843_);
return v_b_843_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_a_852_; lean_object* v___x_853_; 
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_852_ = lean_array_uget_borrowed(v_as_840_, v_i_842_);
v___x_853_ = l_Lake_Package_findTargetDecl_x3f(v_name_839_, v_a_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
v_a_845_ = v___x_851_;
goto v___jp_844_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_869_; 
v_val_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_869_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_869_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_869_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_name_858_; lean_object* v_kind_859_; lean_object* v_config_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_name_858_ = lean_ctor_get(v_val_854_, 1);
lean_inc(v_name_858_);
v_kind_859_ = lean_ctor_get(v_val_854_, 2);
lean_inc(v_kind_859_);
v_config_860_ = lean_ctor_get(v_val_854_, 3);
lean_inc(v_config_860_);
lean_dec(v_val_854_);
v___x_861_ = l_Lake_ExternLib_keyword;
v___x_862_ = lean_name_eq(v_kind_859_, v___x_861_);
lean_dec(v_kind_859_);
if (v___x_862_ == 0)
{
lean_dec(v_config_860_);
lean_dec(v_name_858_);
lean_del_object(v___x_856_);
v_a_845_ = v___x_851_;
goto v___jp_844_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_inc(v_a_852_);
v___x_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_863_, 0, v_a_852_);
lean_ctor_set(v___x_863_, 1, v_name_858_);
lean_ctor_set(v___x_863_, 2, v_config_860_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_863_);
v___x_865_ = v___x_856_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_868_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_850_);
return v___x_867_;
}
}
}
}
}
v___jp_844_:
{
size_t v___x_846_; size_t v___x_847_; 
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_842_, v___x_846_);
v_i_842_ = v___x_847_;
v_b_843_ = v_a_845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_870_, lean_object* v_as_871_, lean_object* v_sz_872_, lean_object* v_i_873_, lean_object* v_b_874_){
_start:
{
size_t v_sz_boxed_875_; size_t v_i_boxed_876_; lean_object* v_res_877_; 
v_sz_boxed_875_ = lean_unbox_usize(v_sz_872_);
lean_dec(v_sz_872_);
v_i_boxed_876_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_870_, v_as_871_, v_sz_boxed_875_, v_i_boxed_876_, v_b_874_);
lean_dec_ref(v_b_874_);
lean_dec_ref(v_as_871_);
lean_dec(v_name_870_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_878_, lean_object* v_self_879_){
_start:
{
lean_object* v_packages_880_; lean_object* v___x_881_; lean_object* v___x_882_; size_t v_sz_883_; size_t v___x_884_; lean_object* v___x_885_; lean_object* v_fst_886_; 
v_packages_880_ = lean_ctor_get(v_self_879_, 4);
v___x_881_ = lean_box(0);
v___x_882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_883_ = lean_array_size(v_packages_880_);
v___x_884_ = ((size_t)0ULL);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_878_, v_packages_880_, v_sz_883_, v___x_884_, v___x_882_);
v_fst_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_fst_886_);
lean_dec_ref(v___x_885_);
if (lean_obj_tag(v_fst_886_) == 0)
{
return v___x_881_;
}
else
{
lean_object* v_val_887_; 
v_val_887_ = lean_ctor_get(v_fst_886_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v_fst_886_, 1);
return v_val_887_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_888_, lean_object* v_self_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lake_Workspace_findExternLib_x3f(v_name_888_, v_self_889_);
lean_dec_ref(v_self_889_);
lean_dec(v_name_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_891_, lean_object* v_f_892_){
_start:
{
if (lean_obj_tag(v_a_891_) == 0)
{
lean_object* v___x_893_; 
lean_dec(v_f_892_);
v___x_893_ = lean_box(0);
return v___x_893_;
}
else
{
lean_object* v_val_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_902_; 
v_val_894_ = lean_ctor_get(v_a_891_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v_a_891_);
if (v_isSharedCheck_902_ == 0)
{
v___x_896_ = v_a_891_;
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_val_894_);
lean_dec(v_a_891_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_902_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_apply_1(v_f_892_, v_val_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_898_);
v___x_900_ = v___x_896_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_a_905_, lean_object* v_f_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_905_, v_f_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_a_908_);
lean_ctor_set(v___x_910_, 1, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_914_, lean_object* v_as_915_, size_t v_sz_916_, size_t v_i_917_, lean_object* v_b_918_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = lean_usize_dec_lt(v_i_917_, v_sz_916_);
if (v___x_919_ == 0)
{
lean_inc_ref(v_b_918_);
return v_b_918_;
}
else
{
lean_object* v___x_920_; lean_object* v_a_921_; lean_object* v___f_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_920_ = lean_box(0);
v_a_921_ = lean_array_uget_borrowed(v_as_915_, v_i_917_);
lean_inc(v_a_921_);
v___f_922_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_922_, 0, v_a_921_);
v___x_923_ = l_Lake_Package_findTargetConfig_x3f(v_name_914_, v_a_921_);
v___x_924_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_923_, v___f_922_);
if (lean_obj_tag(v___x_924_) == 1)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_920_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; size_t v___x_928_; size_t v___x_929_; 
lean_dec(v___x_924_);
v___x_927_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_917_, v___x_928_);
v_i_917_ = v___x_929_;
v_b_918_ = v___x_927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_931_, lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_){
_start:
{
size_t v_sz_boxed_936_; size_t v_i_boxed_937_; lean_object* v_res_938_; 
v_sz_boxed_936_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_937_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_931_, v_as_932_, v_sz_boxed_936_, v_i_boxed_937_, v_b_935_);
lean_dec_ref(v_b_935_);
lean_dec_ref(v_as_932_);
lean_dec(v_name_931_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_939_, lean_object* v_self_940_){
_start:
{
lean_object* v_packages_941_; lean_object* v___x_942_; lean_object* v___x_943_; size_t v_sz_944_; size_t v___x_945_; lean_object* v___x_946_; lean_object* v_fst_947_; 
v_packages_941_ = lean_ctor_get(v_self_940_, 4);
v___x_942_ = lean_box(0);
v___x_943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_944_ = lean_array_size(v_packages_941_);
v___x_945_ = ((size_t)0ULL);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_939_, v_packages_941_, v_sz_944_, v___x_945_, v___x_943_);
v_fst_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_fst_947_);
lean_dec_ref(v___x_946_);
if (lean_obj_tag(v_fst_947_) == 0)
{
return v___x_942_;
}
else
{
lean_object* v_val_948_; 
v_val_948_ = lean_ctor_get(v_fst_947_, 0);
lean_inc(v_val_948_);
lean_dec_ref_known(v_fst_947_, 1);
return v_val_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_949_, lean_object* v_self_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_949_, v_self_950_);
lean_dec_ref(v_self_950_);
lean_dec(v_name_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_952_, lean_object* v_x_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v_a_952_);
lean_ctor_set(v___x_954_, 1, v_x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_955_, lean_object* v_as_956_, size_t v_sz_957_, size_t v_i_958_, lean_object* v_b_959_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = lean_usize_dec_lt(v_i_958_, v_sz_957_);
if (v___x_960_ == 0)
{
lean_inc_ref(v_b_959_);
return v_b_959_;
}
else
{
lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_961_ = lean_box(0);
v_a_962_ = lean_array_uget_borrowed(v_as_956_, v_i_958_);
lean_inc(v_a_962_);
v___f_963_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_963_, 0, v_a_962_);
v___x_964_ = l_Lake_Package_findTargetDecl_x3f(v_name_955_, v_a_962_);
v___x_965_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_964_, v___f_963_);
if (lean_obj_tag(v___x_965_) == 1)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_961_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; size_t v___x_969_; size_t v___x_970_; 
lean_dec(v___x_965_);
v___x_968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_958_, v___x_969_);
v_i_958_ = v___x_970_;
v_b_959_ = v___x_968_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_972_, lean_object* v_as_973_, lean_object* v_sz_974_, lean_object* v_i_975_, lean_object* v_b_976_){
_start:
{
size_t v_sz_boxed_977_; size_t v_i_boxed_978_; lean_object* v_res_979_; 
v_sz_boxed_977_ = lean_unbox_usize(v_sz_974_);
lean_dec(v_sz_974_);
v_i_boxed_978_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_972_, v_as_973_, v_sz_boxed_977_, v_i_boxed_978_, v_b_976_);
lean_dec_ref(v_b_976_);
lean_dec_ref(v_as_973_);
lean_dec(v_name_972_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_980_, lean_object* v_self_981_){
_start:
{
lean_object* v_packages_982_; lean_object* v___x_983_; lean_object* v___x_984_; size_t v_sz_985_; size_t v___x_986_; lean_object* v___x_987_; lean_object* v_fst_988_; 
v_packages_982_ = lean_ctor_get(v_self_981_, 4);
v___x_983_ = lean_box(0);
v___x_984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_985_ = lean_array_size(v_packages_982_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_980_, v_packages_982_, v_sz_985_, v___x_986_, v___x_984_);
v_fst_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_fst_988_);
lean_dec_ref(v___x_987_);
if (lean_obj_tag(v_fst_988_) == 0)
{
return v___x_983_;
}
else
{
lean_object* v_val_989_; 
v_val_989_ = lean_ctor_get(v_fst_988_, 0);
lean_inc(v_val_989_);
lean_dec_ref_known(v_fst_988_, 1);
return v_val_989_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_990_, lean_object* v_self_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_990_, v_self_991_);
lean_dec_ref(v_self_991_);
lean_dec(v_name_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_993_, lean_object* v_cfg_994_, lean_object* v_self_995_){
_start:
{
lean_object* v_lakeEnv_996_; lean_object* v_lakeConfig_997_; lean_object* v_lakeCache_998_; lean_object* v_lakeArgs_x3f_999_; lean_object* v_packages_1000_; lean_object* v_packageMap_1001_; lean_object* v_facetConfigs_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1010_; 
v_lakeEnv_996_ = lean_ctor_get(v_self_995_, 0);
v_lakeConfig_997_ = lean_ctor_get(v_self_995_, 1);
v_lakeCache_998_ = lean_ctor_get(v_self_995_, 2);
v_lakeArgs_x3f_999_ = lean_ctor_get(v_self_995_, 3);
v_packages_1000_ = lean_ctor_get(v_self_995_, 4);
v_packageMap_1001_ = lean_ctor_get(v_self_995_, 5);
v_facetConfigs_1002_ = lean_ctor_get(v_self_995_, 6);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_self_995_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1004_ = v_self_995_;
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_facetConfigs_1002_);
lean_inc(v_packageMap_1001_);
lean_inc(v_packages_1000_);
lean_inc(v_lakeArgs_x3f_999_);
lean_inc(v_lakeCache_998_);
lean_inc(v_lakeConfig_997_);
lean_inc(v_lakeEnv_996_);
lean_dec(v_self_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = l_Lake_FacetConfigMap_insert(v_name_993_, v_cfg_994_, v_facetConfigs_1002_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 6, v___x_1006_);
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_lakeEnv_996_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_lakeConfig_997_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_lakeCache_998_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v_lakeArgs_x3f_999_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_packages_1000_);
lean_ctor_set(v_reuseFailAlloc_1009_, 5, v_packageMap_1001_);
lean_ctor_set(v_reuseFailAlloc_1009_, 6, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_1011_, lean_object* v_self_1012_){
_start:
{
lean_object* v_facetConfigs_1013_; lean_object* v___x_1014_; 
v_facetConfigs_1013_ = lean_ctor_get(v_self_1012_, 6);
v___x_1014_ = l_Lake_FacetConfigMap_get_x3f(v_name_1011_, v_facetConfigs_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_1015_, lean_object* v_self_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1015_, v_self_1016_);
lean_dec_ref(v_self_1016_);
lean_dec(v_name_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_1018_, lean_object* v_cfg_1019_, lean_object* v_self_1020_){
_start:
{
lean_object* v_lakeEnv_1021_; lean_object* v_lakeConfig_1022_; lean_object* v_lakeCache_1023_; lean_object* v_lakeArgs_x3f_1024_; lean_object* v_packages_1025_; lean_object* v_packageMap_1026_; lean_object* v_facetConfigs_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_lakeEnv_1021_ = lean_ctor_get(v_self_1020_, 0);
v_lakeConfig_1022_ = lean_ctor_get(v_self_1020_, 1);
v_lakeCache_1023_ = lean_ctor_get(v_self_1020_, 2);
v_lakeArgs_x3f_1024_ = lean_ctor_get(v_self_1020_, 3);
v_packages_1025_ = lean_ctor_get(v_self_1020_, 4);
v_packageMap_1026_ = lean_ctor_get(v_self_1020_, 5);
v_facetConfigs_1027_ = lean_ctor_get(v_self_1020_, 6);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_self_1020_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v_self_1020_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_facetConfigs_1027_);
lean_inc(v_packageMap_1026_);
lean_inc(v_packages_1025_);
lean_inc(v_lakeArgs_x3f_1024_);
lean_inc(v_lakeCache_1023_);
lean_inc(v_lakeConfig_1022_);
lean_inc(v_lakeEnv_1021_);
lean_dec(v_self_1020_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = l_Lake_FacetConfigMap_insert(v_name_1018_, v_cfg_1019_, v_facetConfigs_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 6, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_lakeEnv_1021_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_lakeConfig_1022_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_lakeCache_1023_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_lakeArgs_x3f_1024_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_packages_1025_);
lean_ctor_set(v_reuseFailAlloc_1034_, 5, v_packageMap_1026_);
lean_ctor_set(v_reuseFailAlloc_1034_, 6, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_1036_, lean_object* v_self_1037_){
_start:
{
lean_object* v_facetConfigs_1038_; lean_object* v___x_1039_; 
v_facetConfigs_1038_ = lean_ctor_get(v_self_1037_, 6);
v___x_1039_ = l_Lake_FacetConfigMap_get_x3f(v_name_1036_, v_facetConfigs_1038_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
else
{
lean_object* v_val_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_val_1041_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1041_);
lean_dec_ref_known(v___x_1039_, 1);
v___x_1042_ = l_Lake_Module_keyword;
v___x_1043_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1042_, v_val_1041_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1044_, lean_object* v_self_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1044_, v_self_1045_);
lean_dec_ref(v_self_1045_);
lean_dec(v_name_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1047_, lean_object* v_cfg_1048_, lean_object* v_self_1049_){
_start:
{
lean_object* v_lakeEnv_1050_; lean_object* v_lakeConfig_1051_; lean_object* v_lakeCache_1052_; lean_object* v_lakeArgs_x3f_1053_; lean_object* v_packages_1054_; lean_object* v_packageMap_1055_; lean_object* v_facetConfigs_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_lakeEnv_1050_ = lean_ctor_get(v_self_1049_, 0);
v_lakeConfig_1051_ = lean_ctor_get(v_self_1049_, 1);
v_lakeCache_1052_ = lean_ctor_get(v_self_1049_, 2);
v_lakeArgs_x3f_1053_ = lean_ctor_get(v_self_1049_, 3);
v_packages_1054_ = lean_ctor_get(v_self_1049_, 4);
v_packageMap_1055_ = lean_ctor_get(v_self_1049_, 5);
v_facetConfigs_1056_ = lean_ctor_get(v_self_1049_, 6);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_self_1049_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1058_ = v_self_1049_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_facetConfigs_1056_);
lean_inc(v_packageMap_1055_);
lean_inc(v_packages_1054_);
lean_inc(v_lakeArgs_x3f_1053_);
lean_inc(v_lakeCache_1052_);
lean_inc(v_lakeConfig_1051_);
lean_inc(v_lakeEnv_1050_);
lean_dec(v_self_1049_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = l_Lake_FacetConfigMap_insert(v_name_1047_, v_cfg_1048_, v_facetConfigs_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 6, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_lakeEnv_1050_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_lakeConfig_1051_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_lakeCache_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_lakeArgs_x3f_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v_packages_1054_);
lean_ctor_set(v_reuseFailAlloc_1063_, 5, v_packageMap_1055_);
lean_ctor_set(v_reuseFailAlloc_1063_, 6, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1065_, lean_object* v_self_1066_){
_start:
{
lean_object* v_facetConfigs_1067_; lean_object* v___x_1068_; 
v_facetConfigs_1067_ = lean_ctor_get(v_self_1066_, 6);
v___x_1068_ = l_Lake_FacetConfigMap_get_x3f(v_name_1065_, v_facetConfigs_1067_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_box(0);
return v___x_1069_;
}
else
{
lean_object* v_val_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_val_1070_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_val_1070_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1071_ = l_Lake_Package_keyword;
v___x_1072_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1071_, v_val_1070_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1073_, lean_object* v_self_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1073_, v_self_1074_);
lean_dec_ref(v_self_1074_);
lean_dec(v_name_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1076_, lean_object* v_cfg_1077_, lean_object* v_self_1078_){
_start:
{
lean_object* v_lakeEnv_1079_; lean_object* v_lakeConfig_1080_; lean_object* v_lakeCache_1081_; lean_object* v_lakeArgs_x3f_1082_; lean_object* v_packages_1083_; lean_object* v_packageMap_1084_; lean_object* v_facetConfigs_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_lakeEnv_1079_ = lean_ctor_get(v_self_1078_, 0);
v_lakeConfig_1080_ = lean_ctor_get(v_self_1078_, 1);
v_lakeCache_1081_ = lean_ctor_get(v_self_1078_, 2);
v_lakeArgs_x3f_1082_ = lean_ctor_get(v_self_1078_, 3);
v_packages_1083_ = lean_ctor_get(v_self_1078_, 4);
v_packageMap_1084_ = lean_ctor_get(v_self_1078_, 5);
v_facetConfigs_1085_ = lean_ctor_get(v_self_1078_, 6);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_self_1078_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1087_ = v_self_1078_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_facetConfigs_1085_);
lean_inc(v_packageMap_1084_);
lean_inc(v_packages_1083_);
lean_inc(v_lakeArgs_x3f_1082_);
lean_inc(v_lakeCache_1081_);
lean_inc(v_lakeConfig_1080_);
lean_inc(v_lakeEnv_1079_);
lean_dec(v_self_1078_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = l_Lake_FacetConfigMap_insert(v_name_1076_, v_cfg_1077_, v_facetConfigs_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 6, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_lakeEnv_1079_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_lakeConfig_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_lakeCache_1081_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_lakeArgs_x3f_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_packages_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 5, v_packageMap_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 6, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1094_, lean_object* v_self_1095_){
_start:
{
lean_object* v_facetConfigs_1096_; lean_object* v___x_1097_; 
v_facetConfigs_1096_ = lean_ctor_get(v_self_1095_, 6);
v___x_1097_ = l_Lake_FacetConfigMap_get_x3f(v_name_1094_, v_facetConfigs_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_box(0);
return v___x_1098_;
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_val_1099_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1101_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1100_, v_val_1099_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1102_, lean_object* v_self_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1102_, v_self_1103_);
lean_dec_ref(v_self_1103_);
lean_dec(v_name_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1105_, size_t v_i_1106_, size_t v_stop_1107_, lean_object* v_b_1108_){
_start:
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_usize_dec_eq(v_i_1106_, v_stop_1107_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; lean_object* v_config_1111_; lean_object* v_dir_1112_; lean_object* v_buildDir_1113_; lean_object* v_binDir_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; 
v___x_1110_ = lean_array_uget_borrowed(v_as_1105_, v_i_1106_);
v_config_1111_ = lean_ctor_get(v___x_1110_, 6);
v_dir_1112_ = lean_ctor_get(v___x_1110_, 4);
v_buildDir_1113_ = lean_ctor_get(v_config_1111_, 5);
v_binDir_1114_ = lean_ctor_get(v_config_1111_, 8);
lean_inc_ref(v_buildDir_1113_);
v___x_1115_ = l_System_FilePath_normalize(v_buildDir_1113_);
lean_inc_ref(v_dir_1112_);
v___x_1116_ = l_Lake_joinRelative(v_dir_1112_, v___x_1115_);
lean_inc_ref(v_binDir_1114_);
v___x_1117_ = l_System_FilePath_normalize(v_binDir_1114_);
v___x_1118_ = l_Lake_joinRelative(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_b_1108_);
v___x_1120_ = ((size_t)1ULL);
v___x_1121_ = lean_usize_add(v_i_1106_, v___x_1120_);
v_i_1106_ = v___x_1121_;
v_b_1108_ = v___x_1119_;
goto _start;
}
else
{
return v_b_1108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1123_, lean_object* v_i_1124_, lean_object* v_stop_1125_, lean_object* v_b_1126_){
_start:
{
size_t v_i_boxed_1127_; size_t v_stop_boxed_1128_; lean_object* v_res_1129_; 
v_i_boxed_1127_ = lean_unbox_usize(v_i_1124_);
lean_dec(v_i_1124_);
v_stop_boxed_1128_ = lean_unbox_usize(v_stop_1125_);
lean_dec(v_stop_1125_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1123_, v_i_boxed_1127_, v_stop_boxed_1128_, v_b_1126_);
lean_dec_ref(v_as_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1130_){
_start:
{
lean_object* v_packages_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_packages_1131_ = lean_ctor_get(v_self_1130_, 4);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get_size(v_packages_1131_);
v___x_1135_ = lean_nat_dec_lt(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
return v___x_1132_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_nat_dec_le(v___x_1134_, v___x_1134_);
if (v___x_1136_ == 0)
{
if (v___x_1135_ == 0)
{
return v___x_1132_;
}
else
{
size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = lean_usize_of_nat(v___x_1134_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1131_, v___x_1137_, v___x_1138_, v___x_1132_);
return v___x_1139_;
}
}
else
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = lean_usize_of_nat(v___x_1134_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1131_, v___x_1140_, v___x_1141_, v___x_1132_);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lake_Workspace_binPath(v_self_1143_);
lean_dec_ref(v_self_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1145_, size_t v_i_1146_, size_t v_stop_1147_, lean_object* v_b_1148_){
_start:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_usize_dec_eq(v_i_1146_, v_stop_1147_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v_config_1151_; lean_object* v_dir_1152_; lean_object* v_buildDir_1153_; lean_object* v_leanLibDir_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; 
v___x_1150_ = lean_array_uget_borrowed(v_as_1145_, v_i_1146_);
v_config_1151_ = lean_ctor_get(v___x_1150_, 6);
v_dir_1152_ = lean_ctor_get(v___x_1150_, 4);
v_buildDir_1153_ = lean_ctor_get(v_config_1151_, 5);
v_leanLibDir_1154_ = lean_ctor_get(v_config_1151_, 6);
lean_inc_ref(v_buildDir_1153_);
v___x_1155_ = l_System_FilePath_normalize(v_buildDir_1153_);
lean_inc_ref(v_dir_1152_);
v___x_1156_ = l_Lake_joinRelative(v_dir_1152_, v___x_1155_);
lean_inc_ref(v_leanLibDir_1154_);
v___x_1157_ = l_System_FilePath_normalize(v_leanLibDir_1154_);
v___x_1158_ = l_Lake_joinRelative(v___x_1156_, v___x_1157_);
v___x_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v_b_1148_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_add(v_i_1146_, v___x_1160_);
v_i_1146_ = v___x_1161_;
v_b_1148_ = v___x_1159_;
goto _start;
}
else
{
return v_b_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1163_, lean_object* v_i_1164_, lean_object* v_stop_1165_, lean_object* v_b_1166_){
_start:
{
size_t v_i_boxed_1167_; size_t v_stop_boxed_1168_; lean_object* v_res_1169_; 
v_i_boxed_1167_ = lean_unbox_usize(v_i_1164_);
lean_dec(v_i_1164_);
v_stop_boxed_1168_ = lean_unbox_usize(v_stop_1165_);
lean_dec(v_stop_1165_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1163_, v_i_boxed_1167_, v_stop_boxed_1168_, v_b_1166_);
lean_dec_ref(v_as_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1170_){
_start:
{
lean_object* v_packages_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_packages_1171_ = lean_ctor_get(v_self_1170_, 4);
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_array_get_size(v_packages_1171_);
v___x_1175_ = lean_nat_dec_lt(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
return v___x_1172_;
}
else
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_nat_dec_le(v___x_1174_, v___x_1174_);
if (v___x_1176_ == 0)
{
if (v___x_1175_ == 0)
{
return v___x_1172_;
}
else
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = lean_usize_of_nat(v___x_1174_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1171_, v___x_1177_, v___x_1178_, v___x_1172_);
return v___x_1179_;
}
}
else
{
size_t v___x_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((size_t)0ULL);
v___x_1181_ = lean_usize_of_nat(v___x_1174_);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1171_, v___x_1180_, v___x_1181_, v___x_1172_);
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* v_self_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lake_Workspace_leanPath(v_self_1183_);
lean_dec_ref(v_self_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1185_, lean_object* v_as_1186_, size_t v_i_1187_, size_t v_stop_1188_, lean_object* v_b_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_usize_dec_eq(v_i_1187_, v_stop_1188_);
if (v___x_1190_ == 0)
{
size_t v___x_1191_; size_t v___x_1192_; lean_object* v___x_1193_; lean_object* v_kind_1194_; lean_object* v_config_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1191_ = ((size_t)1ULL);
v___x_1192_ = lean_usize_sub(v_i_1187_, v___x_1191_);
v___x_1193_ = lean_array_uget_borrowed(v_as_1186_, v___x_1192_);
v_kind_1194_ = lean_ctor_get(v___x_1193_, 2);
v_config_1195_ = lean_ctor_get(v___x_1193_, 3);
v___x_1196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1197_ = lean_name_eq(v_kind_1194_, v___x_1196_);
if (v___x_1197_ == 0)
{
v_i_1187_ = v___x_1192_;
goto _start;
}
else
{
lean_object* v_config_1199_; lean_object* v_dir_1200_; lean_object* v_srcDir_1201_; lean_object* v_srcDir_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_config_1199_ = lean_ctor_get(v_x2_1185_, 6);
v_dir_1200_ = lean_ctor_get(v_x2_1185_, 4);
v_srcDir_1201_ = lean_ctor_get(v_config_1199_, 4);
v_srcDir_1202_ = lean_ctor_get(v_config_1195_, 1);
lean_inc_ref(v_srcDir_1201_);
v___x_1203_ = l_System_FilePath_normalize(v_srcDir_1201_);
lean_inc_ref(v_dir_1200_);
v___x_1204_ = l_Lake_joinRelative(v_dir_1200_, v___x_1203_);
lean_inc_ref(v_srcDir_1202_);
v___x_1205_ = l_Lake_joinRelative(v___x_1204_, v_srcDir_1202_);
v___x_1206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v_b_1189_);
v_i_1187_ = v___x_1192_;
v_b_1189_ = v___x_1206_;
goto _start;
}
}
else
{
lean_dec_ref(v_x2_1185_);
return v_b_1189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1208_, lean_object* v_as_1209_, lean_object* v_i_1210_, lean_object* v_stop_1211_, lean_object* v_b_1212_){
_start:
{
size_t v_i_boxed_1213_; size_t v_stop_boxed_1214_; lean_object* v_res_1215_; 
v_i_boxed_1213_ = lean_unbox_usize(v_i_1210_);
lean_dec(v_i_1210_);
v_stop_boxed_1214_ = lean_unbox_usize(v_stop_1211_);
lean_dec(v_stop_1211_);
v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1208_, v_as_1209_, v_i_boxed_1213_, v_stop_boxed_1214_, v_b_1212_);
lean_dec_ref(v_as_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1216_, size_t v_i_1217_, size_t v_stop_1218_, lean_object* v_b_1219_){
_start:
{
lean_object* v___y_1221_; uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_eq(v_i_1217_, v_stop_1218_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v_targetDecls_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1226_ = lean_array_uget_borrowed(v_as_1216_, v_i_1217_);
v_targetDecls_1227_ = lean_ctor_get(v___x_1226_, 15);
v___x_1228_ = lean_array_get_size(v_targetDecls_1227_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_nat_dec_lt(v___x_1229_, v___x_1228_);
if (v___x_1230_ == 0)
{
v___y_1221_ = v_b_1219_;
goto v___jp_1220_;
}
else
{
size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_usize_of_nat(v___x_1228_);
v___x_1232_ = ((size_t)0ULL);
lean_inc(v___x_1226_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1226_, v_targetDecls_1227_, v___x_1231_, v___x_1232_, v_b_1219_);
v___y_1221_ = v___x_1233_;
goto v___jp_1220_;
}
}
else
{
return v_b_1219_;
}
v___jp_1220_:
{
size_t v___x_1222_; size_t v___x_1223_; 
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1217_, v___x_1222_);
v_i_1217_ = v___x_1223_;
v_b_1219_ = v___y_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1234_, lean_object* v_i_1235_, lean_object* v_stop_1236_, lean_object* v_b_1237_){
_start:
{
size_t v_i_boxed_1238_; size_t v_stop_boxed_1239_; lean_object* v_res_1240_; 
v_i_boxed_1238_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_stop_boxed_1239_ = lean_unbox_usize(v_stop_1236_);
lean_dec(v_stop_1236_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1234_, v_i_boxed_1238_, v_stop_boxed_1239_, v_b_1237_);
lean_dec_ref(v_as_1234_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1241_){
_start:
{
lean_object* v_packages_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_packages_1242_ = lean_ctor_get(v_self_1241_, 4);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_array_get_size(v_packages_1242_);
v___x_1246_ = lean_nat_dec_lt(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
return v___x_1243_;
}
else
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_nat_dec_le(v___x_1245_, v___x_1245_);
if (v___x_1247_ == 0)
{
if (v___x_1246_ == 0)
{
return v___x_1243_;
}
else
{
size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = lean_usize_of_nat(v___x_1245_);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1242_, v___x_1248_, v___x_1249_, v___x_1243_);
return v___x_1250_;
}
}
else
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = ((size_t)0ULL);
v___x_1252_ = lean_usize_of_nat(v___x_1245_);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1242_, v___x_1251_, v___x_1252_, v___x_1243_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lake_Workspace_leanSrcPath(v_self_1254_);
lean_dec_ref(v_self_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1256_, size_t v_i_1257_, size_t v_stop_1258_, lean_object* v_b_1259_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_usize_dec_eq(v_i_1257_, v_stop_1258_);
if (v___x_1260_ == 0)
{
size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; lean_object* v_config_1264_; lean_object* v_dir_1265_; lean_object* v_buildDir_1266_; lean_object* v_nativeLibDir_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_sub(v_i_1257_, v___x_1261_);
v___x_1263_ = lean_array_uget_borrowed(v_as_1256_, v___x_1262_);
v_config_1264_ = lean_ctor_get(v___x_1263_, 6);
v_dir_1265_ = lean_ctor_get(v___x_1263_, 4);
v_buildDir_1266_ = lean_ctor_get(v_config_1264_, 5);
v_nativeLibDir_1267_ = lean_ctor_get(v_config_1264_, 7);
lean_inc_ref(v_buildDir_1266_);
v___x_1268_ = l_System_FilePath_normalize(v_buildDir_1266_);
lean_inc_ref(v_dir_1265_);
v___x_1269_ = l_Lake_joinRelative(v_dir_1265_, v___x_1268_);
lean_inc_ref(v_nativeLibDir_1267_);
v___x_1270_ = l_System_FilePath_normalize(v_nativeLibDir_1267_);
v___x_1271_ = l_Lake_joinRelative(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_b_1259_);
v_i_1257_ = v___x_1262_;
v_b_1259_ = v___x_1272_;
goto _start;
}
else
{
return v_b_1259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1274_, lean_object* v_i_1275_, lean_object* v_stop_1276_, lean_object* v_b_1277_){
_start:
{
size_t v_i_boxed_1278_; size_t v_stop_boxed_1279_; lean_object* v_res_1280_; 
v_i_boxed_1278_ = lean_unbox_usize(v_i_1275_);
lean_dec(v_i_1275_);
v_stop_boxed_1279_ = lean_unbox_usize(v_stop_1276_);
lean_dec(v_stop_1276_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1274_, v_i_boxed_1278_, v_stop_boxed_1279_, v_b_1277_);
lean_dec_ref(v_as_1274_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1281_){
_start:
{
lean_object* v_packages_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_packages_1282_ = lean_ctor_get(v_self_1281_, 4);
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_array_get_size(v_packages_1282_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_nat_dec_lt(v___x_1285_, v___x_1284_);
if (v___x_1286_ == 0)
{
return v___x_1283_;
}
else
{
size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_usize_of_nat(v___x_1284_);
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1282_, v___x_1287_, v___x_1288_, v___x_1283_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lake_Workspace_sharedLibPath(v_self_1290_);
lean_dec_ref(v_self_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_System_Platform_isWindows;
if (v___x_1293_ == 0)
{
lean_object* v_lakeEnv_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_lakeEnv_1294_ = lean_ctor_get(v_self_1292_, 0);
v___x_1295_ = l_Lake_Workspace_binPath(v_self_1292_);
v___x_1296_ = l_Lake_Env_path(v_lakeEnv_1294_);
v___x_1297_ = l_List_appendTR___redArg(v___x_1295_, v___x_1296_);
return v___x_1297_;
}
else
{
lean_object* v_lakeEnv_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_lakeEnv_1298_ = lean_ctor_get(v_self_1292_, 0);
v___x_1299_ = l_Lake_Workspace_binPath(v_self_1292_);
v___x_1300_ = l_Lake_Workspace_sharedLibPath(v_self_1292_);
v___x_1301_ = l_List_appendTR___redArg(v___x_1299_, v___x_1300_);
v___x_1302_ = l_Lake_Env_path(v_lakeEnv_1298_);
v___x_1303_ = l_List_appendTR___redArg(v___x_1301_, v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lake_Workspace_augmentedPath(v_self_1304_);
lean_dec_ref(v_self_1304_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1306_){
_start:
{
lean_object* v_lakeEnv_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_lakeEnv_1307_ = lean_ctor_get(v_self_1306_, 0);
v___x_1308_ = l_Lake_Workspace_leanPath(v_self_1306_);
v___x_1309_ = l_Lake_Env_leanPath(v_lakeEnv_1307_);
v___x_1310_ = l_List_appendTR___redArg(v___x_1308_, v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lake_Workspace_augmentedLeanPath(v_self_1311_);
lean_dec_ref(v_self_1311_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1313_){
_start:
{
lean_object* v_lakeEnv_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_lakeEnv_1314_ = lean_ctor_get(v_self_1313_, 0);
v___x_1315_ = l_Lake_Workspace_leanSrcPath(v_self_1313_);
v___x_1316_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1314_);
v___x_1317_ = l_List_appendTR___redArg(v___x_1315_, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1318_);
lean_dec_ref(v_self_1318_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1320_){
_start:
{
lean_object* v_lakeEnv_1321_; lean_object* v_lean_1322_; lean_object* v_initSharedLibPath_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_lakeEnv_1321_ = lean_ctor_get(v_self_1320_, 0);
v_lean_1322_ = lean_ctor_get(v_lakeEnv_1321_, 1);
v_initSharedLibPath_1323_ = lean_ctor_get(v_lakeEnv_1321_, 17);
lean_inc(v_initSharedLibPath_1323_);
v___x_1324_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1322_);
v___x_1325_ = l_Lake_Workspace_sharedLibPath(v_self_1320_);
lean_dec_ref(v_self_1320_);
v___x_1326_ = l_List_appendTR___redArg(v___x_1324_, v___x_1325_);
v___x_1327_ = l_List_appendTR___redArg(v___x_1326_, v_initSharedLibPath_1323_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0(lean_object* v_x_1331_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__0___closed__1));
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0___boxed(lean_object* v_x_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_x_1333_);
lean_dec(v_x_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1(uint8_t v_b_1341_){
_start:
{
if (v_b_1341_ == 0)
{
lean_object* v___x_1342_; 
v___x_1342_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__1));
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; 
v___x_1343_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__3));
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___boxed(lean_object* v_b_1344_){
_start:
{
uint8_t v_b_boxed_1345_; lean_object* v_res_1346_; 
v_b_boxed_1345_ = lean_unbox(v_b_1344_);
v_res_1346_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_b_boxed_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1354_){
_start:
{
lean_object* v_lakeEnv_1355_; lean_object* v_lakeCache_1356_; lean_object* v_packages_1357_; lean_object* v_enableArtifactCache_x3f_1358_; lean_object* v_restoreAllArtifacts_x3f_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1418_; lean_object* v___y_1419_; uint8_t v_val_1420_; lean_object* v___x_1422_; lean_object* v___y_1424_; uint8_t v_val_1437_; 
v_lakeEnv_1355_ = lean_ctor_get(v_self_1354_, 0);
v_lakeCache_1356_ = lean_ctor_get(v_self_1354_, 2);
v_packages_1357_ = lean_ctor_get(v_self_1354_, 4);
v_enableArtifactCache_x3f_1358_ = lean_ctor_get(v_lakeEnv_1355_, 6);
v_restoreAllArtifacts_x3f_1359_ = lean_ctor_get(v_lakeEnv_1355_, 7);
lean_inc_ref(v_lakeEnv_1355_);
v___x_1360_ = l_Lake_Env_baseVars(v_lakeEnv_1355_);
v___x_1361_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1356_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_lakeCache_1356_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1422_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (lean_obj_tag(v_enableArtifactCache_x3f_1358_) == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_config_1441_; lean_object* v_enableArtifactCache_x3f_1442_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_array_fget_borrowed(v_packages_1357_, v___x_1439_);
v_config_1441_ = lean_ctor_get(v___x_1440_, 6);
v_enableArtifactCache_x3f_1442_ = lean_ctor_get(v_config_1441_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1442_) == 1)
{
lean_object* v_val_1443_; uint8_t v___x_1444_; 
v_val_1443_ = lean_ctor_get(v_enableArtifactCache_x3f_1442_, 0);
v___x_1444_ = lean_unbox(v_val_1443_);
v_val_1437_ = v___x_1444_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_enableArtifactCache_x3f_1442_);
v___y_1424_ = v___x_1445_;
goto v___jp_1423_;
}
}
else
{
lean_object* v_val_1446_; uint8_t v___x_1447_; 
v_val_1446_ = lean_ctor_get(v_enableArtifactCache_x3f_1358_, 0);
v___x_1447_ = lean_unbox(v_val_1446_);
v_val_1437_ = v___x_1447_;
goto v___jp_1436_;
}
v___jp_1364_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_vars_1386_; uint8_t v___x_1387_; 
lean_inc_ref(v___y_1367_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___y_1367_);
lean_ctor_set(v___x_1371_, 1, v___y_1370_);
v___x_1372_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1373_ = l_Lake_Workspace_augmentedPath(v_self_1354_);
v___x_1374_ = l_System_SearchPath_toString(v___x_1373_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1372_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_unsigned_to_nat(7u);
v___x_1378_ = lean_mk_empty_array_with_capacity(v___x_1377_);
v___x_1379_ = lean_array_push(v___x_1378_, v___x_1363_);
v___x_1380_ = lean_array_push(v___x_1379_, v___y_1368_);
v___x_1381_ = lean_array_push(v___x_1380_, v___y_1369_);
v___x_1382_ = lean_array_push(v___x_1381_, v___y_1365_);
v___x_1383_ = lean_array_push(v___x_1382_, v___y_1366_);
v___x_1384_ = lean_array_push(v___x_1383_, v___x_1371_);
v___x_1385_ = lean_array_push(v___x_1384_, v___x_1376_);
v_vars_1386_ = l_Array_append___redArg(v___x_1360_, v___x_1385_);
lean_dec_ref(v___x_1385_);
v___x_1387_ = l_System_Platform_isWindows;
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1388_ = l_Lake_sharedLibPathEnvVar;
v___x_1389_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1354_);
v___x_1390_ = l_System_SearchPath_toString(v___x_1389_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1388_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_array_push(v_vars_1386_, v___x_1392_);
return v___x_1393_;
}
else
{
lean_dec_ref(v_self_1354_);
return v_vars_1386_;
}
}
v___jp_1394_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_config_1400_; uint8_t v_bootstrap_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = lean_array_fget_borrowed(v_packages_1357_, v___x_1398_);
v_config_1400_ = lean_ctor_get(v___x_1399_, 6);
v_bootstrap_1401_ = lean_ctor_get_uint8(v_config_1400_, sizeof(void*)*28);
lean_inc_ref(v___y_1396_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___y_1396_);
lean_ctor_set(v___x_1402_, 1, v___y_1397_);
v___x_1403_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
v___x_1404_ = l_Lake_Workspace_augmentedLeanPath(v_self_1354_);
v___x_1405_ = l_System_SearchPath_toString(v___x_1404_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1403_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1409_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1354_);
v___x_1410_ = l_System_SearchPath_toString(v___x_1409_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1408_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
if (v_bootstrap_1401_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = l_Lake_Env_leanGithash(v_lakeEnv_1355_);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
v___y_1365_ = v___x_1407_;
v___y_1366_ = v___x_1412_;
v___y_1367_ = v___x_1413_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___x_1402_;
v___y_1370_ = v___x_1415_;
goto v___jp_1364_;
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_box(0);
v___y_1365_ = v___x_1407_;
v___y_1366_ = v___x_1412_;
v___y_1367_ = v___x_1413_;
v___y_1368_ = v___y_1395_;
v___y_1369_ = v___x_1402_;
v___y_1370_ = v___x_1416_;
goto v___jp_1364_;
}
}
v___jp_1417_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1420_);
v___y_1395_ = v___y_1418_;
v___y_1396_ = v___y_1419_;
v___y_1397_ = v___x_1421_;
goto v___jp_1394_;
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1422_);
lean_ctor_set(v___x_1425_, 1, v___y_1424_);
v___x_1426_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__6));
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1359_) == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_config_1429_; lean_object* v_restoreAllArtifacts_x3f_1430_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_array_fget_borrowed(v_packages_1357_, v___x_1427_);
v_config_1429_ = lean_ctor_get(v___x_1428_, 6);
v_restoreAllArtifacts_x3f_1430_ = lean_ctor_get(v_config_1429_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1430_) == 1)
{
lean_object* v_val_1431_; uint8_t v___x_1432_; 
v_val_1431_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1430_, 0);
v___x_1432_ = lean_unbox(v_val_1431_);
v___y_1418_ = v___x_1425_;
v___y_1419_ = v___x_1426_;
v_val_1420_ = v___x_1432_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_restoreAllArtifacts_x3f_1430_);
v___y_1395_ = v___x_1425_;
v___y_1396_ = v___x_1426_;
v___y_1397_ = v___x_1433_;
goto v___jp_1394_;
}
}
else
{
lean_object* v_val_1434_; uint8_t v___x_1435_; 
v_val_1434_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1359_, 0);
v___x_1435_ = lean_unbox(v_val_1434_);
v___y_1418_ = v___x_1425_;
v___y_1419_ = v___x_1426_;
v_val_1420_ = v___x_1435_;
goto v___jp_1417_;
}
}
v___jp_1436_:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1437_);
v___y_1424_ = v___x_1438_;
goto v___jp_1423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1448_, size_t v_i_1449_, size_t v_stop_1450_, lean_object* v_b_1451_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_eq(v_i_1449_, v_stop_1450_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_array_uget_borrowed(v_as_1448_, v_i_1449_);
lean_inc(v___x_1454_);
v___x_1455_ = l_Lake_Package_clean(v___x_1454_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; size_t v___x_1457_; size_t v___x_1458_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = ((size_t)1ULL);
v___x_1458_ = lean_usize_add(v_i_1449_, v___x_1457_);
v_i_1449_ = v___x_1458_;
v_b_1451_ = v_a_1456_;
goto _start;
}
else
{
return v___x_1455_;
}
}
else
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_b_1451_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1461_, lean_object* v_i_1462_, lean_object* v_stop_1463_, lean_object* v_b_1464_, lean_object* v___y_1465_){
_start:
{
size_t v_i_boxed_1466_; size_t v_stop_boxed_1467_; lean_object* v_res_1468_; 
v_i_boxed_1466_ = lean_unbox_usize(v_i_1462_);
lean_dec(v_i_1462_);
v_stop_boxed_1467_ = lean_unbox_usize(v_stop_1463_);
lean_dec(v_stop_1463_);
v_res_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1461_, v_i_boxed_1466_, v_stop_boxed_1467_, v_b_1464_);
lean_dec_ref(v_as_1461_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* v_self_1469_){
_start:
{
lean_object* v_packages_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v_packages_1471_ = lean_ctor_get(v_self_1469_, 4);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_array_get_size(v_packages_1471_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_nat_dec_lt(v___x_1472_, v___x_1473_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
return v___x_1476_;
}
else
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_nat_dec_le(v___x_1473_, v___x_1473_);
if (v___x_1477_ == 0)
{
if (v___x_1475_ == 0)
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1474_);
return v___x_1478_;
}
else
{
size_t v___x_1479_; size_t v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = ((size_t)0ULL);
v___x_1480_ = lean_usize_of_nat(v___x_1473_);
v___x_1481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1471_, v___x_1479_, v___x_1480_, v___x_1474_);
return v___x_1481_;
}
}
else
{
size_t v___x_1482_; size_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = lean_usize_of_nat(v___x_1473_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1471_, v___x_1482_, v___x_1483_, v___x_1474_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lake_Workspace_clean(v_self_1485_);
lean_dec_ref(v_self_1485_);
return v_res_1487_;
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

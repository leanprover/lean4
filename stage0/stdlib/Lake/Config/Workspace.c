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
v_bootstrap_5_ = lean_ctor_get_uint8(v_config_4_, sizeof(void*)*27);
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
uint8_t v___x_92_; 
v___x_92_ = lean_nat_dec_le(v___x_90_, v___x_90_);
if (v___x_92_ == 0)
{
if (v___x_91_ == 0)
{
return v___x_89_;
}
else
{
size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_90_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_86_, v_defaultTargets_87_, v___x_93_, v___x_94_, v___x_89_);
return v___x_95_;
}
}
else
{
size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((size_t)0ULL);
v___x_97_ = lean_usize_of_nat(v___x_90_);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_86_, v_defaultTargets_87_, v___x_96_, v___x_97_, v___x_89_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots___boxed(lean_object* v_self_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lake_Package_defaultTargetRoots(v_self_99_);
lean_dec_ref(v_self_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_root(lean_object* v_self_101_){
_start:
{
lean_object* v_packages_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_packages_102_ = lean_ctor_get(v_self_101_, 4);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_array_fget_borrowed(v_packages_102_, v___x_103_);
lean_inc(v___x_104_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_root___boxed(lean_object* v_self_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lake_Workspace_root(v_self_105_);
lean_dec_ref(v_self_105_);
return v_res_106_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(lean_object* v_self_107_){
_start:
{
lean_object* v_packages_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_config_111_; uint8_t v_bootstrap_112_; 
v_packages_108_ = lean_ctor_get(v_self_107_, 4);
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_array_fget_borrowed(v_packages_108_, v___x_109_);
v_config_111_ = lean_ctor_get(v___x_110_, 6);
v_bootstrap_112_ = lean_ctor_get_uint8(v_config_111_, sizeof(void*)*27);
return v_bootstrap_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(lean_object* v_self_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(v_self_113_);
lean_dec_ref(v_self_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object* v_self_116_){
_start:
{
lean_object* v_packages_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_dir_120_; 
v_packages_117_ = lean_ctor_get(v_self_116_, 4);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_array_fget_borrowed(v_packages_117_, v___x_118_);
v_dir_120_ = lean_ctor_get(v___x_119_, 4);
lean_inc_ref(v_dir_120_);
return v_dir_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object* v_self_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lake_Workspace_dir(v_self_121_);
lean_dec_ref(v_self_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object* v_self_123_){
_start:
{
lean_object* v_packages_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_config_127_; lean_object* v_toWorkspaceConfig_128_; 
v_packages_124_ = lean_ctor_get(v_self_123_, 4);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_array_fget_borrowed(v_packages_124_, v___x_125_);
v_config_127_ = lean_ctor_get(v___x_126_, 6);
v_toWorkspaceConfig_128_ = lean_ctor_get(v_config_127_, 0);
lean_inc_ref(v_toWorkspaceConfig_128_);
return v_toWorkspaceConfig_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object* v_self_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lake_Workspace_config(v_self_129_);
lean_dec_ref(v_self_129_);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object* v_ws_216_, lean_object* v_service_217_){
_start:
{
lean_object* v_lakeConfig_218_; lean_object* v_cacheServices_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_lakeConfig_218_ = lean_ctor_get(v_ws_216_, 1);
v_cacheServices_219_ = lean_ctor_get(v_lakeConfig_218_, 3);
v___x_220_ = lean_box(0);
v___x_221_ = l_Lean_Name_str___override(v___x_220_, v_service_217_);
v___x_222_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_219_, v___x_221_);
lean_dec(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object* v_ws_223_, lean_object* v_service_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lake_Workspace_findCacheService_x3f(v_ws_223_, v_service_224_);
lean_dec_ref(v_ws_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* v_self_226_){
_start:
{
lean_object* v_packages_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_config_230_; lean_object* v_toWorkspaceConfig_231_; lean_object* v___x_232_; 
v_packages_227_ = lean_ctor_get(v_self_226_, 4);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_array_fget_borrowed(v_packages_227_, v___x_228_);
v_config_230_ = lean_ctor_get(v___x_229_, 6);
v_toWorkspaceConfig_231_ = lean_ctor_get(v_config_230_, 0);
lean_inc_ref(v_toWorkspaceConfig_231_);
v___x_232_ = l_System_FilePath_normalize(v_toWorkspaceConfig_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir___boxed(lean_object* v_self_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lake_Workspace_relPkgsDir(v_self_233_);
lean_dec_ref(v_self_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* v_self_235_){
_start:
{
lean_object* v_packages_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_config_239_; lean_object* v_dir_240_; lean_object* v_toWorkspaceConfig_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_packages_236_ = lean_ctor_get(v_self_235_, 4);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_array_fget_borrowed(v_packages_236_, v___x_237_);
v_config_239_ = lean_ctor_get(v___x_238_, 6);
v_dir_240_ = lean_ctor_get(v___x_238_, 4);
v_toWorkspaceConfig_241_ = lean_ctor_get(v_config_239_, 0);
lean_inc_ref(v_toWorkspaceConfig_241_);
v___x_242_ = l_System_FilePath_normalize(v_toWorkspaceConfig_241_);
lean_inc_ref(v_dir_240_);
v___x_243_ = l_Lake_joinRelative(v_dir_240_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir___boxed(lean_object* v_self_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_Workspace_pkgsDir(v_self_244_);
lean_dec_ref(v_self_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object* v_self_246_){
_start:
{
lean_object* v_packages_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_config_250_; lean_object* v_toLeanConfig_251_; lean_object* v_moreLeanArgs_252_; 
v_packages_247_ = lean_ctor_get(v_self_246_, 4);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_array_fget_borrowed(v_packages_247_, v___x_248_);
v_config_250_ = lean_ctor_get(v___x_249_, 6);
v_toLeanConfig_251_ = lean_ctor_get(v_config_250_, 1);
v_moreLeanArgs_252_ = lean_ctor_get(v_toLeanConfig_251_, 1);
lean_inc_ref(v_moreLeanArgs_252_);
return v_moreLeanArgs_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object* v_self_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lake_Workspace_leanArgs(v_self_253_);
lean_dec_ref(v_self_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* v_self_255_){
_start:
{
lean_object* v_packages_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_config_259_; lean_object* v_toLeanConfig_260_; lean_object* v_leanOptions_261_; lean_object* v___x_262_; 
v_packages_256_ = lean_ctor_get(v_self_255_, 4);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_array_fget_borrowed(v_packages_256_, v___x_257_);
v_config_259_ = lean_ctor_get(v___x_258_, 6);
v_toLeanConfig_260_ = lean_ctor_get(v_config_259_, 1);
v_leanOptions_261_ = lean_ctor_get(v_toLeanConfig_260_, 0);
v___x_262_ = l_Lean_LeanOptions_ofArray(v_leanOptions_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* v_self_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lake_Workspace_leanOptions(v_self_263_);
lean_dec_ref(v_self_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* v_self_265_){
_start:
{
lean_object* v_packages_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_config_269_; lean_object* v_toLeanConfig_270_; lean_object* v_leanOptions_271_; lean_object* v_moreServerOptions_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_packages_266_ = lean_ctor_get(v_self_265_, 4);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_array_fget_borrowed(v_packages_266_, v___x_267_);
v_config_269_ = lean_ctor_get(v___x_268_, 6);
v_toLeanConfig_270_ = lean_ctor_get(v_config_269_, 1);
v_leanOptions_271_ = lean_ctor_get(v_toLeanConfig_270_, 0);
v_moreServerOptions_272_ = lean_ctor_get(v_toLeanConfig_270_, 4);
v___x_273_ = l_Lean_LeanOptions_ofArray(v_leanOptions_271_);
v___x_274_ = l_Lean_LeanOptions_appendArray(v___x_273_, v_moreServerOptions_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* v_self_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lake_Workspace_serverOptions(v_self_275_);
lean_dec_ref(v_self_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object* v_self_277_){
_start:
{
lean_object* v_packages_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_packages_278_ = lean_ctor_get(v_self_277_, 4);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_array_fget_borrowed(v_packages_278_, v___x_279_);
v___x_281_ = l_Lake_Package_defaultTargetRoots(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object* v_self_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lake_Workspace_defaultTargetRoots(v_self_282_);
lean_dec_ref(v_self_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* v_self_284_){
_start:
{
lean_object* v_packages_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_dir_288_; lean_object* v_relManifestFile_289_; lean_object* v___x_290_; 
v_packages_285_ = lean_ctor_get(v_self_284_, 4);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_array_fget_borrowed(v_packages_285_, v___x_286_);
v_dir_288_ = lean_ctor_get(v___x_287_, 4);
v_relManifestFile_289_ = lean_ctor_get(v___x_287_, 9);
lean_inc_ref(v_relManifestFile_289_);
lean_inc_ref(v_dir_288_);
v___x_290_ = l_Lake_joinRelative(v_dir_288_, v_relManifestFile_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile___boxed(lean_object* v_self_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lake_Workspace_manifestFile(v_self_291_);
lean_dec_ref(v_self_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* v_self_294_){
_start:
{
lean_object* v_packages_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_dir_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_packages_295_ = lean_ctor_get(v_self_294_, 4);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_array_fget_borrowed(v_packages_295_, v___x_296_);
v_dir_298_ = lean_ctor_get(v___x_297_, 4);
v___x_299_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_298_);
v___x_300_ = l_Lake_joinRelative(v_dir_298_, v___x_299_);
v___x_301_ = ((lean_object*)(l_Lake_Workspace_packageOverridesFile___closed__0));
v___x_302_ = l_Lake_joinRelative(v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile___boxed(lean_object* v_self_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lake_Workspace_packageOverridesFile(v_self_303_);
lean_dec_ref(v_self_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object* v_pkg_306_, lean_object* v_self_307_){
_start:
{
lean_object* v_lakeEnv_308_; lean_object* v_lakeConfig_309_; lean_object* v_lakeCache_310_; lean_object* v_lakeArgs_x3f_311_; lean_object* v_packages_312_; lean_object* v_packageMap_313_; lean_object* v_facetConfigs_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_325_; 
v_lakeEnv_308_ = lean_ctor_get(v_self_307_, 0);
v_lakeConfig_309_ = lean_ctor_get(v_self_307_, 1);
v_lakeCache_310_ = lean_ctor_get(v_self_307_, 2);
v_lakeArgs_x3f_311_ = lean_ctor_get(v_self_307_, 3);
v_packages_312_ = lean_ctor_get(v_self_307_, 4);
v_packageMap_313_ = lean_ctor_get(v_self_307_, 5);
v_facetConfigs_314_ = lean_ctor_get(v_self_307_, 6);
v_isSharedCheck_325_ = !lean_is_exclusive(v_self_307_);
if (v_isSharedCheck_325_ == 0)
{
v___x_316_ = v_self_307_;
v_isShared_317_ = v_isSharedCheck_325_;
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
lean_dec(v_self_307_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_325_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_keyName_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v_keyName_318_ = lean_ctor_get(v_pkg_306_, 2);
lean_inc(v_keyName_318_);
lean_inc_ref(v_pkg_306_);
v___x_319_ = lean_array_push(v_packages_312_, v_pkg_306_);
v___x_320_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_321_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_320_, v_keyName_318_, v_pkg_306_, v_packageMap_313_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 5, v___x_321_);
lean_ctor_set(v___x_316_, 4, v___x_319_);
v___x_323_ = v___x_316_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_lakeEnv_308_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_lakeConfig_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_lakeCache_310_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_lakeArgs_x3f_311_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_324_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_324_, 6, v_facetConfigs_314_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object* v_pkg_326_, lean_object* v_self_327_, lean_object* v_h__wsIdx_328_, lean_object* v_h__depIdxs_329_){
_start:
{
lean_object* v_lakeEnv_330_; lean_object* v_lakeConfig_331_; lean_object* v_lakeCache_332_; lean_object* v_lakeArgs_x3f_333_; lean_object* v_packages_334_; lean_object* v_packageMap_335_; lean_object* v_facetConfigs_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_347_; 
v_lakeEnv_330_ = lean_ctor_get(v_self_327_, 0);
v_lakeConfig_331_ = lean_ctor_get(v_self_327_, 1);
v_lakeCache_332_ = lean_ctor_get(v_self_327_, 2);
v_lakeArgs_x3f_333_ = lean_ctor_get(v_self_327_, 3);
v_packages_334_ = lean_ctor_get(v_self_327_, 4);
v_packageMap_335_ = lean_ctor_get(v_self_327_, 5);
v_facetConfigs_336_ = lean_ctor_get(v_self_327_, 6);
v_isSharedCheck_347_ = !lean_is_exclusive(v_self_327_);
if (v_isSharedCheck_347_ == 0)
{
v___x_338_ = v_self_327_;
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_facetConfigs_336_);
lean_inc(v_packageMap_335_);
lean_inc(v_packages_334_);
lean_inc(v_lakeArgs_x3f_333_);
lean_inc(v_lakeCache_332_);
lean_inc(v_lakeConfig_331_);
lean_inc(v_lakeEnv_330_);
lean_dec(v_self_327_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_347_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v_keyName_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_345_; 
v_keyName_340_ = lean_ctor_get(v_pkg_326_, 2);
lean_inc(v_keyName_340_);
lean_inc_ref(v_pkg_326_);
v___x_341_ = lean_array_push(v_packages_334_, v_pkg_326_);
v___x_342_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_343_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_342_, v_keyName_340_, v_pkg_326_, v_packageMap_335_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 5, v___x_343_);
lean_ctor_set(v___x_338_, 4, v___x_341_);
v___x_345_ = v___x_338_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_lakeEnv_330_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_lakeConfig_331_);
lean_ctor_set(v_reuseFailAlloc_346_, 2, v_lakeCache_332_);
lean_ctor_set(v_reuseFailAlloc_346_, 3, v_lakeArgs_x3f_333_);
lean_ctor_set(v_reuseFailAlloc_346_, 4, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_346_, 5, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_346_, 6, v_facetConfigs_336_);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_350_, lean_object* v_self_351_){
_start:
{
lean_object* v_lakeEnv_352_; lean_object* v_lakeConfig_353_; lean_object* v_lakeCache_354_; lean_object* v_lakeArgs_x3f_355_; lean_object* v_packages_356_; lean_object* v_packageMap_357_; lean_object* v_facetConfigs_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_401_; 
v_lakeEnv_352_ = lean_ctor_get(v_self_351_, 0);
v_lakeConfig_353_ = lean_ctor_get(v_self_351_, 1);
v_lakeCache_354_ = lean_ctor_get(v_self_351_, 2);
v_lakeArgs_x3f_355_ = lean_ctor_get(v_self_351_, 3);
v_packages_356_ = lean_ctor_get(v_self_351_, 4);
v_packageMap_357_ = lean_ctor_get(v_self_351_, 5);
v_facetConfigs_358_ = lean_ctor_get(v_self_351_, 6);
v_isSharedCheck_401_ = !lean_is_exclusive(v_self_351_);
if (v_isSharedCheck_401_ == 0)
{
v___x_360_ = v_self_351_;
v_isShared_361_ = v_isSharedCheck_401_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_facetConfigs_358_);
lean_inc(v_packageMap_357_);
lean_inc(v_packages_356_);
lean_inc(v_lakeArgs_x3f_355_);
lean_inc(v_lakeCache_354_);
lean_inc(v_lakeConfig_353_);
lean_inc(v_lakeEnv_352_);
lean_dec(v_self_351_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_401_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_baseName_362_; lean_object* v_keyName_363_; lean_object* v_origName_364_; lean_object* v_dir_365_; lean_object* v_relDir_366_; lean_object* v_config_367_; lean_object* v_configFile_368_; lean_object* v_relConfigFile_369_; lean_object* v_relManifestFile_370_; lean_object* v_scope_371_; lean_object* v_remoteUrl_372_; lean_object* v_depConfigs_373_; lean_object* v_depPkgs_374_; lean_object* v_targetDecls_375_; lean_object* v_targetDeclMap_376_; lean_object* v_defaultTargets_377_; lean_object* v_scripts_378_; lean_object* v_defaultScripts_379_; lean_object* v_postUpdateHooks_380_; lean_object* v_buildArchive_381_; lean_object* v_testDriver_382_; lean_object* v_lintDriver_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_398_; 
v_baseName_362_ = lean_ctor_get(v_pkg_350_, 1);
v_keyName_363_ = lean_ctor_get(v_pkg_350_, 2);
v_origName_364_ = lean_ctor_get(v_pkg_350_, 3);
v_dir_365_ = lean_ctor_get(v_pkg_350_, 4);
v_relDir_366_ = lean_ctor_get(v_pkg_350_, 5);
v_config_367_ = lean_ctor_get(v_pkg_350_, 6);
v_configFile_368_ = lean_ctor_get(v_pkg_350_, 7);
v_relConfigFile_369_ = lean_ctor_get(v_pkg_350_, 8);
v_relManifestFile_370_ = lean_ctor_get(v_pkg_350_, 9);
v_scope_371_ = lean_ctor_get(v_pkg_350_, 10);
v_remoteUrl_372_ = lean_ctor_get(v_pkg_350_, 11);
v_depConfigs_373_ = lean_ctor_get(v_pkg_350_, 12);
v_depPkgs_374_ = lean_ctor_get(v_pkg_350_, 14);
v_targetDecls_375_ = lean_ctor_get(v_pkg_350_, 15);
v_targetDeclMap_376_ = lean_ctor_get(v_pkg_350_, 16);
v_defaultTargets_377_ = lean_ctor_get(v_pkg_350_, 17);
v_scripts_378_ = lean_ctor_get(v_pkg_350_, 18);
v_defaultScripts_379_ = lean_ctor_get(v_pkg_350_, 19);
v_postUpdateHooks_380_ = lean_ctor_get(v_pkg_350_, 20);
v_buildArchive_381_ = lean_ctor_get(v_pkg_350_, 21);
v_testDriver_382_ = lean_ctor_get(v_pkg_350_, 22);
v_lintDriver_383_ = lean_ctor_get(v_pkg_350_, 23);
v_isSharedCheck_398_ = !lean_is_exclusive(v_pkg_350_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; lean_object* v_unused_400_; 
v_unused_399_ = lean_ctor_get(v_pkg_350_, 13);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_pkg_350_, 0);
lean_dec(v_unused_400_);
v___x_385_ = v_pkg_350_;
v_isShared_386_ = v_isSharedCheck_398_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_lintDriver_383_);
lean_inc(v_testDriver_382_);
lean_inc(v_buildArchive_381_);
lean_inc(v_postUpdateHooks_380_);
lean_inc(v_defaultScripts_379_);
lean_inc(v_scripts_378_);
lean_inc(v_defaultTargets_377_);
lean_inc(v_targetDeclMap_376_);
lean_inc(v_targetDecls_375_);
lean_inc(v_depPkgs_374_);
lean_inc(v_depConfigs_373_);
lean_inc(v_remoteUrl_372_);
lean_inc(v_scope_371_);
lean_inc(v_relManifestFile_370_);
lean_inc(v_relConfigFile_369_);
lean_inc(v_configFile_368_);
lean_inc(v_config_367_);
lean_inc(v_relDir_366_);
lean_inc(v_dir_365_);
lean_inc(v_origName_364_);
lean_inc(v_keyName_363_);
lean_inc(v_baseName_362_);
lean_dec(v_pkg_350_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_398_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = lean_array_get_size(v_packages_356_);
v___x_388_ = ((lean_object*)(l_Lake_Workspace_addPackage___closed__0));
lean_inc(v_keyName_363_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 13, v___x_388_);
lean_ctor_set(v___x_385_, 0, v___x_387_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_baseName_362_);
lean_ctor_set(v_reuseFailAlloc_397_, 2, v_keyName_363_);
lean_ctor_set(v_reuseFailAlloc_397_, 3, v_origName_364_);
lean_ctor_set(v_reuseFailAlloc_397_, 4, v_dir_365_);
lean_ctor_set(v_reuseFailAlloc_397_, 5, v_relDir_366_);
lean_ctor_set(v_reuseFailAlloc_397_, 6, v_config_367_);
lean_ctor_set(v_reuseFailAlloc_397_, 7, v_configFile_368_);
lean_ctor_set(v_reuseFailAlloc_397_, 8, v_relConfigFile_369_);
lean_ctor_set(v_reuseFailAlloc_397_, 9, v_relManifestFile_370_);
lean_ctor_set(v_reuseFailAlloc_397_, 10, v_scope_371_);
lean_ctor_set(v_reuseFailAlloc_397_, 11, v_remoteUrl_372_);
lean_ctor_set(v_reuseFailAlloc_397_, 12, v_depConfigs_373_);
lean_ctor_set(v_reuseFailAlloc_397_, 13, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_397_, 14, v_depPkgs_374_);
lean_ctor_set(v_reuseFailAlloc_397_, 15, v_targetDecls_375_);
lean_ctor_set(v_reuseFailAlloc_397_, 16, v_targetDeclMap_376_);
lean_ctor_set(v_reuseFailAlloc_397_, 17, v_defaultTargets_377_);
lean_ctor_set(v_reuseFailAlloc_397_, 18, v_scripts_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 19, v_defaultScripts_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 20, v_postUpdateHooks_380_);
lean_ctor_set(v_reuseFailAlloc_397_, 21, v_buildArchive_381_);
lean_ctor_set(v_reuseFailAlloc_397_, 22, v_testDriver_382_);
lean_ctor_set(v_reuseFailAlloc_397_, 23, v_lintDriver_383_);
v___x_390_ = v_reuseFailAlloc_397_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
lean_inc_ref(v___x_390_);
v___x_391_ = lean_array_push(v_packages_356_, v___x_390_);
v___x_392_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_393_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_392_, v_keyName_363_, v___x_390_, v_packageMap_357_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 5, v___x_393_);
lean_ctor_set(v___x_360_, 4, v___x_391_);
v___x_395_ = v___x_360_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_lakeEnv_352_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_lakeConfig_353_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_lakeCache_354_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_lakeArgs_x3f_355_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_facetConfigs_358_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_402_, lean_object* v_self_403_){
_start:
{
lean_object* v_packageMap_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_packageMap_404_ = lean_ctor_get(v_self_403_, 5);
lean_inc(v_packageMap_404_);
lean_dec_ref(v_self_403_);
v___x_405_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_406_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_405_, v_packageMap_404_, v_keyName_402_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_407_, lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v_a_410_, lean_object* v_x_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_baseName_413_; uint8_t v___x_414_; 
v_baseName_413_ = lean_ctor_get(v_a_410_, 1);
v___x_414_ = lean_name_eq(v_baseName_413_, v_name_407_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec_ref(v_a_410_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_408_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v___x_408_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_a_410_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_409_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v_a_423_, lean_object* v_x_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_420_, v___x_421_, v___x_422_, v_a_423_, v_x_424_, v___y_425_);
lean_dec_ref(v___y_425_);
lean_dec(v_name_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_449_, lean_object* v_self_450_){
_start:
{
lean_object* v_packages_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___f_456_; size_t v_sz_457_; size_t v___x_458_; lean_object* v___x_459_; lean_object* v_fst_460_; 
v_packages_451_ = lean_ctor_get(v_self_450_, 4);
lean_inc_ref(v_packages_451_);
lean_dec_ref(v_self_450_);
v___x_452_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__9));
v___x_453_ = lean_box(0);
v___x_454_ = lean_box(0);
v___x_455_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__10));
v___f_456_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_456_, 0, v_name_449_);
lean_closure_set(v___f_456_, 1, v___x_455_);
lean_closure_set(v___f_456_, 2, v___x_454_);
v_sz_457_ = lean_array_size(v_packages_451_);
v___x_458_ = ((size_t)0ULL);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_452_, v_packages_451_, v___f_456_, v_sz_457_, v___x_458_, v___x_455_);
v_fst_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_fst_460_);
lean_dec(v___x_459_);
if (lean_obj_tag(v_fst_460_) == 0)
{
return v___x_453_;
}
else
{
lean_object* v_val_461_; 
v_val_461_ = lean_ctor_get(v_fst_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref_known(v_fst_460_, 1);
return v_val_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_462_, lean_object* v_self_463_){
_start:
{
lean_object* v_packageMap_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_packageMap_464_ = lean_ctor_get(v_self_463_, 5);
lean_inc(v_packageMap_464_);
lean_dec_ref(v_self_463_);
v___x_465_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_466_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_465_, v_packageMap_464_, v_name_462_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_470_, lean_object* v_as_471_, size_t v_sz_472_, size_t v_i_473_, lean_object* v_b_474_){
_start:
{
uint8_t v___x_475_; 
v___x_475_ = lean_usize_dec_lt(v_i_473_, v_sz_472_);
if (v___x_475_ == 0)
{
lean_inc_ref(v_b_474_);
return v_b_474_;
}
else
{
lean_object* v_a_476_; lean_object* v_scripts_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_a_476_ = lean_array_uget_borrowed(v_as_471_, v_i_473_);
v_scripts_477_ = lean_ctor_get(v_a_476_, 18);
v___x_478_ = lean_box(0);
v___x_479_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_477_, v_script_470_);
if (lean_obj_tag(v___x_479_) == 1)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_478_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; 
lean_dec(v___x_479_);
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_i_473_, v___x_483_);
v_i_473_ = v___x_484_;
v_b_474_ = v___x_482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_486_, lean_object* v_as_487_, lean_object* v_sz_488_, lean_object* v_i_489_, lean_object* v_b_490_){
_start:
{
size_t v_sz_boxed_491_; size_t v_i_boxed_492_; lean_object* v_res_493_; 
v_sz_boxed_491_ = lean_unbox_usize(v_sz_488_);
lean_dec(v_sz_488_);
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_486_, v_as_487_, v_sz_boxed_491_, v_i_boxed_492_, v_b_490_);
lean_dec_ref(v_b_490_);
lean_dec_ref(v_as_487_);
lean_dec(v_script_486_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_494_, lean_object* v_self_495_){
_start:
{
lean_object* v_packages_496_; lean_object* v___x_497_; lean_object* v___x_498_; size_t v_sz_499_; size_t v___x_500_; lean_object* v___x_501_; lean_object* v_fst_502_; 
v_packages_496_ = lean_ctor_get(v_self_495_, 4);
v___x_497_ = lean_box(0);
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_499_ = lean_array_size(v_packages_496_);
v___x_500_ = ((size_t)0ULL);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_494_, v_packages_496_, v_sz_499_, v___x_500_, v___x_498_);
v_fst_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_fst_502_);
lean_dec_ref(v___x_501_);
if (lean_obj_tag(v_fst_502_) == 0)
{
return v___x_497_;
}
else
{
lean_object* v_val_503_; 
v_val_503_ = lean_ctor_get(v_fst_502_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v_fst_502_, 1);
return v_val_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_504_, lean_object* v_self_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lake_Workspace_findScript_x3f(v_script_504_, v_self_505_);
lean_dec_ref(v_self_505_);
lean_dec(v_script_504_);
return v_res_506_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_507_, lean_object* v_as_508_, size_t v_i_509_, size_t v_stop_510_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_eq(v_i_509_, v_stop_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_array_uget_borrowed(v_as_508_, v_i_509_);
v___x_513_ = l_Lake_Package_isLocalModule(v_mod_507_, v___x_512_);
if (v___x_513_ == 0)
{
size_t v___x_514_; size_t v___x_515_; 
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_509_, v___x_514_);
v_i_509_ = v___x_515_;
goto _start;
}
else
{
return v___x_513_;
}
}
else
{
uint8_t v___x_517_; 
v___x_517_ = 0;
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_stop_521_){
_start:
{
size_t v_i_boxed_522_; size_t v_stop_boxed_523_; uint8_t v_res_524_; lean_object* v_r_525_; 
v_i_boxed_522_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_stop_boxed_523_ = lean_unbox_usize(v_stop_521_);
lean_dec(v_stop_521_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_518_, v_as_519_, v_i_boxed_522_, v_stop_boxed_523_);
lean_dec_ref(v_as_519_);
lean_dec(v_mod_518_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_526_, lean_object* v_self_527_){
_start:
{
lean_object* v_packages_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_packages_528_ = lean_ctor_get(v_self_527_, 4);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_array_get_size(v_packages_528_);
v___x_531_ = lean_nat_dec_lt(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
return v___x_531_;
}
else
{
if (v___x_531_ == 0)
{
return v___x_531_;
}
else
{
size_t v___x_532_; size_t v___x_533_; uint8_t v___x_534_; 
v___x_532_ = ((size_t)0ULL);
v___x_533_ = lean_usize_of_nat(v___x_530_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_526_, v_packages_528_, v___x_532_, v___x_533_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_535_, lean_object* v_self_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Lake_Workspace_isLocalModule(v_mod_535_, v_self_536_);
lean_dec_ref(v_self_536_);
lean_dec(v_mod_535_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_539_, lean_object* v_as_540_, size_t v_i_541_, size_t v_stop_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_eq(v_i_541_, v_stop_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_array_uget_borrowed(v_as_540_, v_i_541_);
v___x_545_ = l_Lake_Package_isBuildableModule(v_mod_539_, v___x_544_);
if (v___x_545_ == 0)
{
size_t v___x_546_; size_t v___x_547_; 
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_541_, v___x_546_);
v_i_541_ = v___x_547_;
goto _start;
}
else
{
return v___x_545_;
}
}
else
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_550_, lean_object* v_as_551_, lean_object* v_i_552_, lean_object* v_stop_553_){
_start:
{
size_t v_i_boxed_554_; size_t v_stop_boxed_555_; uint8_t v_res_556_; lean_object* v_r_557_; 
v_i_boxed_554_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_stop_boxed_555_ = lean_unbox_usize(v_stop_553_);
lean_dec(v_stop_553_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_550_, v_as_551_, v_i_boxed_554_, v_stop_boxed_555_);
lean_dec_ref(v_as_551_);
lean_dec(v_mod_550_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_558_, lean_object* v_self_559_){
_start:
{
lean_object* v_packages_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_packages_560_ = lean_ctor_get(v_self_559_, 4);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_array_get_size(v_packages_560_);
v___x_563_ = lean_nat_dec_lt(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
return v___x_563_;
}
else
{
if (v___x_563_ == 0)
{
return v___x_563_;
}
else
{
size_t v___x_564_; size_t v___x_565_; uint8_t v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_562_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_558_, v_packages_560_, v___x_564_, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_567_, lean_object* v_self_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Lake_Workspace_isBuildableModule(v_mod_567_, v_self_568_);
lean_dec_ref(v_self_568_);
lean_dec(v_mod_567_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_574_, lean_object* v_as_575_, size_t v_sz_576_, size_t v_i_577_, lean_object* v_b_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_lt(v_i_577_, v_sz_576_);
if (v___x_579_ == 0)
{
lean_dec(v_mod_574_);
lean_inc_ref(v_b_578_);
return v_b_578_;
}
else
{
lean_object* v___x_580_; lean_object* v_a_581_; lean_object* v___x_582_; 
v___x_580_ = lean_box(0);
v_a_581_ = lean_array_uget_borrowed(v_as_575_, v_i_577_);
lean_inc(v_a_581_);
lean_inc(v_mod_574_);
v___x_582_ = l_Lake_Package_findModule_x3f(v_mod_574_, v_a_581_);
if (lean_obj_tag(v___x_582_) == 1)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v_mod_574_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v___x_580_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; size_t v___x_586_; size_t v___x_587_; 
lean_dec(v___x_582_);
v___x_585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_add(v_i_577_, v___x_586_);
v_i_577_ = v___x_587_;
v_b_578_ = v___x_585_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_589_, lean_object* v_as_590_, lean_object* v_sz_591_, lean_object* v_i_592_, lean_object* v_b_593_){
_start:
{
size_t v_sz_boxed_594_; size_t v_i_boxed_595_; lean_object* v_res_596_; 
v_sz_boxed_594_ = lean_unbox_usize(v_sz_591_);
lean_dec(v_sz_591_);
v_i_boxed_595_ = lean_unbox_usize(v_i_592_);
lean_dec(v_i_592_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_589_, v_as_590_, v_sz_boxed_594_, v_i_boxed_595_, v_b_593_);
lean_dec_ref(v_b_593_);
lean_dec_ref(v_as_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_597_, lean_object* v_self_598_){
_start:
{
lean_object* v_packages_599_; lean_object* v___x_600_; lean_object* v___x_601_; size_t v_sz_602_; size_t v___x_603_; lean_object* v___x_604_; lean_object* v_fst_605_; 
v_packages_599_ = lean_ctor_get(v_self_598_, 4);
v___x_600_ = lean_box(0);
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_602_ = lean_array_size(v_packages_599_);
v___x_603_ = ((size_t)0ULL);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_597_, v_packages_599_, v_sz_602_, v___x_603_, v___x_601_);
v_fst_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_fst_605_);
lean_dec_ref(v___x_604_);
if (lean_obj_tag(v_fst_605_) == 0)
{
return v___x_600_;
}
else
{
lean_object* v_val_606_; 
v_val_606_ = lean_ctor_get(v_fst_605_, 0);
lean_inc(v_val_606_);
lean_dec_ref_known(v_fst_605_, 1);
return v_val_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_607_, lean_object* v_self_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lake_Workspace_findModule_x3f(v_mod_607_, v_self_608_);
lean_dec_ref(v_self_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_610_, lean_object* v_as_611_, size_t v_i_612_, size_t v_stop_613_, lean_object* v_b_614_){
_start:
{
lean_object* v___y_616_; uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_eq(v_i_612_, v_stop_613_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_array_uget_borrowed(v_as_611_, v_i_612_);
lean_inc(v___x_621_);
lean_inc(v_mod_610_);
v___x_622_ = l_Lake_Package_findModule_x3f(v_mod_610_, v___x_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
v___y_616_ = v_b_614_;
goto v___jp_615_;
}
else
{
lean_object* v_val_623_; lean_object* v___x_624_; 
v_val_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_array_push(v_b_614_, v_val_623_);
v___y_616_ = v___x_624_;
goto v___jp_615_;
}
}
else
{
lean_dec(v_mod_610_);
return v_b_614_;
}
v___jp_615_:
{
size_t v___x_617_; size_t v___x_618_; 
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_612_, v___x_617_);
v_i_612_ = v___x_618_;
v_b_614_ = v___y_616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_625_, lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_, lean_object* v_b_629_){
_start:
{
size_t v_i_boxed_630_; size_t v_stop_boxed_631_; lean_object* v_res_632_; 
v_i_boxed_630_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_625_, v_as_626_, v_i_boxed_630_, v_stop_boxed_631_, v_b_629_);
lean_dec_ref(v_as_626_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_635_, lean_object* v_as_636_, lean_object* v_start_637_, lean_object* v_stop_638_){
_start:
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_640_ = lean_nat_dec_lt(v_start_637_, v_stop_638_);
if (v___x_640_ == 0)
{
lean_dec(v_mod_635_);
return v___x_639_;
}
else
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_array_get_size(v_as_636_);
v___x_642_ = lean_nat_dec_le(v_stop_638_, v___x_641_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_lt(v_start_637_, v___x_641_);
if (v___x_643_ == 0)
{
lean_dec(v_mod_635_);
return v___x_639_;
}
else
{
size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_usize_of_nat(v_start_637_);
v___x_645_ = lean_usize_of_nat(v___x_641_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_635_, v_as_636_, v___x_644_, v___x_645_, v___x_639_);
return v___x_646_;
}
}
else
{
size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_usize_of_nat(v_start_637_);
v___x_648_ = lean_usize_of_nat(v_stop_638_);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_635_, v_as_636_, v___x_647_, v___x_648_, v___x_639_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_650_, lean_object* v_as_651_, lean_object* v_start_652_, lean_object* v_stop_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_650_, v_as_651_, v_start_652_, v_stop_653_);
lean_dec(v_stop_653_);
lean_dec(v_start_652_);
lean_dec_ref(v_as_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_655_, lean_object* v_self_656_){
_start:
{
lean_object* v_packages_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_packages_657_ = lean_ctor_get(v_self_656_, 4);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_array_get_size(v_packages_657_);
v___x_660_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_655_, v_packages_657_, v___x_658_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_661_, lean_object* v_self_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lake_Workspace_findModules(v_mod_661_, v_self_662_);
lean_dec_ref(v_self_662_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_664_, lean_object* v_as_665_, size_t v_sz_666_, size_t v_i_667_, lean_object* v_b_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = lean_usize_dec_lt(v_i_667_, v_sz_666_);
if (v___x_669_ == 0)
{
lean_dec(v_mod_664_);
lean_inc_ref(v_b_668_);
return v_b_668_;
}
else
{
lean_object* v___x_670_; lean_object* v_a_671_; lean_object* v___x_672_; 
v___x_670_ = lean_box(0);
v_a_671_ = lean_array_uget_borrowed(v_as_665_, v_i_667_);
lean_inc(v_a_671_);
lean_inc(v_mod_664_);
v___x_672_ = l_Lake_Package_findTargetModule_x3f(v_mod_664_, v_a_671_);
if (lean_obj_tag(v___x_672_) == 1)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_mod_664_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_670_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; size_t v___x_676_; size_t v___x_677_; 
lean_dec(v___x_672_);
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_667_, v___x_676_);
v_i_667_ = v___x_677_;
v_b_668_ = v___x_675_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_679_, lean_object* v_as_680_, lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_b_683_){
_start:
{
size_t v_sz_boxed_684_; size_t v_i_boxed_685_; lean_object* v_res_686_; 
v_sz_boxed_684_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_685_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_679_, v_as_680_, v_sz_boxed_684_, v_i_boxed_685_, v_b_683_);
lean_dec_ref(v_b_683_);
lean_dec_ref(v_as_680_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_687_, lean_object* v_self_688_){
_start:
{
lean_object* v_packages_689_; lean_object* v___x_690_; lean_object* v___x_691_; size_t v_sz_692_; size_t v___x_693_; lean_object* v___x_694_; lean_object* v_fst_695_; 
v_packages_689_ = lean_ctor_get(v_self_688_, 4);
v___x_690_ = lean_box(0);
v___x_691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_692_ = lean_array_size(v_packages_689_);
v___x_693_ = ((size_t)0ULL);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_687_, v_packages_689_, v_sz_692_, v___x_693_, v___x_691_);
v_fst_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_fst_695_);
lean_dec_ref(v___x_694_);
if (lean_obj_tag(v_fst_695_) == 0)
{
return v___x_690_;
}
else
{
lean_object* v_val_696_; 
v_val_696_ = lean_ctor_get(v_fst_695_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_fst_695_, 1);
return v_val_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_697_, lean_object* v_self_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_697_, v_self_698_);
lean_dec_ref(v_self_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_700_, lean_object* v_as_701_, size_t v_sz_702_, size_t v_i_703_, lean_object* v_b_704_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = lean_usize_dec_lt(v_i_703_, v_sz_702_);
if (v___x_705_ == 0)
{
lean_dec_ref(v_path_700_);
lean_inc_ref(v_b_704_);
return v_b_704_;
}
else
{
lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_708_; 
v___x_706_ = lean_box(0);
v_a_707_ = lean_array_uget_borrowed(v_as_701_, v_i_703_);
lean_inc(v_a_707_);
lean_inc_ref(v_path_700_);
v___x_708_ = l_Lake_Package_findModuleBySrc_x3f(v_path_700_, v_a_707_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_path_700_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; size_t v___x_712_; size_t v___x_713_; 
lean_dec(v___x_708_);
v___x_711_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_i_703_, v___x_712_);
v_i_703_ = v___x_713_;
v_b_704_ = v___x_711_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_715_, lean_object* v_as_716_, lean_object* v_sz_717_, lean_object* v_i_718_, lean_object* v_b_719_){
_start:
{
size_t v_sz_boxed_720_; size_t v_i_boxed_721_; lean_object* v_res_722_; 
v_sz_boxed_720_ = lean_unbox_usize(v_sz_717_);
lean_dec(v_sz_717_);
v_i_boxed_721_ = lean_unbox_usize(v_i_718_);
lean_dec(v_i_718_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_715_, v_as_716_, v_sz_boxed_720_, v_i_boxed_721_, v_b_719_);
lean_dec_ref(v_b_719_);
lean_dec_ref(v_as_716_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_723_, lean_object* v_self_724_){
_start:
{
lean_object* v_packages_725_; lean_object* v___x_726_; lean_object* v___x_727_; size_t v_sz_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v_fst_731_; 
v_packages_725_ = lean_ctor_get(v_self_724_, 4);
v___x_726_ = lean_box(0);
v___x_727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_728_ = lean_array_size(v_packages_725_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_723_, v_packages_725_, v_sz_728_, v___x_729_, v___x_727_);
v_fst_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_fst_731_);
lean_dec_ref(v___x_730_);
if (lean_obj_tag(v_fst_731_) == 0)
{
return v___x_726_;
}
else
{
lean_object* v_val_732_; 
v_val_732_ = lean_ctor_get(v_fst_731_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v_fst_731_, 1);
return v_val_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_733_, lean_object* v_self_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_733_, v_self_734_);
lean_dec_ref(v_self_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_739_, lean_object* v_as_740_, size_t v_sz_741_, size_t v_i_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_a_745_; uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_lt(v_i_742_, v_sz_741_);
if (v___x_749_ == 0)
{
lean_inc_ref(v_b_743_);
return v_b_743_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_a_752_; lean_object* v___x_753_; 
v___x_750_ = lean_box(0);
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_752_ = lean_array_uget_borrowed(v_as_740_, v_i_742_);
v___x_753_ = l_Lake_Package_findTargetDecl_x3f(v_name_739_, v_a_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
v_a_745_ = v___x_751_;
goto v___jp_744_;
}
else
{
lean_object* v_val_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_769_; 
v_val_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_769_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_769_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_val_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_769_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_name_758_; lean_object* v_kind_759_; lean_object* v_config_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_name_758_ = lean_ctor_get(v_val_754_, 1);
lean_inc(v_name_758_);
v_kind_759_ = lean_ctor_get(v_val_754_, 2);
lean_inc(v_kind_759_);
v_config_760_ = lean_ctor_get(v_val_754_, 3);
lean_inc(v_config_760_);
lean_dec(v_val_754_);
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_762_ = lean_name_eq(v_kind_759_, v___x_761_);
lean_dec(v_kind_759_);
if (v___x_762_ == 0)
{
lean_dec(v_config_760_);
lean_dec(v_name_758_);
lean_del_object(v___x_756_);
v_a_745_ = v___x_751_;
goto v___jp_744_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_765_; 
lean_inc(v_a_752_);
v___x_763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_763_, 0, v_a_752_);
lean_ctor_set(v___x_763_, 1, v_name_758_);
lean_ctor_set(v___x_763_, 2, v_config_760_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_763_);
v___x_765_ = v___x_756_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_768_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_750_);
return v___x_767_;
}
}
}
}
}
v___jp_744_:
{
size_t v___x_746_; size_t v___x_747_; 
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_add(v_i_742_, v___x_746_);
v_i_742_ = v___x_747_;
v_b_743_ = v_a_745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_770_, lean_object* v_as_771_, lean_object* v_sz_772_, lean_object* v_i_773_, lean_object* v_b_774_){
_start:
{
size_t v_sz_boxed_775_; size_t v_i_boxed_776_; lean_object* v_res_777_; 
v_sz_boxed_775_ = lean_unbox_usize(v_sz_772_);
lean_dec(v_sz_772_);
v_i_boxed_776_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_770_, v_as_771_, v_sz_boxed_775_, v_i_boxed_776_, v_b_774_);
lean_dec_ref(v_b_774_);
lean_dec_ref(v_as_771_);
lean_dec(v_name_770_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_778_, lean_object* v_self_779_){
_start:
{
lean_object* v_packages_780_; lean_object* v___x_781_; lean_object* v___x_782_; size_t v_sz_783_; size_t v___x_784_; lean_object* v___x_785_; lean_object* v_fst_786_; 
v_packages_780_ = lean_ctor_get(v_self_779_, 4);
v___x_781_ = lean_box(0);
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_783_ = lean_array_size(v_packages_780_);
v___x_784_ = ((size_t)0ULL);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_778_, v_packages_780_, v_sz_783_, v___x_784_, v___x_782_);
v_fst_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_fst_786_);
lean_dec_ref(v___x_785_);
if (lean_obj_tag(v_fst_786_) == 0)
{
return v___x_781_;
}
else
{
lean_object* v_val_787_; 
v_val_787_ = lean_ctor_get(v_fst_786_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v_fst_786_, 1);
return v_val_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_788_, lean_object* v_self_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lake_Workspace_findLeanLib_x3f(v_name_788_, v_self_789_);
lean_dec_ref(v_self_789_);
lean_dec(v_name_788_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_791_, lean_object* v_as_792_, size_t v_sz_793_, size_t v_i_794_, lean_object* v_b_795_){
_start:
{
lean_object* v_a_797_; uint8_t v___x_801_; 
v___x_801_ = lean_usize_dec_lt(v_i_794_, v_sz_793_);
if (v___x_801_ == 0)
{
lean_inc_ref(v_b_795_);
return v_b_795_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_a_804_; lean_object* v___x_805_; 
v___x_802_ = lean_box(0);
v___x_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_804_ = lean_array_uget_borrowed(v_as_792_, v_i_794_);
v___x_805_ = l_Lake_Package_findTargetDecl_x3f(v_name_791_, v_a_804_);
if (lean_obj_tag(v___x_805_) == 0)
{
v_a_797_ = v___x_803_;
goto v___jp_796_;
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_821_; 
v_val_806_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_821_ == 0)
{
v___x_808_ = v___x_805_;
v_isShared_809_ = v_isSharedCheck_821_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_val_806_);
lean_dec(v___x_805_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_821_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_name_810_; lean_object* v_kind_811_; lean_object* v_config_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_name_810_ = lean_ctor_get(v_val_806_, 1);
lean_inc(v_name_810_);
v_kind_811_ = lean_ctor_get(v_val_806_, 2);
lean_inc(v_kind_811_);
v_config_812_ = lean_ctor_get(v_val_806_, 3);
lean_inc(v_config_812_);
lean_dec(v_val_806_);
v___x_813_ = l_Lake_LeanExe_keyword;
v___x_814_ = lean_name_eq(v_kind_811_, v___x_813_);
lean_dec(v_kind_811_);
if (v___x_814_ == 0)
{
lean_dec(v_config_812_);
lean_dec(v_name_810_);
lean_del_object(v___x_808_);
v_a_797_ = v___x_803_;
goto v___jp_796_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_inc(v_a_804_);
v___x_815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_815_, 0, v_a_804_);
lean_ctor_set(v___x_815_, 1, v_name_810_);
lean_ctor_set(v___x_815_, 2, v_config_812_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_815_);
v___x_817_ = v___x_808_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_820_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v___x_802_);
return v___x_819_;
}
}
}
}
}
v___jp_796_:
{
size_t v___x_798_; size_t v___x_799_; 
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_794_, v___x_798_);
v_i_794_ = v___x_799_;
v_b_795_ = v_a_797_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_822_, lean_object* v_as_823_, lean_object* v_sz_824_, lean_object* v_i_825_, lean_object* v_b_826_){
_start:
{
size_t v_sz_boxed_827_; size_t v_i_boxed_828_; lean_object* v_res_829_; 
v_sz_boxed_827_ = lean_unbox_usize(v_sz_824_);
lean_dec(v_sz_824_);
v_i_boxed_828_ = lean_unbox_usize(v_i_825_);
lean_dec(v_i_825_);
v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_822_, v_as_823_, v_sz_boxed_827_, v_i_boxed_828_, v_b_826_);
lean_dec_ref(v_b_826_);
lean_dec_ref(v_as_823_);
lean_dec(v_name_822_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_830_, lean_object* v_self_831_){
_start:
{
lean_object* v_packages_832_; lean_object* v___x_833_; lean_object* v___x_834_; size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v_fst_838_; 
v_packages_832_ = lean_ctor_get(v_self_831_, 4);
v___x_833_ = lean_box(0);
v___x_834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_835_ = lean_array_size(v_packages_832_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_830_, v_packages_832_, v_sz_835_, v___x_836_, v___x_834_);
v_fst_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_fst_838_);
lean_dec_ref(v___x_837_);
if (lean_obj_tag(v_fst_838_) == 0)
{
return v___x_833_;
}
else
{
lean_object* v_val_839_; 
v_val_839_ = lean_ctor_get(v_fst_838_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v_fst_838_, 1);
return v_val_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_840_, lean_object* v_self_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_Workspace_findLeanExe_x3f(v_name_840_, v_self_841_);
lean_dec_ref(v_self_841_);
lean_dec(v_name_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_843_, lean_object* v_as_844_, size_t v_sz_845_, size_t v_i_846_, lean_object* v_b_847_){
_start:
{
lean_object* v_a_849_; uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_846_, v_sz_845_);
if (v___x_853_ == 0)
{
lean_inc_ref(v_b_847_);
return v_b_847_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v_a_856_; lean_object* v___x_857_; 
v___x_854_ = lean_box(0);
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_856_ = lean_array_uget_borrowed(v_as_844_, v_i_846_);
v___x_857_ = l_Lake_Package_findTargetDecl_x3f(v_name_843_, v_a_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
v_a_849_ = v___x_855_;
goto v___jp_848_;
}
else
{
lean_object* v_val_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_873_; 
v_val_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_873_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_873_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_val_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_873_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_name_862_; lean_object* v_kind_863_; lean_object* v_config_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_name_862_ = lean_ctor_get(v_val_858_, 1);
lean_inc(v_name_862_);
v_kind_863_ = lean_ctor_get(v_val_858_, 2);
lean_inc(v_kind_863_);
v_config_864_ = lean_ctor_get(v_val_858_, 3);
lean_inc(v_config_864_);
lean_dec(v_val_858_);
v___x_865_ = l_Lake_ExternLib_keyword;
v___x_866_ = lean_name_eq(v_kind_863_, v___x_865_);
lean_dec(v_kind_863_);
if (v___x_866_ == 0)
{
lean_dec(v_config_864_);
lean_dec(v_name_862_);
lean_del_object(v___x_860_);
v_a_849_ = v___x_855_;
goto v___jp_848_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_869_; 
lean_inc(v_a_856_);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v_a_856_);
lean_ctor_set(v___x_867_, 1, v_name_862_);
lean_ctor_set(v___x_867_, 2, v_config_864_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_867_);
v___x_869_ = v___x_860_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_854_);
return v___x_871_;
}
}
}
}
}
v___jp_848_:
{
size_t v___x_850_; size_t v___x_851_; 
v___x_850_ = ((size_t)1ULL);
v___x_851_ = lean_usize_add(v_i_846_, v___x_850_);
v_i_846_ = v___x_851_;
v_b_847_ = v_a_849_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_874_, lean_object* v_as_875_, lean_object* v_sz_876_, lean_object* v_i_877_, lean_object* v_b_878_){
_start:
{
size_t v_sz_boxed_879_; size_t v_i_boxed_880_; lean_object* v_res_881_; 
v_sz_boxed_879_ = lean_unbox_usize(v_sz_876_);
lean_dec(v_sz_876_);
v_i_boxed_880_ = lean_unbox_usize(v_i_877_);
lean_dec(v_i_877_);
v_res_881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_874_, v_as_875_, v_sz_boxed_879_, v_i_boxed_880_, v_b_878_);
lean_dec_ref(v_b_878_);
lean_dec_ref(v_as_875_);
lean_dec(v_name_874_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_882_, lean_object* v_self_883_){
_start:
{
lean_object* v_packages_884_; lean_object* v___x_885_; lean_object* v___x_886_; size_t v_sz_887_; size_t v___x_888_; lean_object* v___x_889_; lean_object* v_fst_890_; 
v_packages_884_ = lean_ctor_get(v_self_883_, 4);
v___x_885_ = lean_box(0);
v___x_886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_887_ = lean_array_size(v_packages_884_);
v___x_888_ = ((size_t)0ULL);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_882_, v_packages_884_, v_sz_887_, v___x_888_, v___x_886_);
v_fst_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_fst_890_);
lean_dec_ref(v___x_889_);
if (lean_obj_tag(v_fst_890_) == 0)
{
return v___x_885_;
}
else
{
lean_object* v_val_891_; 
v_val_891_ = lean_ctor_get(v_fst_890_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v_fst_890_, 1);
return v_val_891_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_892_, lean_object* v_self_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lake_Workspace_findExternLib_x3f(v_name_892_, v_self_893_);
lean_dec_ref(v_self_893_);
lean_dec(v_name_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_895_, lean_object* v_f_896_){
_start:
{
if (lean_obj_tag(v_a_895_) == 0)
{
lean_object* v___x_897_; 
lean_dec(v_f_896_);
v___x_897_ = lean_box(0);
return v___x_897_;
}
else
{
lean_object* v_val_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_906_; 
v_val_898_ = lean_ctor_get(v_a_895_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v_a_895_);
if (v_isSharedCheck_906_ == 0)
{
v___x_900_ = v_a_895_;
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_val_898_);
lean_dec(v_a_895_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_906_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_902_ = lean_apply_1(v_f_896_, v_val_898_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_902_);
v___x_904_ = v___x_900_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_a_909_, lean_object* v_f_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_909_, v_f_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_a_912_);
lean_ctor_set(v___x_914_, 1, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_918_, lean_object* v_as_919_, size_t v_sz_920_, size_t v_i_921_, lean_object* v_b_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_lt(v_i_921_, v_sz_920_);
if (v___x_923_ == 0)
{
lean_inc_ref(v_b_922_);
return v_b_922_;
}
else
{
lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___f_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_924_ = lean_box(0);
v_a_925_ = lean_array_uget_borrowed(v_as_919_, v_i_921_);
lean_inc(v_a_925_);
v___f_926_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_926_, 0, v_a_925_);
v___x_927_ = l_Lake_Package_findTargetConfig_x3f(v_name_918_, v_a_925_);
v___x_928_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_927_, v___f_926_);
if (lean_obj_tag(v___x_928_) == 1)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_924_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; size_t v___x_932_; size_t v___x_933_; 
lean_dec(v___x_928_);
v___x_931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_921_, v___x_932_);
v_i_921_ = v___x_933_;
v_b_922_ = v___x_931_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_935_, lean_object* v_as_936_, lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_b_939_){
_start:
{
size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_sz_boxed_940_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_941_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_935_, v_as_936_, v_sz_boxed_940_, v_i_boxed_941_, v_b_939_);
lean_dec_ref(v_b_939_);
lean_dec_ref(v_as_936_);
lean_dec(v_name_935_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_943_, lean_object* v_self_944_){
_start:
{
lean_object* v_packages_945_; lean_object* v___x_946_; lean_object* v___x_947_; size_t v_sz_948_; size_t v___x_949_; lean_object* v___x_950_; lean_object* v_fst_951_; 
v_packages_945_ = lean_ctor_get(v_self_944_, 4);
v___x_946_ = lean_box(0);
v___x_947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_948_ = lean_array_size(v_packages_945_);
v___x_949_ = ((size_t)0ULL);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_943_, v_packages_945_, v_sz_948_, v___x_949_, v___x_947_);
v_fst_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_fst_951_);
lean_dec_ref(v___x_950_);
if (lean_obj_tag(v_fst_951_) == 0)
{
return v___x_946_;
}
else
{
lean_object* v_val_952_; 
v_val_952_ = lean_ctor_get(v_fst_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_fst_951_, 1);
return v_val_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_953_, lean_object* v_self_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_953_, v_self_954_);
lean_dec_ref(v_self_954_);
lean_dec(v_name_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_956_, lean_object* v_x_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_a_956_);
lean_ctor_set(v___x_958_, 1, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_959_, lean_object* v_as_960_, size_t v_sz_961_, size_t v_i_962_, lean_object* v_b_963_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = lean_usize_dec_lt(v_i_962_, v_sz_961_);
if (v___x_964_ == 0)
{
lean_inc_ref(v_b_963_);
return v_b_963_;
}
else
{
lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_965_ = lean_box(0);
v_a_966_ = lean_array_uget_borrowed(v_as_960_, v_i_962_);
lean_inc(v_a_966_);
v___f_967_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_967_, 0, v_a_966_);
v___x_968_ = l_Lake_Package_findTargetDecl_x3f(v_name_959_, v_a_966_);
v___x_969_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_968_, v___f_967_);
if (lean_obj_tag(v___x_969_) == 1)
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v___x_965_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; size_t v___x_973_; size_t v___x_974_; 
lean_dec(v___x_969_);
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_962_, v___x_973_);
v_i_962_ = v___x_974_;
v_b_963_ = v___x_972_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_976_, lean_object* v_as_977_, lean_object* v_sz_978_, lean_object* v_i_979_, lean_object* v_b_980_){
_start:
{
size_t v_sz_boxed_981_; size_t v_i_boxed_982_; lean_object* v_res_983_; 
v_sz_boxed_981_ = lean_unbox_usize(v_sz_978_);
lean_dec(v_sz_978_);
v_i_boxed_982_ = lean_unbox_usize(v_i_979_);
lean_dec(v_i_979_);
v_res_983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_976_, v_as_977_, v_sz_boxed_981_, v_i_boxed_982_, v_b_980_);
lean_dec_ref(v_b_980_);
lean_dec_ref(v_as_977_);
lean_dec(v_name_976_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_984_, lean_object* v_self_985_){
_start:
{
lean_object* v_packages_986_; lean_object* v___x_987_; lean_object* v___x_988_; size_t v_sz_989_; size_t v___x_990_; lean_object* v___x_991_; lean_object* v_fst_992_; 
v_packages_986_ = lean_ctor_get(v_self_985_, 4);
v___x_987_ = lean_box(0);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_989_ = lean_array_size(v_packages_986_);
v___x_990_ = ((size_t)0ULL);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_984_, v_packages_986_, v_sz_989_, v___x_990_, v___x_988_);
v_fst_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_fst_992_);
lean_dec_ref(v___x_991_);
if (lean_obj_tag(v_fst_992_) == 0)
{
return v___x_987_;
}
else
{
lean_object* v_val_993_; 
v_val_993_ = lean_ctor_get(v_fst_992_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v_fst_992_, 1);
return v_val_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_994_, lean_object* v_self_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_994_, v_self_995_);
lean_dec_ref(v_self_995_);
lean_dec(v_name_994_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_997_, lean_object* v_cfg_998_, lean_object* v_self_999_){
_start:
{
lean_object* v_lakeEnv_1000_; lean_object* v_lakeConfig_1001_; lean_object* v_lakeCache_1002_; lean_object* v_lakeArgs_x3f_1003_; lean_object* v_packages_1004_; lean_object* v_packageMap_1005_; lean_object* v_facetConfigs_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
v_lakeEnv_1000_ = lean_ctor_get(v_self_999_, 0);
v_lakeConfig_1001_ = lean_ctor_get(v_self_999_, 1);
v_lakeCache_1002_ = lean_ctor_get(v_self_999_, 2);
v_lakeArgs_x3f_1003_ = lean_ctor_get(v_self_999_, 3);
v_packages_1004_ = lean_ctor_get(v_self_999_, 4);
v_packageMap_1005_ = lean_ctor_get(v_self_999_, 5);
v_facetConfigs_1006_ = lean_ctor_get(v_self_999_, 6);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_self_999_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1008_ = v_self_999_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_facetConfigs_1006_);
lean_inc(v_packageMap_1005_);
lean_inc(v_packages_1004_);
lean_inc(v_lakeArgs_x3f_1003_);
lean_inc(v_lakeCache_1002_);
lean_inc(v_lakeConfig_1001_);
lean_inc(v_lakeEnv_1000_);
lean_dec(v_self_999_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = l_Lake_FacetConfigMap_insert(v_name_997_, v_cfg_998_, v_facetConfigs_1006_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 6, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_lakeEnv_1000_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_lakeConfig_1001_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_lakeCache_1002_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_lakeArgs_x3f_1003_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_packages_1004_);
lean_ctor_set(v_reuseFailAlloc_1013_, 5, v_packageMap_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 6, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_1015_, lean_object* v_self_1016_){
_start:
{
lean_object* v_facetConfigs_1017_; lean_object* v___x_1018_; 
v_facetConfigs_1017_ = lean_ctor_get(v_self_1016_, 6);
v___x_1018_ = l_Lake_FacetConfigMap_get_x3f(v_name_1015_, v_facetConfigs_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_1019_, lean_object* v_self_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1019_, v_self_1020_);
lean_dec_ref(v_self_1020_);
lean_dec(v_name_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_1022_, lean_object* v_cfg_1023_, lean_object* v_self_1024_){
_start:
{
lean_object* v_lakeEnv_1025_; lean_object* v_lakeConfig_1026_; lean_object* v_lakeCache_1027_; lean_object* v_lakeArgs_x3f_1028_; lean_object* v_packages_1029_; lean_object* v_packageMap_1030_; lean_object* v_facetConfigs_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
v_lakeEnv_1025_ = lean_ctor_get(v_self_1024_, 0);
v_lakeConfig_1026_ = lean_ctor_get(v_self_1024_, 1);
v_lakeCache_1027_ = lean_ctor_get(v_self_1024_, 2);
v_lakeArgs_x3f_1028_ = lean_ctor_get(v_self_1024_, 3);
v_packages_1029_ = lean_ctor_get(v_self_1024_, 4);
v_packageMap_1030_ = lean_ctor_get(v_self_1024_, 5);
v_facetConfigs_1031_ = lean_ctor_get(v_self_1024_, 6);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_self_1024_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1033_ = v_self_1024_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_facetConfigs_1031_);
lean_inc(v_packageMap_1030_);
lean_inc(v_packages_1029_);
lean_inc(v_lakeArgs_x3f_1028_);
lean_inc(v_lakeCache_1027_);
lean_inc(v_lakeConfig_1026_);
lean_inc(v_lakeEnv_1025_);
lean_dec(v_self_1024_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = l_Lake_FacetConfigMap_insert(v_name_1022_, v_cfg_1023_, v_facetConfigs_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 6, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_lakeEnv_1025_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_lakeConfig_1026_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_lakeCache_1027_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_lakeArgs_x3f_1028_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v_packages_1029_);
lean_ctor_set(v_reuseFailAlloc_1038_, 5, v_packageMap_1030_);
lean_ctor_set(v_reuseFailAlloc_1038_, 6, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_1040_, lean_object* v_self_1041_){
_start:
{
lean_object* v_facetConfigs_1042_; lean_object* v___x_1043_; 
v_facetConfigs_1042_ = lean_ctor_get(v_self_1041_, 6);
v___x_1043_ = l_Lake_FacetConfigMap_get_x3f(v_name_1040_, v_facetConfigs_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_box(0);
return v___x_1044_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_val_1045_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1046_ = l_Lake_Module_keyword;
v___x_1047_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1046_, v_val_1045_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1048_, lean_object* v_self_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1048_, v_self_1049_);
lean_dec_ref(v_self_1049_);
lean_dec(v_name_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1051_, lean_object* v_cfg_1052_, lean_object* v_self_1053_){
_start:
{
lean_object* v_lakeEnv_1054_; lean_object* v_lakeConfig_1055_; lean_object* v_lakeCache_1056_; lean_object* v_lakeArgs_x3f_1057_; lean_object* v_packages_1058_; lean_object* v_packageMap_1059_; lean_object* v_facetConfigs_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1068_; 
v_lakeEnv_1054_ = lean_ctor_get(v_self_1053_, 0);
v_lakeConfig_1055_ = lean_ctor_get(v_self_1053_, 1);
v_lakeCache_1056_ = lean_ctor_get(v_self_1053_, 2);
v_lakeArgs_x3f_1057_ = lean_ctor_get(v_self_1053_, 3);
v_packages_1058_ = lean_ctor_get(v_self_1053_, 4);
v_packageMap_1059_ = lean_ctor_get(v_self_1053_, 5);
v_facetConfigs_1060_ = lean_ctor_get(v_self_1053_, 6);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_self_1053_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1062_ = v_self_1053_;
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_facetConfigs_1060_);
lean_inc(v_packageMap_1059_);
lean_inc(v_packages_1058_);
lean_inc(v_lakeArgs_x3f_1057_);
lean_inc(v_lakeCache_1056_);
lean_inc(v_lakeConfig_1055_);
lean_inc(v_lakeEnv_1054_);
lean_dec(v_self_1053_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1068_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = l_Lake_FacetConfigMap_insert(v_name_1051_, v_cfg_1052_, v_facetConfigs_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 6, v___x_1064_);
v___x_1066_ = v___x_1062_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_lakeEnv_1054_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_lakeConfig_1055_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_lakeCache_1056_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_lakeArgs_x3f_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_packages_1058_);
lean_ctor_set(v_reuseFailAlloc_1067_, 5, v_packageMap_1059_);
lean_ctor_set(v_reuseFailAlloc_1067_, 6, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1069_, lean_object* v_self_1070_){
_start:
{
lean_object* v_facetConfigs_1071_; lean_object* v___x_1072_; 
v_facetConfigs_1071_ = lean_ctor_get(v_self_1070_, 6);
v___x_1072_ = l_Lake_FacetConfigMap_get_x3f(v_name_1069_, v_facetConfigs_1071_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_box(0);
return v___x_1073_;
}
else
{
lean_object* v_val_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_val_1074_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1074_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1075_ = l_Lake_Package_keyword;
v___x_1076_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1075_, v_val_1074_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1077_, lean_object* v_self_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1077_, v_self_1078_);
lean_dec_ref(v_self_1078_);
lean_dec(v_name_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1080_, lean_object* v_cfg_1081_, lean_object* v_self_1082_){
_start:
{
lean_object* v_lakeEnv_1083_; lean_object* v_lakeConfig_1084_; lean_object* v_lakeCache_1085_; lean_object* v_lakeArgs_x3f_1086_; lean_object* v_packages_1087_; lean_object* v_packageMap_1088_; lean_object* v_facetConfigs_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
v_lakeEnv_1083_ = lean_ctor_get(v_self_1082_, 0);
v_lakeConfig_1084_ = lean_ctor_get(v_self_1082_, 1);
v_lakeCache_1085_ = lean_ctor_get(v_self_1082_, 2);
v_lakeArgs_x3f_1086_ = lean_ctor_get(v_self_1082_, 3);
v_packages_1087_ = lean_ctor_get(v_self_1082_, 4);
v_packageMap_1088_ = lean_ctor_get(v_self_1082_, 5);
v_facetConfigs_1089_ = lean_ctor_get(v_self_1082_, 6);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_self_1082_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v_self_1082_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_facetConfigs_1089_);
lean_inc(v_packageMap_1088_);
lean_inc(v_packages_1087_);
lean_inc(v_lakeArgs_x3f_1086_);
lean_inc(v_lakeCache_1085_);
lean_inc(v_lakeConfig_1084_);
lean_inc(v_lakeEnv_1083_);
lean_dec(v_self_1082_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = l_Lake_FacetConfigMap_insert(v_name_1080_, v_cfg_1081_, v_facetConfigs_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 6, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_lakeEnv_1083_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_lakeConfig_1084_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_lakeCache_1085_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_lakeArgs_x3f_1086_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_packages_1087_);
lean_ctor_set(v_reuseFailAlloc_1096_, 5, v_packageMap_1088_);
lean_ctor_set(v_reuseFailAlloc_1096_, 6, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1098_, lean_object* v_self_1099_){
_start:
{
lean_object* v_facetConfigs_1100_; lean_object* v___x_1101_; 
v_facetConfigs_1100_ = lean_ctor_get(v_self_1099_, 6);
v___x_1101_ = l_Lake_FacetConfigMap_get_x3f(v_name_1098_, v_facetConfigs_1100_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_box(0);
return v___x_1102_;
}
else
{
lean_object* v_val_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_val_1103_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1105_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1104_, v_val_1103_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1106_, lean_object* v_self_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1106_, v_self_1107_);
lean_dec_ref(v_self_1107_);
lean_dec(v_name_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1109_, size_t v_i_1110_, size_t v_stop_1111_, lean_object* v_b_1112_){
_start:
{
uint8_t v___x_1113_; 
v___x_1113_ = lean_usize_dec_eq(v_i_1110_, v_stop_1111_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v_config_1115_; lean_object* v_dir_1116_; lean_object* v_buildDir_1117_; lean_object* v_binDir_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; 
v___x_1114_ = lean_array_uget_borrowed(v_as_1109_, v_i_1110_);
v_config_1115_ = lean_ctor_get(v___x_1114_, 6);
v_dir_1116_ = lean_ctor_get(v___x_1114_, 4);
v_buildDir_1117_ = lean_ctor_get(v_config_1115_, 5);
v_binDir_1118_ = lean_ctor_get(v_config_1115_, 8);
lean_inc_ref(v_buildDir_1117_);
v___x_1119_ = l_System_FilePath_normalize(v_buildDir_1117_);
lean_inc_ref(v_dir_1116_);
v___x_1120_ = l_Lake_joinRelative(v_dir_1116_, v___x_1119_);
lean_inc_ref(v_binDir_1118_);
v___x_1121_ = l_System_FilePath_normalize(v_binDir_1118_);
v___x_1122_ = l_Lake_joinRelative(v___x_1120_, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_b_1112_);
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_add(v_i_1110_, v___x_1124_);
v_i_1110_ = v___x_1125_;
v_b_1112_ = v___x_1123_;
goto _start;
}
else
{
return v_b_1112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1127_, lean_object* v_i_1128_, lean_object* v_stop_1129_, lean_object* v_b_1130_){
_start:
{
size_t v_i_boxed_1131_; size_t v_stop_boxed_1132_; lean_object* v_res_1133_; 
v_i_boxed_1131_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_stop_boxed_1132_ = lean_unbox_usize(v_stop_1129_);
lean_dec(v_stop_1129_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1127_, v_i_boxed_1131_, v_stop_boxed_1132_, v_b_1130_);
lean_dec_ref(v_as_1127_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1134_){
_start:
{
lean_object* v_packages_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_packages_1135_ = lean_ctor_get(v_self_1134_, 4);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_array_get_size(v_packages_1135_);
v___x_1139_ = lean_nat_dec_lt(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
return v___x_1136_;
}
else
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_le(v___x_1138_, v___x_1138_);
if (v___x_1140_ == 0)
{
if (v___x_1139_ == 0)
{
return v___x_1136_;
}
else
{
size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = lean_usize_of_nat(v___x_1138_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1135_, v___x_1141_, v___x_1142_, v___x_1136_);
return v___x_1143_;
}
}
else
{
size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = lean_usize_of_nat(v___x_1138_);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1135_, v___x_1144_, v___x_1145_, v___x_1136_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lake_Workspace_binPath(v_self_1147_);
lean_dec_ref(v_self_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1149_, size_t v_i_1150_, size_t v_stop_1151_, lean_object* v_b_1152_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_eq(v_i_1150_, v_stop_1151_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v_config_1155_; lean_object* v_dir_1156_; lean_object* v_buildDir_1157_; lean_object* v_leanLibDir_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; 
v___x_1154_ = lean_array_uget_borrowed(v_as_1149_, v_i_1150_);
v_config_1155_ = lean_ctor_get(v___x_1154_, 6);
v_dir_1156_ = lean_ctor_get(v___x_1154_, 4);
v_buildDir_1157_ = lean_ctor_get(v_config_1155_, 5);
v_leanLibDir_1158_ = lean_ctor_get(v_config_1155_, 6);
lean_inc_ref(v_buildDir_1157_);
v___x_1159_ = l_System_FilePath_normalize(v_buildDir_1157_);
lean_inc_ref(v_dir_1156_);
v___x_1160_ = l_Lake_joinRelative(v_dir_1156_, v___x_1159_);
lean_inc_ref(v_leanLibDir_1158_);
v___x_1161_ = l_System_FilePath_normalize(v_leanLibDir_1158_);
v___x_1162_ = l_Lake_joinRelative(v___x_1160_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_b_1152_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1150_, v___x_1164_);
v_i_1150_ = v___x_1165_;
v_b_1152_ = v___x_1163_;
goto _start;
}
else
{
return v_b_1152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1167_, lean_object* v_i_1168_, lean_object* v_stop_1169_, lean_object* v_b_1170_){
_start:
{
size_t v_i_boxed_1171_; size_t v_stop_boxed_1172_; lean_object* v_res_1173_; 
v_i_boxed_1171_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v_stop_boxed_1172_ = lean_unbox_usize(v_stop_1169_);
lean_dec(v_stop_1169_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1167_, v_i_boxed_1171_, v_stop_boxed_1172_, v_b_1170_);
lean_dec_ref(v_as_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1174_){
_start:
{
lean_object* v_packages_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_packages_1175_ = lean_ctor_get(v_self_1174_, 4);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_array_get_size(v_packages_1175_);
v___x_1179_ = lean_nat_dec_lt(v___x_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
return v___x_1176_;
}
else
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_nat_dec_le(v___x_1178_, v___x_1178_);
if (v___x_1180_ == 0)
{
if (v___x_1179_ == 0)
{
return v___x_1176_;
}
else
{
size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = lean_usize_of_nat(v___x_1178_);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1175_, v___x_1181_, v___x_1182_, v___x_1176_);
return v___x_1183_;
}
}
else
{
size_t v___x_1184_; size_t v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = ((size_t)0ULL);
v___x_1185_ = lean_usize_of_nat(v___x_1178_);
v___x_1186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1175_, v___x_1184_, v___x_1185_, v___x_1176_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* v_self_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lake_Workspace_leanPath(v_self_1187_);
lean_dec_ref(v_self_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1189_, lean_object* v_as_1190_, size_t v_i_1191_, size_t v_stop_1192_, lean_object* v_b_1193_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = lean_usize_dec_eq(v_i_1191_, v_stop_1192_);
if (v___x_1194_ == 0)
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; lean_object* v_kind_1198_; lean_object* v_config_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_sub(v_i_1191_, v___x_1195_);
v___x_1197_ = lean_array_uget_borrowed(v_as_1190_, v___x_1196_);
v_kind_1198_ = lean_ctor_get(v___x_1197_, 2);
v_config_1199_ = lean_ctor_get(v___x_1197_, 3);
v___x_1200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1201_ = lean_name_eq(v_kind_1198_, v___x_1200_);
if (v___x_1201_ == 0)
{
v_i_1191_ = v___x_1196_;
goto _start;
}
else
{
lean_object* v_config_1203_; lean_object* v_dir_1204_; lean_object* v_srcDir_1205_; lean_object* v_srcDir_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_config_1203_ = lean_ctor_get(v_x2_1189_, 6);
v_dir_1204_ = lean_ctor_get(v_x2_1189_, 4);
v_srcDir_1205_ = lean_ctor_get(v_config_1203_, 4);
v_srcDir_1206_ = lean_ctor_get(v_config_1199_, 1);
lean_inc_ref(v_srcDir_1205_);
v___x_1207_ = l_System_FilePath_normalize(v_srcDir_1205_);
lean_inc_ref(v_dir_1204_);
v___x_1208_ = l_Lake_joinRelative(v_dir_1204_, v___x_1207_);
lean_inc_ref(v_srcDir_1206_);
v___x_1209_ = l_Lake_joinRelative(v___x_1208_, v_srcDir_1206_);
v___x_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v_b_1193_);
v_i_1191_ = v___x_1196_;
v_b_1193_ = v___x_1210_;
goto _start;
}
}
else
{
lean_dec_ref(v_x2_1189_);
return v_b_1193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1212_, lean_object* v_as_1213_, lean_object* v_i_1214_, lean_object* v_stop_1215_, lean_object* v_b_1216_){
_start:
{
size_t v_i_boxed_1217_; size_t v_stop_boxed_1218_; lean_object* v_res_1219_; 
v_i_boxed_1217_ = lean_unbox_usize(v_i_1214_);
lean_dec(v_i_1214_);
v_stop_boxed_1218_ = lean_unbox_usize(v_stop_1215_);
lean_dec(v_stop_1215_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1212_, v_as_1213_, v_i_boxed_1217_, v_stop_boxed_1218_, v_b_1216_);
lean_dec_ref(v_as_1213_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1220_, size_t v_i_1221_, size_t v_stop_1222_, lean_object* v_b_1223_){
_start:
{
lean_object* v___y_1225_; uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_eq(v_i_1221_, v_stop_1222_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v_targetDecls_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1230_ = lean_array_uget_borrowed(v_as_1220_, v_i_1221_);
v_targetDecls_1231_ = lean_ctor_get(v___x_1230_, 15);
v___x_1232_ = lean_array_get_size(v_targetDecls_1231_);
v___x_1233_ = lean_unsigned_to_nat(0u);
v___x_1234_ = lean_nat_dec_lt(v___x_1233_, v___x_1232_);
if (v___x_1234_ == 0)
{
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_usize_of_nat(v___x_1232_);
v___x_1236_ = ((size_t)0ULL);
lean_inc(v___x_1230_);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1230_, v_targetDecls_1231_, v___x_1235_, v___x_1236_, v_b_1223_);
v___y_1225_ = v___x_1237_;
goto v___jp_1224_;
}
}
else
{
return v_b_1223_;
}
v___jp_1224_:
{
size_t v___x_1226_; size_t v___x_1227_; 
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1221_, v___x_1226_);
v_i_1221_ = v___x_1227_;
v_b_1223_ = v___y_1225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1238_, lean_object* v_i_1239_, lean_object* v_stop_1240_, lean_object* v_b_1241_){
_start:
{
size_t v_i_boxed_1242_; size_t v_stop_boxed_1243_; lean_object* v_res_1244_; 
v_i_boxed_1242_ = lean_unbox_usize(v_i_1239_);
lean_dec(v_i_1239_);
v_stop_boxed_1243_ = lean_unbox_usize(v_stop_1240_);
lean_dec(v_stop_1240_);
v_res_1244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1238_, v_i_boxed_1242_, v_stop_boxed_1243_, v_b_1241_);
lean_dec_ref(v_as_1238_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1245_){
_start:
{
lean_object* v_packages_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_packages_1246_ = lean_ctor_get(v_self_1245_, 4);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = lean_array_get_size(v_packages_1246_);
v___x_1250_ = lean_nat_dec_lt(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
return v___x_1247_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_nat_dec_le(v___x_1249_, v___x_1249_);
if (v___x_1251_ == 0)
{
if (v___x_1250_ == 0)
{
return v___x_1247_;
}
else
{
size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = ((size_t)0ULL);
v___x_1253_ = lean_usize_of_nat(v___x_1249_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1246_, v___x_1252_, v___x_1253_, v___x_1247_);
return v___x_1254_;
}
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = lean_usize_of_nat(v___x_1249_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1246_, v___x_1255_, v___x_1256_, v___x_1247_);
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lake_Workspace_leanSrcPath(v_self_1258_);
lean_dec_ref(v_self_1258_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1260_, size_t v_i_1261_, size_t v_stop_1262_, lean_object* v_b_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_usize_dec_eq(v_i_1261_, v_stop_1262_);
if (v___x_1264_ == 0)
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; lean_object* v_config_1268_; lean_object* v_dir_1269_; lean_object* v_buildDir_1270_; lean_object* v_nativeLibDir_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_sub(v_i_1261_, v___x_1265_);
v___x_1267_ = lean_array_uget_borrowed(v_as_1260_, v___x_1266_);
v_config_1268_ = lean_ctor_get(v___x_1267_, 6);
v_dir_1269_ = lean_ctor_get(v___x_1267_, 4);
v_buildDir_1270_ = lean_ctor_get(v_config_1268_, 5);
v_nativeLibDir_1271_ = lean_ctor_get(v_config_1268_, 7);
lean_inc_ref(v_buildDir_1270_);
v___x_1272_ = l_System_FilePath_normalize(v_buildDir_1270_);
lean_inc_ref(v_dir_1269_);
v___x_1273_ = l_Lake_joinRelative(v_dir_1269_, v___x_1272_);
lean_inc_ref(v_nativeLibDir_1271_);
v___x_1274_ = l_System_FilePath_normalize(v_nativeLibDir_1271_);
v___x_1275_ = l_Lake_joinRelative(v___x_1273_, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_b_1263_);
v_i_1261_ = v___x_1266_;
v_b_1263_ = v___x_1276_;
goto _start;
}
else
{
return v_b_1263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1278_, lean_object* v_i_1279_, lean_object* v_stop_1280_, lean_object* v_b_1281_){
_start:
{
size_t v_i_boxed_1282_; size_t v_stop_boxed_1283_; lean_object* v_res_1284_; 
v_i_boxed_1282_ = lean_unbox_usize(v_i_1279_);
lean_dec(v_i_1279_);
v_stop_boxed_1283_ = lean_unbox_usize(v_stop_1280_);
lean_dec(v_stop_1280_);
v_res_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1278_, v_i_boxed_1282_, v_stop_boxed_1283_, v_b_1281_);
lean_dec_ref(v_as_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1285_){
_start:
{
lean_object* v_packages_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_packages_1286_ = lean_ctor_get(v_self_1285_, 4);
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_array_get_size(v_packages_1286_);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_nat_dec_lt(v___x_1289_, v___x_1288_);
if (v___x_1290_ == 0)
{
return v___x_1287_;
}
else
{
size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_usize_of_nat(v___x_1288_);
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1286_, v___x_1291_, v___x_1292_, v___x_1287_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lake_Workspace_sharedLibPath(v_self_1294_);
lean_dec_ref(v_self_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1296_){
_start:
{
uint8_t v___x_1297_; 
v___x_1297_ = l_System_Platform_isWindows;
if (v___x_1297_ == 0)
{
lean_object* v_lakeEnv_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_lakeEnv_1298_ = lean_ctor_get(v_self_1296_, 0);
v___x_1299_ = l_Lake_Workspace_binPath(v_self_1296_);
v___x_1300_ = l_Lake_Env_path(v_lakeEnv_1298_);
v___x_1301_ = l_List_appendTR___redArg(v___x_1299_, v___x_1300_);
return v___x_1301_;
}
else
{
lean_object* v_lakeEnv_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_lakeEnv_1302_ = lean_ctor_get(v_self_1296_, 0);
v___x_1303_ = l_Lake_Workspace_binPath(v_self_1296_);
v___x_1304_ = l_Lake_Workspace_sharedLibPath(v_self_1296_);
v___x_1305_ = l_List_appendTR___redArg(v___x_1303_, v___x_1304_);
v___x_1306_ = l_Lake_Env_path(v_lakeEnv_1302_);
v___x_1307_ = l_List_appendTR___redArg(v___x_1305_, v___x_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lake_Workspace_augmentedPath(v_self_1308_);
lean_dec_ref(v_self_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1310_){
_start:
{
lean_object* v_lakeEnv_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_lakeEnv_1311_ = lean_ctor_get(v_self_1310_, 0);
v___x_1312_ = l_Lake_Workspace_leanPath(v_self_1310_);
v___x_1313_ = l_Lake_Env_leanPath(v_lakeEnv_1311_);
v___x_1314_ = l_List_appendTR___redArg(v___x_1312_, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_Workspace_augmentedLeanPath(v_self_1315_);
lean_dec_ref(v_self_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1317_){
_start:
{
lean_object* v_lakeEnv_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_lakeEnv_1318_ = lean_ctor_get(v_self_1317_, 0);
v___x_1319_ = l_Lake_Workspace_leanSrcPath(v_self_1317_);
v___x_1320_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1318_);
v___x_1321_ = l_List_appendTR___redArg(v___x_1319_, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1322_);
lean_dec_ref(v_self_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1324_){
_start:
{
lean_object* v_lakeEnv_1325_; lean_object* v_lean_1326_; lean_object* v_initSharedLibPath_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_lakeEnv_1325_ = lean_ctor_get(v_self_1324_, 0);
v_lean_1326_ = lean_ctor_get(v_lakeEnv_1325_, 1);
v_initSharedLibPath_1327_ = lean_ctor_get(v_lakeEnv_1325_, 17);
lean_inc(v_initSharedLibPath_1327_);
v___x_1328_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1326_);
v___x_1329_ = l_Lake_Workspace_sharedLibPath(v_self_1324_);
lean_dec_ref(v_self_1324_);
v___x_1330_ = l_List_appendTR___redArg(v___x_1328_, v___x_1329_);
v___x_1331_ = l_List_appendTR___redArg(v___x_1330_, v_initSharedLibPath_1327_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0(lean_object* v_x_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__0___closed__1));
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0___boxed(lean_object* v_x_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_x_1337_);
lean_dec(v_x_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1(uint8_t v_b_1345_){
_start:
{
if (v_b_1345_ == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__1));
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
v___x_1347_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__3));
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___boxed(lean_object* v_b_1348_){
_start:
{
uint8_t v_b_boxed_1349_; lean_object* v_res_1350_; 
v_b_boxed_1349_ = lean_unbox(v_b_1348_);
v_res_1350_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_b_boxed_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1358_){
_start:
{
lean_object* v_lakeEnv_1359_; lean_object* v_lakeCache_1360_; lean_object* v_packages_1361_; lean_object* v_enableArtifactCache_x3f_1362_; lean_object* v_restoreAllArtifacts_x3f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v_val_1424_; lean_object* v___x_1426_; lean_object* v___y_1428_; uint8_t v_val_1441_; 
v_lakeEnv_1359_ = lean_ctor_get(v_self_1358_, 0);
v_lakeCache_1360_ = lean_ctor_get(v_self_1358_, 2);
v_packages_1361_ = lean_ctor_get(v_self_1358_, 4);
v_enableArtifactCache_x3f_1362_ = lean_ctor_get(v_lakeEnv_1359_, 6);
v_restoreAllArtifacts_x3f_1363_ = lean_ctor_get(v_lakeEnv_1359_, 7);
lean_inc_ref(v_lakeEnv_1359_);
v___x_1364_ = l_Lake_Env_baseVars(v_lakeEnv_1359_);
v___x_1365_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1360_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_lakeCache_1360_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1426_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (lean_obj_tag(v_enableArtifactCache_x3f_1362_) == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v_config_1445_; lean_object* v_enableArtifactCache_x3f_1446_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_array_fget_borrowed(v_packages_1361_, v___x_1443_);
v_config_1445_ = lean_ctor_get(v___x_1444_, 6);
v_enableArtifactCache_x3f_1446_ = lean_ctor_get(v_config_1445_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1446_) == 1)
{
lean_object* v_val_1447_; uint8_t v___x_1448_; 
v_val_1447_ = lean_ctor_get(v_enableArtifactCache_x3f_1446_, 0);
v___x_1448_ = lean_unbox(v_val_1447_);
v_val_1441_ = v___x_1448_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_enableArtifactCache_x3f_1446_);
v___y_1428_ = v___x_1449_;
goto v___jp_1427_;
}
}
else
{
lean_object* v_val_1450_; uint8_t v___x_1451_; 
v_val_1450_ = lean_ctor_get(v_enableArtifactCache_x3f_1362_, 0);
v___x_1451_ = lean_unbox(v_val_1450_);
v_val_1441_ = v___x_1451_;
goto v___jp_1440_;
}
v___jp_1368_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_vars_1390_; uint8_t v___x_1391_; 
lean_inc_ref(v___y_1369_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___y_1369_);
lean_ctor_set(v___x_1375_, 1, v___y_1374_);
v___x_1376_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1377_ = l_Lake_Workspace_augmentedPath(v_self_1358_);
v___x_1378_ = l_System_SearchPath_toString(v___x_1377_);
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1376_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = lean_unsigned_to_nat(7u);
v___x_1382_ = lean_mk_empty_array_with_capacity(v___x_1381_);
v___x_1383_ = lean_array_push(v___x_1382_, v___x_1367_);
v___x_1384_ = lean_array_push(v___x_1383_, v___y_1372_);
v___x_1385_ = lean_array_push(v___x_1384_, v___y_1370_);
v___x_1386_ = lean_array_push(v___x_1385_, v___y_1373_);
v___x_1387_ = lean_array_push(v___x_1386_, v___y_1371_);
v___x_1388_ = lean_array_push(v___x_1387_, v___x_1375_);
v___x_1389_ = lean_array_push(v___x_1388_, v___x_1380_);
v_vars_1390_ = l_Array_append___redArg(v___x_1364_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = l_System_Platform_isWindows;
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1392_ = l_Lake_sharedLibPathEnvVar;
v___x_1393_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1358_);
v___x_1394_ = l_System_SearchPath_toString(v___x_1393_);
v___x_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1392_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = lean_array_push(v_vars_1390_, v___x_1396_);
return v___x_1397_;
}
else
{
lean_dec_ref(v_self_1358_);
return v_vars_1390_;
}
}
v___jp_1398_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_config_1404_; uint8_t v_bootstrap_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_array_fget_borrowed(v_packages_1361_, v___x_1402_);
v_config_1404_ = lean_ctor_get(v___x_1403_, 6);
v_bootstrap_1405_ = lean_ctor_get_uint8(v_config_1404_, sizeof(void*)*27);
lean_inc_ref(v___y_1400_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___y_1400_);
lean_ctor_set(v___x_1406_, 1, v___y_1401_);
v___x_1407_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
v___x_1408_ = l_Lake_Workspace_augmentedLeanPath(v_self_1358_);
v___x_1409_ = l_System_SearchPath_toString(v___x_1408_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1407_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1413_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1358_);
v___x_1414_ = l_System_SearchPath_toString(v___x_1413_);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1412_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
if (v_bootstrap_1405_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = l_Lake_Env_leanGithash(v_lakeEnv_1359_);
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
v___y_1369_ = v___x_1417_;
v___y_1370_ = v___x_1406_;
v___y_1371_ = v___x_1416_;
v___y_1372_ = v___y_1399_;
v___y_1373_ = v___x_1411_;
v___y_1374_ = v___x_1419_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_box(0);
v___y_1369_ = v___x_1417_;
v___y_1370_ = v___x_1406_;
v___y_1371_ = v___x_1416_;
v___y_1372_ = v___y_1399_;
v___y_1373_ = v___x_1411_;
v___y_1374_ = v___x_1420_;
goto v___jp_1368_;
}
}
v___jp_1421_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1424_);
v___y_1399_ = v___y_1422_;
v___y_1400_ = v___y_1423_;
v___y_1401_ = v___x_1425_;
goto v___jp_1398_;
}
v___jp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1426_);
lean_ctor_set(v___x_1429_, 1, v___y_1428_);
v___x_1430_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__6));
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1363_) == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_config_1433_; lean_object* v_restoreAllArtifacts_x3f_1434_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_array_fget_borrowed(v_packages_1361_, v___x_1431_);
v_config_1433_ = lean_ctor_get(v___x_1432_, 6);
v_restoreAllArtifacts_x3f_1434_ = lean_ctor_get(v_config_1433_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1434_) == 1)
{
lean_object* v_val_1435_; uint8_t v___x_1436_; 
v_val_1435_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1434_, 0);
v___x_1436_ = lean_unbox(v_val_1435_);
v___y_1422_ = v___x_1429_;
v___y_1423_ = v___x_1430_;
v_val_1424_ = v___x_1436_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_restoreAllArtifacts_x3f_1434_);
v___y_1399_ = v___x_1429_;
v___y_1400_ = v___x_1430_;
v___y_1401_ = v___x_1437_;
goto v___jp_1398_;
}
}
else
{
lean_object* v_val_1438_; uint8_t v___x_1439_; 
v_val_1438_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1363_, 0);
v___x_1439_ = lean_unbox(v_val_1438_);
v___y_1422_ = v___x_1429_;
v___y_1423_ = v___x_1430_;
v_val_1424_ = v___x_1439_;
goto v___jp_1421_;
}
}
v___jp_1440_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1441_);
v___y_1428_ = v___x_1442_;
goto v___jp_1427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1452_, size_t v_i_1453_, size_t v_stop_1454_, lean_object* v_b_1455_){
_start:
{
uint8_t v___x_1457_; 
v___x_1457_ = lean_usize_dec_eq(v_i_1453_, v_stop_1454_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_array_uget_borrowed(v_as_1452_, v_i_1453_);
lean_inc(v___x_1458_);
v___x_1459_ = l_Lake_Package_clean(v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; size_t v___x_1461_; size_t v___x_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = ((size_t)1ULL);
v___x_1462_ = lean_usize_add(v_i_1453_, v___x_1461_);
v_i_1453_ = v___x_1462_;
v_b_1455_ = v_a_1460_;
goto _start;
}
else
{
return v___x_1459_;
}
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_b_1455_);
return v___x_1464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1465_, lean_object* v_i_1466_, lean_object* v_stop_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_){
_start:
{
size_t v_i_boxed_1470_; size_t v_stop_boxed_1471_; lean_object* v_res_1472_; 
v_i_boxed_1470_ = lean_unbox_usize(v_i_1466_);
lean_dec(v_i_1466_);
v_stop_boxed_1471_ = lean_unbox_usize(v_stop_1467_);
lean_dec(v_stop_1467_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1465_, v_i_boxed_1470_, v_stop_boxed_1471_, v_b_1468_);
lean_dec_ref(v_as_1465_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* v_self_1473_){
_start:
{
lean_object* v_packages_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_packages_1475_ = lean_ctor_get(v_self_1473_, 4);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_get_size(v_packages_1475_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_nat_dec_lt(v___x_1476_, v___x_1477_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
return v___x_1480_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_nat_dec_le(v___x_1477_, v___x_1477_);
if (v___x_1481_ == 0)
{
if (v___x_1479_ == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1478_);
return v___x_1482_;
}
else
{
size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((size_t)0ULL);
v___x_1484_ = lean_usize_of_nat(v___x_1477_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1475_, v___x_1483_, v___x_1484_, v___x_1478_);
return v___x_1485_;
}
}
else
{
size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = lean_usize_of_nat(v___x_1477_);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1475_, v___x_1486_, v___x_1487_, v___x_1478_);
return v___x_1488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lake_Workspace_clean(v_self_1489_);
lean_dec_ref(v_self_1489_);
return v_res_1491_;
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

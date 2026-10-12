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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(lean_object* v_self_41_, lean_object* v_as_42_, size_t v_i_43_, size_t v_stop_44_, lean_object* v_b_45_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_41_ = stack[0].m_obj;
lean_object* v_as_42_ = stack[1].m_obj;
size_t v_i_43_ = stack[2].m_num;
size_t v_stop_44_ = stack[3].m_num;
lean_object* v_b_45_ = stack[4].m_obj;
lean_object* v_res_76_;
v_res_76_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_41_, v_as_42_, v_i_43_, v_stop_44_, v_b_45_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___boxed(lean_object* v_self_77_, lean_object* v_as_78_, lean_object* v_i_79_, lean_object* v_stop_80_, lean_object* v_b_81_){
_start:
{
size_t v_i_boxed_82_; size_t v_stop_boxed_83_; lean_object* v_res_84_; 
v_i_boxed_82_ = lean_unbox_usize(v_i_79_);
lean_dec(v_i_79_);
v_stop_boxed_83_ = lean_unbox_usize(v_stop_80_);
lean_dec(v_stop_80_);
v_res_84_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_77_, v_as_78_, v_i_boxed_82_, v_stop_boxed_83_, v_b_81_);
lean_dec_ref(v_as_78_);
lean_dec_ref(v_self_77_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots(lean_object* v_self_87_){
_start:
{
lean_object* v_defaultTargets_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_defaultTargets_88_ = lean_ctor_get(v_self_87_, 17);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = ((lean_object*)(l_Lake_Package_defaultTargetRoots___closed__0));
v___x_91_ = lean_array_get_size(v_defaultTargets_88_);
v___x_92_ = lean_nat_dec_lt(v___x_89_, v___x_91_);
if (v___x_92_ == 0)
{
return v___x_90_;
}
else
{
size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_91_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_87_, v_defaultTargets_88_, v___x_93_, v___x_94_, v___x_90_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargetRoots___boxed(lean_object* v_self_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lake_Package_defaultTargetRoots(v_self_96_);
lean_dec_ref(v_self_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_root(lean_object* v_self_98_){
_start:
{
lean_object* v_packages_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_packages_99_ = lean_ctor_get(v_self_98_, 4);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_fget_borrowed(v_packages_99_, v___x_100_);
lean_inc(v___x_101_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_root___boxed(lean_object* v_self_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lake_Workspace_root(v_self_102_);
lean_dec_ref(v_self_102_);
return v_res_103_;
}
}
uint8_t l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(lean_object* v_self_104_){
_start:
{
lean_object* v_packages_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_config_108_; uint8_t v_bootstrap_109_; 
v_packages_105_ = lean_ctor_get(v_self_104_, 4);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_array_fget_borrowed(v_packages_105_, v___x_106_);
v_config_108_ = lean_ctor_get(v___x_107_, 6);
v_bootstrap_109_ = lean_ctor_get_uint8(v_config_108_, sizeof(void*)*28);
return v_bootstrap_109_;
}
}
LEAN_EXPORT void l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_104_ = stack[0].m_obj;
uint8_t v_res_110_;
v_res_110_ = l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(v_self_104_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(lean_object* v_self_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(v_self_111_);
lean_dec_ref(v_self_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object* v_self_114_){
_start:
{
lean_object* v_packages_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_dir_118_; 
v_packages_115_ = lean_ctor_get(v_self_114_, 4);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_array_fget_borrowed(v_packages_115_, v___x_116_);
v_dir_118_ = lean_ctor_get(v___x_117_, 4);
lean_inc_ref(v_dir_118_);
return v_dir_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object* v_self_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lake_Workspace_dir(v_self_119_);
lean_dec_ref(v_self_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object* v_self_121_){
_start:
{
lean_object* v_packages_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_config_125_; lean_object* v_toWorkspaceConfig_126_; 
v_packages_122_ = lean_ctor_get(v_self_121_, 4);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_array_fget_borrowed(v_packages_122_, v___x_123_);
v_config_125_ = lean_ctor_get(v___x_124_, 6);
v_toWorkspaceConfig_126_ = lean_ctor_get(v_config_125_, 0);
lean_inc_ref(v_toWorkspaceConfig_126_);
return v_toWorkspaceConfig_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object* v_self_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lake_Workspace_config(v_self_127_);
lean_dec_ref(v_self_127_);
return v_res_128_;
}
}
lean_object* l_Lake_Workspace_relLakeDir___redArg(){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lake_defaultLakeDir;
return v___x_130_;
}
}
LEAN_EXPORT void l_Lake_Workspace_relLakeDir___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_131_;
v_res_131_ = l_Lake_Workspace_relLakeDir___redArg();
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___redArg___boxed(lean_object* v___dummy_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lake_Workspace_relLakeDir___redArg();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object* v_self_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lake_defaultLakeDir;
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object* v_self_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_Workspace_relLakeDir(v_self_136_);
lean_dec_ref(v_self_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object* v_self_138_){
_start:
{
lean_object* v_packages_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_dir_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_packages_139_ = lean_ctor_get(v_self_138_, 4);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_array_fget_borrowed(v_packages_139_, v___x_140_);
v_dir_142_ = lean_ctor_get(v___x_141_, 4);
v___x_143_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_142_);
v___x_144_ = l_Lake_joinRelative(v_dir_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir___boxed(lean_object* v_self_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lake_Workspace_lakeDir(v_self_145_);
lean_dec_ref(v_self_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f(lean_object* v_ws_147_){
_start:
{
lean_object* v_lakeEnv_148_; lean_object* v_enableArtifactCache_x3f_149_; 
v_lakeEnv_148_ = lean_ctor_get(v_ws_147_, 0);
v_enableArtifactCache_x3f_149_ = lean_ctor_get(v_lakeEnv_148_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_149_) == 0)
{
lean_object* v_packages_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_config_153_; lean_object* v_enableArtifactCache_x3f_154_; 
v_packages_150_ = lean_ctor_get(v_ws_147_, 4);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_array_fget_borrowed(v_packages_150_, v___x_151_);
v_config_153_ = lean_ctor_get(v___x_152_, 6);
v_enableArtifactCache_x3f_154_ = lean_ctor_get(v_config_153_, 24);
lean_inc(v_enableArtifactCache_x3f_154_);
return v_enableArtifactCache_x3f_154_;
}
else
{
lean_inc_ref(v_enableArtifactCache_x3f_149_);
return v_enableArtifactCache_x3f_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache_x3f___boxed(lean_object* v_ws_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lake_Workspace_enableArtifactCache_x3f(v_ws_155_);
lean_dec_ref(v_ws_155_);
return v_res_156_;
}
}
uint8_t l_Lake_Workspace_enableArtifactCache(lean_object* v_ws_157_){
_start:
{
lean_object* v_lakeEnv_158_; lean_object* v_enableArtifactCache_x3f_159_; 
v_lakeEnv_158_ = lean_ctor_get(v_ws_157_, 0);
v_enableArtifactCache_x3f_159_ = lean_ctor_get(v_lakeEnv_158_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_159_) == 0)
{
lean_object* v_packages_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_config_163_; lean_object* v_enableArtifactCache_x3f_164_; 
v_packages_160_ = lean_ctor_get(v_ws_157_, 4);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_fget_borrowed(v_packages_160_, v___x_161_);
v_config_163_ = lean_ctor_get(v___x_162_, 6);
v_enableArtifactCache_x3f_164_ = lean_ctor_get(v_config_163_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_164_) == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
else
{
lean_object* v_val_166_; uint8_t v___x_167_; 
v_val_166_ = lean_ctor_get(v_enableArtifactCache_x3f_164_, 0);
v___x_167_ = lean_unbox(v_val_166_);
return v___x_167_;
}
}
else
{
lean_object* v_val_168_; uint8_t v___x_169_; 
v_val_168_ = lean_ctor_get(v_enableArtifactCache_x3f_159_, 0);
v___x_169_ = lean_unbox(v_val_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT void l_Lake_Workspace_enableArtifactCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_157_ = stack[0].m_obj;
uint8_t v_res_170_;
v_res_170_ = l_Lake_Workspace_enableArtifactCache(v_ws_157_);
stack->m_num = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_enableArtifactCache___boxed(lean_object* v_ws_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lake_Workspace_enableArtifactCache(v_ws_171_);
lean_dec_ref(v_ws_171_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
uint8_t l_Lake_Workspace_isRootArtifactCacheWritable(lean_object* v_ws_174_){
_start:
{
lean_object* v_lakeEnv_175_; lean_object* v_enableArtifactCache_x3f_176_; 
v_lakeEnv_175_ = lean_ctor_get(v_ws_174_, 0);
v_enableArtifactCache_x3f_176_ = lean_ctor_get(v_lakeEnv_175_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_176_) == 0)
{
lean_object* v_packages_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_config_180_; lean_object* v_enableArtifactCache_x3f_181_; 
v_packages_177_ = lean_ctor_get(v_ws_174_, 4);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_array_fget_borrowed(v_packages_177_, v___x_178_);
v_config_180_ = lean_ctor_get(v___x_179_, 6);
v_enableArtifactCache_x3f_181_ = lean_ctor_get(v_config_180_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_181_) == 0)
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
else
{
lean_object* v_val_183_; uint8_t v___x_184_; 
v_val_183_ = lean_ctor_get(v_enableArtifactCache_x3f_181_, 0);
v___x_184_ = lean_unbox(v_val_183_);
return v___x_184_;
}
}
else
{
lean_object* v_val_185_; uint8_t v___x_186_; 
v_val_185_ = lean_ctor_get(v_enableArtifactCache_x3f_176_, 0);
v___x_186_ = lean_unbox(v_val_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT void l_Lake_Workspace_isRootArtifactCacheWritable_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_174_ = stack[0].m_obj;
uint8_t v_res_187_;
v_res_187_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_174_);
stack->m_num = v_res_187_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheWritable___boxed(lean_object* v_ws_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_188_);
lean_dec_ref(v_ws_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
uint8_t l_Lake_Workspace_isRootArtifactCacheEnabled(lean_object* v_ws_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_191_);
return v___x_192_;
}
}
LEAN_EXPORT void l_Lake_Workspace_isRootArtifactCacheEnabled_0interp(lean_interpreter_value* stack)
{
lean_object* v_ws_191_ = stack[0].m_obj;
uint8_t v_res_193_;
v_res_193_ = l_Lake_Workspace_isRootArtifactCacheEnabled(v_ws_191_);
stack->m_num = v_res_193_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isRootArtifactCacheEnabled___boxed(lean_object* v_ws_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Lake_Workspace_isRootArtifactCacheEnabled(v_ws_194_);
lean_dec_ref(v_ws_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f(lean_object* v_ws_197_){
_start:
{
lean_object* v_lakeEnv_198_; lean_object* v_restoreAllArtifacts_x3f_199_; 
v_lakeEnv_198_ = lean_ctor_get(v_ws_197_, 0);
v_restoreAllArtifacts_x3f_199_ = lean_ctor_get(v_lakeEnv_198_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_199_) == 0)
{
lean_object* v_packages_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_config_203_; lean_object* v_restoreAllArtifacts_x3f_204_; 
v_packages_200_ = lean_ctor_get(v_ws_197_, 4);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_array_fget_borrowed(v_packages_200_, v___x_201_);
v_config_203_ = lean_ctor_get(v___x_202_, 6);
v_restoreAllArtifacts_x3f_204_ = lean_ctor_get(v_config_203_, 25);
lean_inc(v_restoreAllArtifacts_x3f_204_);
return v_restoreAllArtifacts_x3f_204_;
}
else
{
lean_inc_ref(v_restoreAllArtifacts_x3f_199_);
return v_restoreAllArtifacts_x3f_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(lean_object* v_ws_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_Workspace_restoreAllArtifacts_x3f(v_ws_205_);
lean_dec_ref(v_ws_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain(lean_object* v_ws_207_){
_start:
{
lean_object* v_lakeEnv_208_; lean_object* v_toolchain_209_; 
v_lakeEnv_208_ = lean_ctor_get(v_ws_207_, 0);
v_toolchain_209_ = lean_ctor_get(v_lakeEnv_208_, 19);
lean_inc_ref(v_toolchain_209_);
return v_toolchain_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain___boxed(lean_object* v_ws_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lake_Workspace_cacheToolchain(v_ws_210_);
lean_dec_ref(v_ws_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService(lean_object* v_ws_212_){
_start:
{
lean_object* v_lakeConfig_213_; lean_object* v_defaultCacheService_214_; 
v_lakeConfig_213_ = lean_ctor_get(v_ws_212_, 1);
v_defaultCacheService_214_ = lean_ctor_get(v_lakeConfig_213_, 1);
lean_inc_ref(v_defaultCacheService_214_);
return v_defaultCacheService_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService___boxed(lean_object* v_ws_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lake_Workspace_defaultCacheService(v_ws_215_);
lean_dec_ref(v_ws_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f(lean_object* v_ws_217_){
_start:
{
lean_object* v_lakeConfig_218_; lean_object* v_defaultCacheUploadService_x3f_219_; 
v_lakeConfig_218_ = lean_ctor_get(v_ws_217_, 1);
v_defaultCacheUploadService_x3f_219_ = lean_ctor_get(v_lakeConfig_218_, 2);
lean_inc(v_defaultCacheUploadService_x3f_219_);
return v_defaultCacheUploadService_x3f_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(lean_object* v_ws_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lake_Workspace_defaultCacheUploadService_x3f(v_ws_220_);
lean_dec_ref(v_ws_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object* v_ws_222_, lean_object* v_service_223_){
_start:
{
lean_object* v_lakeConfig_224_; lean_object* v_cacheServices_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_lakeConfig_224_ = lean_ctor_get(v_ws_222_, 1);
v_cacheServices_225_ = lean_ctor_get(v_lakeConfig_224_, 3);
v___x_226_ = lean_box(0);
v___x_227_ = l_Lean_Name_str___override(v___x_226_, v_service_223_);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_225_, v___x_227_);
lean_dec(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object* v_ws_229_, lean_object* v_service_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_Workspace_findCacheService_x3f(v_ws_229_, v_service_230_);
lean_dec_ref(v_ws_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* v_self_232_){
_start:
{
lean_object* v_packages_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_config_236_; lean_object* v_toWorkspaceConfig_237_; lean_object* v___x_238_; 
v_packages_233_ = lean_ctor_get(v_self_232_, 4);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = lean_array_fget_borrowed(v_packages_233_, v___x_234_);
v_config_236_ = lean_ctor_get(v___x_235_, 6);
v_toWorkspaceConfig_237_ = lean_ctor_get(v_config_236_, 0);
lean_inc_ref(v_toWorkspaceConfig_237_);
v___x_238_ = l_System_FilePath_normalize(v_toWorkspaceConfig_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir___boxed(lean_object* v_self_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lake_Workspace_relPkgsDir(v_self_239_);
lean_dec_ref(v_self_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* v_self_241_){
_start:
{
lean_object* v_packages_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_config_245_; lean_object* v_dir_246_; lean_object* v_toWorkspaceConfig_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_packages_242_ = lean_ctor_get(v_self_241_, 4);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_array_fget_borrowed(v_packages_242_, v___x_243_);
v_config_245_ = lean_ctor_get(v___x_244_, 6);
v_dir_246_ = lean_ctor_get(v___x_244_, 4);
v_toWorkspaceConfig_247_ = lean_ctor_get(v_config_245_, 0);
lean_inc_ref(v_toWorkspaceConfig_247_);
v___x_248_ = l_System_FilePath_normalize(v_toWorkspaceConfig_247_);
lean_inc_ref(v_dir_246_);
v___x_249_ = l_Lake_joinRelative(v_dir_246_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir___boxed(lean_object* v_self_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_Workspace_pkgsDir(v_self_250_);
lean_dec_ref(v_self_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object* v_self_252_){
_start:
{
lean_object* v_packages_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_config_256_; lean_object* v_toLeanConfig_257_; lean_object* v_moreLeanArgs_258_; 
v_packages_253_ = lean_ctor_get(v_self_252_, 4);
v___x_254_ = lean_unsigned_to_nat(0u);
v___x_255_ = lean_array_fget_borrowed(v_packages_253_, v___x_254_);
v_config_256_ = lean_ctor_get(v___x_255_, 6);
v_toLeanConfig_257_ = lean_ctor_get(v_config_256_, 1);
v_moreLeanArgs_258_ = lean_ctor_get(v_toLeanConfig_257_, 1);
lean_inc_ref(v_moreLeanArgs_258_);
return v_moreLeanArgs_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object* v_self_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lake_Workspace_leanArgs(v_self_259_);
lean_dec_ref(v_self_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* v_self_261_){
_start:
{
lean_object* v_packages_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_config_265_; lean_object* v_toLeanConfig_266_; lean_object* v_leanOptions_267_; lean_object* v___x_268_; 
v_packages_262_ = lean_ctor_get(v_self_261_, 4);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_array_fget_borrowed(v_packages_262_, v___x_263_);
v_config_265_ = lean_ctor_get(v___x_264_, 6);
v_toLeanConfig_266_ = lean_ctor_get(v_config_265_, 1);
v_leanOptions_267_ = lean_ctor_get(v_toLeanConfig_266_, 0);
v___x_268_ = l_Lean_LeanOptions_ofArray(v_leanOptions_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* v_self_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lake_Workspace_leanOptions(v_self_269_);
lean_dec_ref(v_self_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* v_self_271_){
_start:
{
lean_object* v_packages_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_config_275_; lean_object* v_toLeanConfig_276_; lean_object* v_leanOptions_277_; lean_object* v_moreServerOptions_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_packages_272_ = lean_ctor_get(v_self_271_, 4);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_array_fget_borrowed(v_packages_272_, v___x_273_);
v_config_275_ = lean_ctor_get(v___x_274_, 6);
v_toLeanConfig_276_ = lean_ctor_get(v_config_275_, 1);
v_leanOptions_277_ = lean_ctor_get(v_toLeanConfig_276_, 0);
v_moreServerOptions_278_ = lean_ctor_get(v_toLeanConfig_276_, 4);
v___x_279_ = l_Lean_LeanOptions_ofArray(v_leanOptions_277_);
v___x_280_ = l_Lean_LeanOptions_appendArray(v___x_279_, v_moreServerOptions_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* v_self_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lake_Workspace_serverOptions(v_self_281_);
lean_dec_ref(v_self_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object* v_self_283_){
_start:
{
lean_object* v_packages_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_packages_284_ = lean_ctor_get(v_self_283_, 4);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_array_fget_borrowed(v_packages_284_, v___x_285_);
v___x_287_ = l_Lake_Package_defaultTargetRoots(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object* v_self_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lake_Workspace_defaultTargetRoots(v_self_288_);
lean_dec_ref(v_self_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* v_self_290_){
_start:
{
lean_object* v_packages_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_dir_294_; lean_object* v_relManifestFile_295_; lean_object* v___x_296_; 
v_packages_291_ = lean_ctor_get(v_self_290_, 4);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_fget_borrowed(v_packages_291_, v___x_292_);
v_dir_294_ = lean_ctor_get(v___x_293_, 4);
v_relManifestFile_295_ = lean_ctor_get(v___x_293_, 9);
lean_inc_ref(v_relManifestFile_295_);
lean_inc_ref(v_dir_294_);
v___x_296_ = l_Lake_joinRelative(v_dir_294_, v_relManifestFile_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile___boxed(lean_object* v_self_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lake_Workspace_manifestFile(v_self_297_);
lean_dec_ref(v_self_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* v_self_300_){
_start:
{
lean_object* v_packages_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_dir_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_packages_301_ = lean_ctor_get(v_self_300_, 4);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_array_fget_borrowed(v_packages_301_, v___x_302_);
v_dir_304_ = lean_ctor_get(v___x_303_, 4);
v___x_305_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_304_);
v___x_306_ = l_Lake_joinRelative(v_dir_304_, v___x_305_);
v___x_307_ = ((lean_object*)(l_Lake_Workspace_packageOverridesFile___closed__0));
v___x_308_ = l_Lake_joinRelative(v___x_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile___boxed(lean_object* v_self_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lake_Workspace_packageOverridesFile(v_self_309_);
lean_dec_ref(v_self_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object* v_pkg_312_, lean_object* v_self_313_){
_start:
{
lean_object* v_lakeEnv_314_; lean_object* v_lakeConfig_315_; lean_object* v_lakeCache_316_; lean_object* v_lakeArgs_x3f_317_; lean_object* v_packages_318_; lean_object* v_packageMap_319_; lean_object* v_facetConfigs_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_331_; 
v_lakeEnv_314_ = lean_ctor_get(v_self_313_, 0);
v_lakeConfig_315_ = lean_ctor_get(v_self_313_, 1);
v_lakeCache_316_ = lean_ctor_get(v_self_313_, 2);
v_lakeArgs_x3f_317_ = lean_ctor_get(v_self_313_, 3);
v_packages_318_ = lean_ctor_get(v_self_313_, 4);
v_packageMap_319_ = lean_ctor_get(v_self_313_, 5);
v_facetConfigs_320_ = lean_ctor_get(v_self_313_, 6);
v_isSharedCheck_331_ = !lean_is_exclusive(v_self_313_);
if (v_isSharedCheck_331_ == 0)
{
v___x_322_ = v_self_313_;
v_isShared_323_ = v_isSharedCheck_331_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_facetConfigs_320_);
lean_inc(v_packageMap_319_);
lean_inc(v_packages_318_);
lean_inc(v_lakeArgs_x3f_317_);
lean_inc(v_lakeCache_316_);
lean_inc(v_lakeConfig_315_);
lean_inc(v_lakeEnv_314_);
lean_dec(v_self_313_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_331_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_keyName_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v_keyName_324_ = lean_ctor_get(v_pkg_312_, 2);
lean_inc(v_keyName_324_);
lean_inc_ref(v_pkg_312_);
v___x_325_ = lean_array_push(v_packages_318_, v_pkg_312_);
v___x_326_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_327_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_326_, v_keyName_324_, v_pkg_312_, v_packageMap_319_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 5, v___x_327_);
lean_ctor_set(v___x_322_, 4, v___x_325_);
v___x_329_ = v___x_322_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_lakeEnv_314_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_lakeConfig_315_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_lakeCache_316_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_lakeArgs_x3f_317_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_facetConfigs_320_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object* v_pkg_332_, lean_object* v_self_333_, lean_object* v_h__wsIdx_334_, lean_object* v_h__depIdxs_335_){
_start:
{
lean_object* v_lakeEnv_336_; lean_object* v_lakeConfig_337_; lean_object* v_lakeCache_338_; lean_object* v_lakeArgs_x3f_339_; lean_object* v_packages_340_; lean_object* v_packageMap_341_; lean_object* v_facetConfigs_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_353_; 
v_lakeEnv_336_ = lean_ctor_get(v_self_333_, 0);
v_lakeConfig_337_ = lean_ctor_get(v_self_333_, 1);
v_lakeCache_338_ = lean_ctor_get(v_self_333_, 2);
v_lakeArgs_x3f_339_ = lean_ctor_get(v_self_333_, 3);
v_packages_340_ = lean_ctor_get(v_self_333_, 4);
v_packageMap_341_ = lean_ctor_get(v_self_333_, 5);
v_facetConfigs_342_ = lean_ctor_get(v_self_333_, 6);
v_isSharedCheck_353_ = !lean_is_exclusive(v_self_333_);
if (v_isSharedCheck_353_ == 0)
{
v___x_344_ = v_self_333_;
v_isShared_345_ = v_isSharedCheck_353_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_facetConfigs_342_);
lean_inc(v_packageMap_341_);
lean_inc(v_packages_340_);
lean_inc(v_lakeArgs_x3f_339_);
lean_inc(v_lakeCache_338_);
lean_inc(v_lakeConfig_337_);
lean_inc(v_lakeEnv_336_);
lean_dec(v_self_333_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_353_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_keyName_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v_keyName_346_ = lean_ctor_get(v_pkg_332_, 2);
lean_inc(v_keyName_346_);
lean_inc_ref(v_pkg_332_);
v___x_347_ = lean_array_push(v_packages_340_, v_pkg_332_);
v___x_348_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_349_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_348_, v_keyName_346_, v_pkg_332_, v_packageMap_341_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 5, v___x_349_);
lean_ctor_set(v___x_344_, 4, v___x_347_);
v___x_351_ = v___x_344_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_lakeEnv_336_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_lakeConfig_337_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_lakeCache_338_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_lakeArgs_x3f_339_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_facetConfigs_342_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_356_, lean_object* v_self_357_){
_start:
{
lean_object* v_lakeEnv_358_; lean_object* v_lakeConfig_359_; lean_object* v_lakeCache_360_; lean_object* v_lakeArgs_x3f_361_; lean_object* v_packages_362_; lean_object* v_packageMap_363_; lean_object* v_facetConfigs_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_407_; 
v_lakeEnv_358_ = lean_ctor_get(v_self_357_, 0);
v_lakeConfig_359_ = lean_ctor_get(v_self_357_, 1);
v_lakeCache_360_ = lean_ctor_get(v_self_357_, 2);
v_lakeArgs_x3f_361_ = lean_ctor_get(v_self_357_, 3);
v_packages_362_ = lean_ctor_get(v_self_357_, 4);
v_packageMap_363_ = lean_ctor_get(v_self_357_, 5);
v_facetConfigs_364_ = lean_ctor_get(v_self_357_, 6);
v_isSharedCheck_407_ = !lean_is_exclusive(v_self_357_);
if (v_isSharedCheck_407_ == 0)
{
v___x_366_ = v_self_357_;
v_isShared_367_ = v_isSharedCheck_407_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_facetConfigs_364_);
lean_inc(v_packageMap_363_);
lean_inc(v_packages_362_);
lean_inc(v_lakeArgs_x3f_361_);
lean_inc(v_lakeCache_360_);
lean_inc(v_lakeConfig_359_);
lean_inc(v_lakeEnv_358_);
lean_dec(v_self_357_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_407_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_baseName_368_; lean_object* v_keyName_369_; lean_object* v_origName_370_; lean_object* v_dir_371_; lean_object* v_relDir_372_; lean_object* v_config_373_; lean_object* v_configFile_374_; lean_object* v_relConfigFile_375_; lean_object* v_relManifestFile_376_; lean_object* v_scope_377_; lean_object* v_remoteUrl_378_; lean_object* v_depConfigs_379_; lean_object* v_depPkgs_380_; lean_object* v_targetDecls_381_; lean_object* v_targetDeclMap_382_; lean_object* v_defaultTargets_383_; lean_object* v_scripts_384_; lean_object* v_defaultScripts_385_; lean_object* v_postUpdateHooks_386_; lean_object* v_buildArchive_387_; lean_object* v_testDriver_388_; lean_object* v_lintDriver_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_404_; 
v_baseName_368_ = lean_ctor_get(v_pkg_356_, 1);
v_keyName_369_ = lean_ctor_get(v_pkg_356_, 2);
v_origName_370_ = lean_ctor_get(v_pkg_356_, 3);
v_dir_371_ = lean_ctor_get(v_pkg_356_, 4);
v_relDir_372_ = lean_ctor_get(v_pkg_356_, 5);
v_config_373_ = lean_ctor_get(v_pkg_356_, 6);
v_configFile_374_ = lean_ctor_get(v_pkg_356_, 7);
v_relConfigFile_375_ = lean_ctor_get(v_pkg_356_, 8);
v_relManifestFile_376_ = lean_ctor_get(v_pkg_356_, 9);
v_scope_377_ = lean_ctor_get(v_pkg_356_, 10);
v_remoteUrl_378_ = lean_ctor_get(v_pkg_356_, 11);
v_depConfigs_379_ = lean_ctor_get(v_pkg_356_, 12);
v_depPkgs_380_ = lean_ctor_get(v_pkg_356_, 14);
v_targetDecls_381_ = lean_ctor_get(v_pkg_356_, 15);
v_targetDeclMap_382_ = lean_ctor_get(v_pkg_356_, 16);
v_defaultTargets_383_ = lean_ctor_get(v_pkg_356_, 17);
v_scripts_384_ = lean_ctor_get(v_pkg_356_, 18);
v_defaultScripts_385_ = lean_ctor_get(v_pkg_356_, 19);
v_postUpdateHooks_386_ = lean_ctor_get(v_pkg_356_, 20);
v_buildArchive_387_ = lean_ctor_get(v_pkg_356_, 21);
v_testDriver_388_ = lean_ctor_get(v_pkg_356_, 22);
v_lintDriver_389_ = lean_ctor_get(v_pkg_356_, 23);
v_isSharedCheck_404_ = !lean_is_exclusive(v_pkg_356_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; lean_object* v_unused_406_; 
v_unused_405_ = lean_ctor_get(v_pkg_356_, 13);
lean_dec(v_unused_405_);
v_unused_406_ = lean_ctor_get(v_pkg_356_, 0);
lean_dec(v_unused_406_);
v___x_391_ = v_pkg_356_;
v_isShared_392_ = v_isSharedCheck_404_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_lintDriver_389_);
lean_inc(v_testDriver_388_);
lean_inc(v_buildArchive_387_);
lean_inc(v_postUpdateHooks_386_);
lean_inc(v_defaultScripts_385_);
lean_inc(v_scripts_384_);
lean_inc(v_defaultTargets_383_);
lean_inc(v_targetDeclMap_382_);
lean_inc(v_targetDecls_381_);
lean_inc(v_depPkgs_380_);
lean_inc(v_depConfigs_379_);
lean_inc(v_remoteUrl_378_);
lean_inc(v_scope_377_);
lean_inc(v_relManifestFile_376_);
lean_inc(v_relConfigFile_375_);
lean_inc(v_configFile_374_);
lean_inc(v_config_373_);
lean_inc(v_relDir_372_);
lean_inc(v_dir_371_);
lean_inc(v_origName_370_);
lean_inc(v_keyName_369_);
lean_inc(v_baseName_368_);
lean_dec(v_pkg_356_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_404_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = lean_array_get_size(v_packages_362_);
v___x_394_ = ((lean_object*)(l_Lake_Workspace_addPackage___closed__0));
lean_inc(v_keyName_369_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 13, v___x_394_);
lean_ctor_set(v___x_391_, 0, v___x_393_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 24, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_baseName_368_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_keyName_369_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_origName_370_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v_dir_371_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_relDir_372_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_config_373_);
lean_ctor_set(v_reuseFailAlloc_403_, 7, v_configFile_374_);
lean_ctor_set(v_reuseFailAlloc_403_, 8, v_relConfigFile_375_);
lean_ctor_set(v_reuseFailAlloc_403_, 9, v_relManifestFile_376_);
lean_ctor_set(v_reuseFailAlloc_403_, 10, v_scope_377_);
lean_ctor_set(v_reuseFailAlloc_403_, 11, v_remoteUrl_378_);
lean_ctor_set(v_reuseFailAlloc_403_, 12, v_depConfigs_379_);
lean_ctor_set(v_reuseFailAlloc_403_, 13, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_403_, 14, v_depPkgs_380_);
lean_ctor_set(v_reuseFailAlloc_403_, 15, v_targetDecls_381_);
lean_ctor_set(v_reuseFailAlloc_403_, 16, v_targetDeclMap_382_);
lean_ctor_set(v_reuseFailAlloc_403_, 17, v_defaultTargets_383_);
lean_ctor_set(v_reuseFailAlloc_403_, 18, v_scripts_384_);
lean_ctor_set(v_reuseFailAlloc_403_, 19, v_defaultScripts_385_);
lean_ctor_set(v_reuseFailAlloc_403_, 20, v_postUpdateHooks_386_);
lean_ctor_set(v_reuseFailAlloc_403_, 21, v_buildArchive_387_);
lean_ctor_set(v_reuseFailAlloc_403_, 22, v_testDriver_388_);
lean_ctor_set(v_reuseFailAlloc_403_, 23, v_lintDriver_389_);
v___x_396_ = v_reuseFailAlloc_403_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
lean_inc_ref(v___x_396_);
v___x_397_ = lean_array_push(v_packages_362_, v___x_396_);
v___x_398_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_399_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_398_, v_keyName_369_, v___x_396_, v_packageMap_363_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 5, v___x_399_);
lean_ctor_set(v___x_366_, 4, v___x_397_);
v___x_401_ = v___x_366_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_lakeEnv_358_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_lakeConfig_359_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_lakeCache_360_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_lakeArgs_x3f_361_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_facetConfigs_364_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_408_, lean_object* v_self_409_){
_start:
{
lean_object* v_packageMap_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_packageMap_410_ = lean_ctor_get(v_self_409_, 5);
lean_inc(v_packageMap_410_);
lean_dec_ref(v_self_409_);
v___x_411_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_412_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_411_, v_packageMap_410_, v_keyName_408_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_a_416_, lean_object* v_x_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_baseName_419_; uint8_t v___x_420_; 
v_baseName_419_ = lean_ctor_get(v_a_416_, 1);
v___x_420_ = lean_name_eq(v_baseName_419_, v_name_413_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_dec_ref(v_a_416_);
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_414_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v___x_414_);
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_a_416_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_415_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_426_, lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v_a_429_, lean_object* v_x_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_426_, v___x_427_, v___x_428_, v_a_429_, v_x_430_, v___y_431_);
lean_dec_ref(v___y_431_);
lean_dec(v_name_426_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_455_, lean_object* v_self_456_){
_start:
{
lean_object* v_packages_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___f_462_; size_t v_sz_463_; size_t v___x_464_; lean_object* v___x_465_; lean_object* v_fst_466_; 
v_packages_457_ = lean_ctor_get(v_self_456_, 4);
lean_inc_ref(v_packages_457_);
lean_dec_ref(v_self_456_);
v___x_458_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__9));
v___x_459_ = lean_box(0);
v___x_460_ = lean_box(0);
v___x_461_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__10));
v___f_462_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_462_, 0, v_name_455_);
lean_closure_set(v___f_462_, 1, v___x_461_);
lean_closure_set(v___f_462_, 2, v___x_460_);
v_sz_463_ = lean_array_size(v_packages_457_);
v___x_464_ = ((size_t)0ULL);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_458_, v_packages_457_, v___f_462_, v_sz_463_, v___x_464_, v___x_461_);
v_fst_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_fst_466_);
lean_dec(v___x_465_);
if (lean_obj_tag(v_fst_466_) == 0)
{
return v___x_459_;
}
else
{
lean_object* v_val_467_; 
v_val_467_ = lean_ctor_get(v_fst_466_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v_fst_466_, 1);
return v_val_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_468_, lean_object* v_self_469_){
_start:
{
lean_object* v_packageMap_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_packageMap_470_ = lean_ctor_get(v_self_469_, 5);
lean_inc(v_packageMap_470_);
lean_dec_ref(v_self_469_);
v___x_471_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_472_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_471_, v_packageMap_470_, v_name_468_);
return v___x_472_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_476_, lean_object* v_as_477_, size_t v_sz_478_, size_t v_i_479_, lean_object* v_b_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_lt(v_i_479_, v_sz_478_);
if (v___x_481_ == 0)
{
lean_inc_ref(v_b_480_);
return v_b_480_;
}
else
{
lean_object* v_a_482_; lean_object* v_scripts_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_a_482_ = lean_array_uget_borrowed(v_as_477_, v_i_479_);
v_scripts_483_ = lean_ctor_get(v_a_482_, 18);
v___x_484_ = lean_box(0);
v___x_485_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_483_, v_script_476_);
if (lean_obj_tag(v___x_485_) == 1)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_484_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; size_t v___x_489_; size_t v___x_490_; 
lean_dec(v___x_485_);
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_479_, v___x_489_);
v_i_479_ = v___x_490_;
v_b_480_ = v___x_488_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_script_476_ = stack[0].m_obj;
lean_object* v_as_477_ = stack[1].m_obj;
size_t v_sz_478_ = stack[2].m_num;
size_t v_i_479_ = stack[3].m_num;
lean_object* v_b_480_ = stack[4].m_obj;
lean_object* v_res_492_;
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_476_, v_as_477_, v_sz_478_, v_i_479_, v_b_480_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_493_, lean_object* v_as_494_, lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_b_497_){
_start:
{
size_t v_sz_boxed_498_; size_t v_i_boxed_499_; lean_object* v_res_500_; 
v_sz_boxed_498_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_499_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_493_, v_as_494_, v_sz_boxed_498_, v_i_boxed_499_, v_b_497_);
lean_dec_ref(v_b_497_);
lean_dec_ref(v_as_494_);
lean_dec(v_script_493_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_501_, lean_object* v_self_502_){
_start:
{
lean_object* v_packages_503_; lean_object* v___x_504_; lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v_fst_509_; 
v_packages_503_ = lean_ctor_get(v_self_502_, 4);
v___x_504_ = lean_box(0);
v___x_505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_506_ = lean_array_size(v_packages_503_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_501_, v_packages_503_, v_sz_506_, v___x_507_, v___x_505_);
v_fst_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_fst_509_);
lean_dec_ref(v___x_508_);
if (lean_obj_tag(v_fst_509_) == 0)
{
return v___x_504_;
}
else
{
lean_object* v_val_510_; 
v_val_510_ = lean_ctor_get(v_fst_509_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v_fst_509_, 1);
return v_val_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_511_, lean_object* v_self_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_Workspace_findScript_x3f(v_script_511_, v_self_512_);
lean_dec_ref(v_self_512_);
lean_dec(v_script_511_);
return v_res_513_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_514_, lean_object* v_as_515_, size_t v_i_516_, size_t v_stop_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_usize_dec_eq(v_i_516_, v_stop_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_array_uget_borrowed(v_as_515_, v_i_516_);
v___x_520_ = l_Lake_Package_isLocalModule(v_mod_514_, v___x_519_);
if (v___x_520_ == 0)
{
size_t v___x_521_; size_t v___x_522_; 
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_516_, v___x_521_);
v_i_516_ = v___x_522_;
goto _start;
}
else
{
return v___x_520_;
}
}
else
{
uint8_t v___x_524_; 
v___x_524_ = 0;
return v___x_524_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_514_ = stack[0].m_obj;
lean_object* v_as_515_ = stack[1].m_obj;
size_t v_i_516_ = stack[2].m_num;
size_t v_stop_517_ = stack[3].m_num;
uint8_t v_res_525_;
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_514_, v_as_515_, v_i_516_, v_stop_517_);
stack->m_num = v_res_525_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_526_, lean_object* v_as_527_, lean_object* v_i_528_, lean_object* v_stop_529_){
_start:
{
size_t v_i_boxed_530_; size_t v_stop_boxed_531_; uint8_t v_res_532_; lean_object* v_r_533_; 
v_i_boxed_530_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_stop_boxed_531_ = lean_unbox_usize(v_stop_529_);
lean_dec(v_stop_529_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_526_, v_as_527_, v_i_boxed_530_, v_stop_boxed_531_);
lean_dec_ref(v_as_527_);
lean_dec(v_mod_526_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_534_, lean_object* v_self_535_){
_start:
{
lean_object* v_packages_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_packages_536_ = lean_ctor_get(v_self_535_, 4);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_array_get_size(v_packages_536_);
v___x_539_ = lean_nat_dec_lt(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
return v___x_539_;
}
else
{
if (v___x_539_ == 0)
{
return v___x_539_;
}
else
{
size_t v___x_540_; size_t v___x_541_; uint8_t v___x_542_; 
v___x_540_ = ((size_t)0ULL);
v___x_541_ = lean_usize_of_nat(v___x_538_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_534_, v_packages_536_, v___x_540_, v___x_541_);
return v___x_542_;
}
}
}
}
LEAN_EXPORT void l_Lake_Workspace_isLocalModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_534_ = stack[0].m_obj;
lean_object* v_self_535_ = stack[1].m_obj;
uint8_t v_res_543_;
v_res_543_ = l_Lake_Workspace_isLocalModule(v_mod_534_, v_self_535_);
stack->m_num = v_res_543_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_544_, lean_object* v_self_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lake_Workspace_isLocalModule(v_mod_544_, v_self_545_);
lean_dec_ref(v_self_545_);
lean_dec(v_mod_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_548_, lean_object* v_as_549_, size_t v_i_550_, size_t v_stop_551_){
_start:
{
uint8_t v___x_552_; 
v___x_552_ = lean_usize_dec_eq(v_i_550_, v_stop_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_array_uget_borrowed(v_as_549_, v_i_550_);
v___x_554_ = l_Lake_Package_isBuildableModule(v_mod_548_, v___x_553_);
if (v___x_554_ == 0)
{
size_t v___x_555_; size_t v___x_556_; 
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_550_, v___x_555_);
v_i_550_ = v___x_556_;
goto _start;
}
else
{
return v___x_554_;
}
}
else
{
uint8_t v___x_558_; 
v___x_558_ = 0;
return v___x_558_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_548_ = stack[0].m_obj;
lean_object* v_as_549_ = stack[1].m_obj;
size_t v_i_550_ = stack[2].m_num;
size_t v_stop_551_ = stack[3].m_num;
uint8_t v_res_559_;
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_548_, v_as_549_, v_i_550_, v_stop_551_);
stack->m_num = v_res_559_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_560_, lean_object* v_as_561_, lean_object* v_i_562_, lean_object* v_stop_563_){
_start:
{
size_t v_i_boxed_564_; size_t v_stop_boxed_565_; uint8_t v_res_566_; lean_object* v_r_567_; 
v_i_boxed_564_ = lean_unbox_usize(v_i_562_);
lean_dec(v_i_562_);
v_stop_boxed_565_ = lean_unbox_usize(v_stop_563_);
lean_dec(v_stop_563_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_560_, v_as_561_, v_i_boxed_564_, v_stop_boxed_565_);
lean_dec_ref(v_as_561_);
lean_dec(v_mod_560_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_568_, lean_object* v_self_569_){
_start:
{
lean_object* v_packages_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_packages_570_ = lean_ctor_get(v_self_569_, 4);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_array_get_size(v_packages_570_);
v___x_573_ = lean_nat_dec_lt(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
return v___x_573_;
}
else
{
if (v___x_573_ == 0)
{
return v___x_573_;
}
else
{
size_t v___x_574_; size_t v___x_575_; uint8_t v___x_576_; 
v___x_574_ = ((size_t)0ULL);
v___x_575_ = lean_usize_of_nat(v___x_572_);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_568_, v_packages_570_, v___x_574_, v___x_575_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT void l_Lake_Workspace_isBuildableModule_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_568_ = stack[0].m_obj;
lean_object* v_self_569_ = stack[1].m_obj;
uint8_t v_res_577_;
v_res_577_ = l_Lake_Workspace_isBuildableModule(v_mod_568_, v_self_569_);
stack->m_num = v_res_577_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_578_, lean_object* v_self_579_){
_start:
{
uint8_t v_res_580_; lean_object* v_r_581_; 
v_res_580_ = l_Lake_Workspace_isBuildableModule(v_mod_578_, v_self_579_);
lean_dec_ref(v_self_579_);
lean_dec(v_mod_578_);
v_r_581_ = lean_box(v_res_580_);
return v_r_581_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_585_, lean_object* v_as_586_, size_t v_sz_587_, size_t v_i_588_, lean_object* v_b_589_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = lean_usize_dec_lt(v_i_588_, v_sz_587_);
if (v___x_590_ == 0)
{
lean_dec(v_mod_585_);
lean_inc_ref(v_b_589_);
return v_b_589_;
}
else
{
lean_object* v___x_591_; lean_object* v_a_592_; lean_object* v___x_593_; 
v___x_591_ = lean_box(0);
v_a_592_ = lean_array_uget_borrowed(v_as_586_, v_i_588_);
lean_inc(v_a_592_);
lean_inc(v_mod_585_);
v___x_593_ = l_Lake_Package_findModule_x3f(v_mod_585_, v_a_592_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_mod_585_);
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_591_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; size_t v___x_597_; size_t v___x_598_; 
lean_dec(v___x_593_);
v___x_596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_597_ = ((size_t)1ULL);
v___x_598_ = lean_usize_add(v_i_588_, v___x_597_);
v_i_588_ = v___x_598_;
v_b_589_ = v___x_596_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_585_ = stack[0].m_obj;
lean_object* v_as_586_ = stack[1].m_obj;
size_t v_sz_587_ = stack[2].m_num;
size_t v_i_588_ = stack[3].m_num;
lean_object* v_b_589_ = stack[4].m_obj;
lean_object* v_res_600_;
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_585_, v_as_586_, v_sz_587_, v_i_588_, v_b_589_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_601_, lean_object* v_as_602_, lean_object* v_sz_603_, lean_object* v_i_604_, lean_object* v_b_605_){
_start:
{
size_t v_sz_boxed_606_; size_t v_i_boxed_607_; lean_object* v_res_608_; 
v_sz_boxed_606_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v_i_boxed_607_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_601_, v_as_602_, v_sz_boxed_606_, v_i_boxed_607_, v_b_605_);
lean_dec_ref(v_b_605_);
lean_dec_ref(v_as_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_609_, lean_object* v_self_610_){
_start:
{
lean_object* v_packages_611_; lean_object* v___x_612_; lean_object* v___x_613_; size_t v_sz_614_; size_t v___x_615_; lean_object* v___x_616_; lean_object* v_fst_617_; 
v_packages_611_ = lean_ctor_get(v_self_610_, 4);
v___x_612_ = lean_box(0);
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_614_ = lean_array_size(v_packages_611_);
v___x_615_ = ((size_t)0ULL);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_609_, v_packages_611_, v_sz_614_, v___x_615_, v___x_613_);
v_fst_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_fst_617_);
lean_dec_ref(v___x_616_);
if (lean_obj_tag(v_fst_617_) == 0)
{
return v___x_612_;
}
else
{
lean_object* v_val_618_; 
v_val_618_ = lean_ctor_get(v_fst_617_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v_fst_617_, 1);
return v_val_618_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_619_, lean_object* v_self_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lake_Workspace_findModule_x3f(v_mod_619_, v_self_620_);
lean_dec_ref(v_self_620_);
return v_res_621_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_622_, lean_object* v_as_623_, size_t v_i_624_, size_t v_stop_625_, lean_object* v_b_626_){
_start:
{
lean_object* v___y_628_; uint8_t v___x_632_; 
v___x_632_ = lean_usize_dec_eq(v_i_624_, v_stop_625_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_array_uget_borrowed(v_as_623_, v_i_624_);
lean_inc(v___x_633_);
lean_inc(v_mod_622_);
v___x_634_ = l_Lake_Package_findModule_x3f(v_mod_622_, v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
v___y_628_ = v_b_626_;
goto v___jp_627_;
}
else
{
lean_object* v_val_635_; lean_object* v___x_636_; 
v_val_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = lean_array_push(v_b_626_, v_val_635_);
v___y_628_ = v___x_636_;
goto v___jp_627_;
}
}
else
{
lean_dec(v_mod_622_);
return v_b_626_;
}
v___jp_627_:
{
size_t v___x_629_; size_t v___x_630_; 
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_624_, v___x_629_);
v_i_624_ = v___x_630_;
v_b_626_ = v___y_628_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_622_ = stack[0].m_obj;
lean_object* v_as_623_ = stack[1].m_obj;
size_t v_i_624_ = stack[2].m_num;
size_t v_stop_625_ = stack[3].m_num;
lean_object* v_b_626_ = stack[4].m_obj;
lean_object* v_res_637_;
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_622_, v_as_623_, v_i_624_, v_stop_625_, v_b_626_);
stack->m_obj
 = v_res_637_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_638_, lean_object* v_as_639_, lean_object* v_i_640_, lean_object* v_stop_641_, lean_object* v_b_642_){
_start:
{
size_t v_i_boxed_643_; size_t v_stop_boxed_644_; lean_object* v_res_645_; 
v_i_boxed_643_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_stop_boxed_644_ = lean_unbox_usize(v_stop_641_);
lean_dec(v_stop_641_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_638_, v_as_639_, v_i_boxed_643_, v_stop_boxed_644_, v_b_642_);
lean_dec_ref(v_as_639_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_648_, lean_object* v_as_649_, lean_object* v_start_650_, lean_object* v_stop_651_){
_start:
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_653_ = lean_nat_dec_lt(v_start_650_, v_stop_651_);
if (v___x_653_ == 0)
{
lean_dec(v_mod_648_);
return v___x_652_;
}
else
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = lean_array_get_size(v_as_649_);
v___x_655_ = lean_nat_dec_le(v_stop_651_, v___x_654_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
v___x_656_ = lean_nat_dec_lt(v_start_650_, v___x_654_);
if (v___x_656_ == 0)
{
lean_dec(v_mod_648_);
return v___x_652_;
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_usize_of_nat(v_start_650_);
v___x_658_ = lean_usize_of_nat(v___x_654_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_648_, v_as_649_, v___x_657_, v___x_658_, v___x_652_);
return v___x_659_;
}
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_usize_of_nat(v_start_650_);
v___x_661_ = lean_usize_of_nat(v_stop_651_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_648_, v_as_649_, v___x_660_, v___x_661_, v___x_652_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_663_, lean_object* v_as_664_, lean_object* v_start_665_, lean_object* v_stop_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_663_, v_as_664_, v_start_665_, v_stop_666_);
lean_dec(v_stop_666_);
lean_dec(v_start_665_);
lean_dec_ref(v_as_664_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_668_, lean_object* v_self_669_){
_start:
{
lean_object* v_packages_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_packages_670_ = lean_ctor_get(v_self_669_, 4);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_array_get_size(v_packages_670_);
v___x_673_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_668_, v_packages_670_, v___x_671_, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_674_, lean_object* v_self_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lake_Workspace_findModules(v_mod_674_, v_self_675_);
lean_dec_ref(v_self_675_);
return v_res_676_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_677_, lean_object* v_as_678_, size_t v_sz_679_, size_t v_i_680_, lean_object* v_b_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_682_ == 0)
{
lean_dec(v_mod_677_);
lean_inc_ref(v_b_681_);
return v_b_681_;
}
else
{
lean_object* v___x_683_; lean_object* v_a_684_; lean_object* v___x_685_; 
v___x_683_ = lean_box(0);
v_a_684_ = lean_array_uget_borrowed(v_as_678_, v_i_680_);
lean_inc(v_a_684_);
lean_inc(v_mod_677_);
v___x_685_ = l_Lake_Package_findTargetModule_x3f(v_mod_677_, v_a_684_);
if (lean_obj_tag(v___x_685_) == 1)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v_mod_677_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_683_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; size_t v___x_689_; size_t v___x_690_; 
lean_dec(v___x_685_);
v___x_688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_680_, v___x_689_);
v_i_680_ = v___x_690_;
v_b_681_ = v___x_688_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_677_ = stack[0].m_obj;
lean_object* v_as_678_ = stack[1].m_obj;
size_t v_sz_679_ = stack[2].m_num;
size_t v_i_680_ = stack[3].m_num;
lean_object* v_b_681_ = stack[4].m_obj;
lean_object* v_res_692_;
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_677_, v_as_678_, v_sz_679_, v_i_680_, v_b_681_);
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_693_, lean_object* v_as_694_, lean_object* v_sz_695_, lean_object* v_i_696_, lean_object* v_b_697_){
_start:
{
size_t v_sz_boxed_698_; size_t v_i_boxed_699_; lean_object* v_res_700_; 
v_sz_boxed_698_ = lean_unbox_usize(v_sz_695_);
lean_dec(v_sz_695_);
v_i_boxed_699_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_693_, v_as_694_, v_sz_boxed_698_, v_i_boxed_699_, v_b_697_);
lean_dec_ref(v_b_697_);
lean_dec_ref(v_as_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_701_, lean_object* v_self_702_){
_start:
{
lean_object* v_packages_703_; lean_object* v___x_704_; lean_object* v___x_705_; size_t v_sz_706_; size_t v___x_707_; lean_object* v___x_708_; lean_object* v_fst_709_; 
v_packages_703_ = lean_ctor_get(v_self_702_, 4);
v___x_704_ = lean_box(0);
v___x_705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_706_ = lean_array_size(v_packages_703_);
v___x_707_ = ((size_t)0ULL);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_701_, v_packages_703_, v_sz_706_, v___x_707_, v___x_705_);
v_fst_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_fst_709_);
lean_dec_ref(v___x_708_);
if (lean_obj_tag(v_fst_709_) == 0)
{
return v___x_704_;
}
else
{
lean_object* v_val_710_; 
v_val_710_ = lean_ctor_get(v_fst_709_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v_fst_709_, 1);
return v_val_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_711_, lean_object* v_self_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_711_, v_self_712_);
lean_dec_ref(v_self_712_);
return v_res_713_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_714_, lean_object* v_as_715_, size_t v_sz_716_, size_t v_i_717_, lean_object* v_b_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_lt(v_i_717_, v_sz_716_);
if (v___x_719_ == 0)
{
lean_dec_ref(v_path_714_);
lean_inc_ref(v_b_718_);
return v_b_718_;
}
else
{
lean_object* v___x_720_; lean_object* v_a_721_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
v_a_721_ = lean_array_uget_borrowed(v_as_715_, v_i_717_);
lean_inc(v_a_721_);
lean_inc_ref(v_path_714_);
v___x_722_ = l_Lake_Package_findModuleBySrc_x3f(v_path_714_, v_a_721_);
if (lean_obj_tag(v___x_722_) == 1)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec_ref(v_path_714_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v___x_720_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; size_t v___x_726_; size_t v___x_727_; 
lean_dec(v___x_722_);
v___x_725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_717_, v___x_726_);
v_i_717_ = v___x_727_;
v_b_718_ = v___x_725_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_path_714_ = stack[0].m_obj;
lean_object* v_as_715_ = stack[1].m_obj;
size_t v_sz_716_ = stack[2].m_num;
size_t v_i_717_ = stack[3].m_num;
lean_object* v_b_718_ = stack[4].m_obj;
lean_object* v_res_729_;
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_714_, v_as_715_, v_sz_716_, v_i_717_, v_b_718_);
stack->m_obj
 = v_res_729_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_730_, lean_object* v_as_731_, lean_object* v_sz_732_, lean_object* v_i_733_, lean_object* v_b_734_){
_start:
{
size_t v_sz_boxed_735_; size_t v_i_boxed_736_; lean_object* v_res_737_; 
v_sz_boxed_735_ = lean_unbox_usize(v_sz_732_);
lean_dec(v_sz_732_);
v_i_boxed_736_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_730_, v_as_731_, v_sz_boxed_735_, v_i_boxed_736_, v_b_734_);
lean_dec_ref(v_b_734_);
lean_dec_ref(v_as_731_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_738_, lean_object* v_self_739_){
_start:
{
lean_object* v_packages_740_; lean_object* v___x_741_; lean_object* v___x_742_; size_t v_sz_743_; size_t v___x_744_; lean_object* v___x_745_; lean_object* v_fst_746_; 
v_packages_740_ = lean_ctor_get(v_self_739_, 4);
v___x_741_ = lean_box(0);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_743_ = lean_array_size(v_packages_740_);
v___x_744_ = ((size_t)0ULL);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_738_, v_packages_740_, v_sz_743_, v___x_744_, v___x_742_);
v_fst_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_fst_746_);
lean_dec_ref(v___x_745_);
if (lean_obj_tag(v_fst_746_) == 0)
{
return v___x_741_;
}
else
{
lean_object* v_val_747_; 
v_val_747_ = lean_ctor_get(v_fst_746_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v_fst_746_, 1);
return v_val_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_748_, lean_object* v_self_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_748_, v_self_749_);
lean_dec_ref(v_self_749_);
return v_res_750_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_754_, lean_object* v_as_755_, size_t v_sz_756_, size_t v_i_757_, lean_object* v_b_758_){
_start:
{
lean_object* v_a_760_; uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_lt(v_i_757_, v_sz_756_);
if (v___x_764_ == 0)
{
lean_inc_ref(v_b_758_);
return v_b_758_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_a_767_; lean_object* v___x_768_; 
v___x_765_ = lean_box(0);
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_767_ = lean_array_uget_borrowed(v_as_755_, v_i_757_);
v___x_768_ = l_Lake_Package_findTargetDecl_x3f(v_name_754_, v_a_767_);
if (lean_obj_tag(v___x_768_) == 0)
{
v_a_760_ = v___x_766_;
goto v___jp_759_;
}
else
{
lean_object* v_val_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_784_; 
v_val_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_784_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_784_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_val_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_784_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_name_773_; lean_object* v_kind_774_; lean_object* v_config_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_name_773_ = lean_ctor_get(v_val_769_, 1);
lean_inc(v_name_773_);
v_kind_774_ = lean_ctor_get(v_val_769_, 2);
lean_inc(v_kind_774_);
v_config_775_ = lean_ctor_get(v_val_769_, 3);
lean_inc(v_config_775_);
lean_dec(v_val_769_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_777_ = lean_name_eq(v_kind_774_, v___x_776_);
lean_dec(v_kind_774_);
if (v___x_777_ == 0)
{
lean_dec(v_config_775_);
lean_dec(v_name_773_);
lean_del_object(v___x_771_);
v_a_760_ = v___x_766_;
goto v___jp_759_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_inc(v_a_767_);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v_a_767_);
lean_ctor_set(v___x_778_, 1, v_name_773_);
lean_ctor_set(v___x_778_, 2, v_config_775_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_778_);
v___x_780_ = v___x_771_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_783_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v___x_765_);
return v___x_782_;
}
}
}
}
}
v___jp_759_:
{
size_t v___x_761_; size_t v___x_762_; 
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_757_, v___x_761_);
v_i_757_ = v___x_762_;
v_b_758_ = v_a_760_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_754_ = stack[0].m_obj;
lean_object* v_as_755_ = stack[1].m_obj;
size_t v_sz_756_ = stack[2].m_num;
size_t v_i_757_ = stack[3].m_num;
lean_object* v_b_758_ = stack[4].m_obj;
lean_object* v_res_785_;
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_754_, v_as_755_, v_sz_756_, v_i_757_, v_b_758_);
stack->m_obj
 = v_res_785_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_786_, lean_object* v_as_787_, lean_object* v_sz_788_, lean_object* v_i_789_, lean_object* v_b_790_){
_start:
{
size_t v_sz_boxed_791_; size_t v_i_boxed_792_; lean_object* v_res_793_; 
v_sz_boxed_791_ = lean_unbox_usize(v_sz_788_);
lean_dec(v_sz_788_);
v_i_boxed_792_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_786_, v_as_787_, v_sz_boxed_791_, v_i_boxed_792_, v_b_790_);
lean_dec_ref(v_b_790_);
lean_dec_ref(v_as_787_);
lean_dec(v_name_786_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_794_, lean_object* v_self_795_){
_start:
{
lean_object* v_packages_796_; lean_object* v___x_797_; lean_object* v___x_798_; size_t v_sz_799_; size_t v___x_800_; lean_object* v___x_801_; lean_object* v_fst_802_; 
v_packages_796_ = lean_ctor_get(v_self_795_, 4);
v___x_797_ = lean_box(0);
v___x_798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_799_ = lean_array_size(v_packages_796_);
v___x_800_ = ((size_t)0ULL);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_794_, v_packages_796_, v_sz_799_, v___x_800_, v___x_798_);
v_fst_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_fst_802_);
lean_dec_ref(v___x_801_);
if (lean_obj_tag(v_fst_802_) == 0)
{
return v___x_797_;
}
else
{
lean_object* v_val_803_; 
v_val_803_ = lean_ctor_get(v_fst_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref_known(v_fst_802_, 1);
return v_val_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_804_, lean_object* v_self_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lake_Workspace_findLeanLib_x3f(v_name_804_, v_self_805_);
lean_dec_ref(v_self_805_);
lean_dec(v_name_804_);
return v_res_806_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_807_, lean_object* v_as_808_, size_t v_sz_809_, size_t v_i_810_, lean_object* v_b_811_){
_start:
{
lean_object* v_a_813_; uint8_t v___x_817_; 
v___x_817_ = lean_usize_dec_lt(v_i_810_, v_sz_809_);
if (v___x_817_ == 0)
{
lean_inc_ref(v_b_811_);
return v_b_811_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_a_820_; lean_object* v___x_821_; 
v___x_818_ = lean_box(0);
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_820_ = lean_array_uget_borrowed(v_as_808_, v_i_810_);
v___x_821_ = l_Lake_Package_findTargetDecl_x3f(v_name_807_, v_a_820_);
if (lean_obj_tag(v___x_821_) == 0)
{
v_a_813_ = v___x_819_;
goto v___jp_812_;
}
else
{
lean_object* v_val_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_837_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_837_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_837_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_val_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_837_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_name_826_; lean_object* v_kind_827_; lean_object* v_config_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_name_826_ = lean_ctor_get(v_val_822_, 1);
lean_inc(v_name_826_);
v_kind_827_ = lean_ctor_get(v_val_822_, 2);
lean_inc(v_kind_827_);
v_config_828_ = lean_ctor_get(v_val_822_, 3);
lean_inc(v_config_828_);
lean_dec(v_val_822_);
v___x_829_ = l_Lake_LeanExe_keyword;
v___x_830_ = lean_name_eq(v_kind_827_, v___x_829_);
lean_dec(v_kind_827_);
if (v___x_830_ == 0)
{
lean_dec(v_config_828_);
lean_dec(v_name_826_);
lean_del_object(v___x_824_);
v_a_813_ = v___x_819_;
goto v___jp_812_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_833_; 
lean_inc(v_a_820_);
v___x_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_831_, 0, v_a_820_);
lean_ctor_set(v___x_831_, 1, v_name_826_);
lean_ctor_set(v___x_831_, 2, v_config_828_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_831_);
v___x_833_ = v___x_824_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_836_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_818_);
return v___x_835_;
}
}
}
}
}
v___jp_812_:
{
size_t v___x_814_; size_t v___x_815_; 
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_810_, v___x_814_);
v_i_810_ = v___x_815_;
v_b_811_ = v_a_813_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_807_ = stack[0].m_obj;
lean_object* v_as_808_ = stack[1].m_obj;
size_t v_sz_809_ = stack[2].m_num;
size_t v_i_810_ = stack[3].m_num;
lean_object* v_b_811_ = stack[4].m_obj;
lean_object* v_res_838_;
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_807_, v_as_808_, v_sz_809_, v_i_810_, v_b_811_);
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_839_, lean_object* v_as_840_, lean_object* v_sz_841_, lean_object* v_i_842_, lean_object* v_b_843_){
_start:
{
size_t v_sz_boxed_844_; size_t v_i_boxed_845_; lean_object* v_res_846_; 
v_sz_boxed_844_ = lean_unbox_usize(v_sz_841_);
lean_dec(v_sz_841_);
v_i_boxed_845_ = lean_unbox_usize(v_i_842_);
lean_dec(v_i_842_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_839_, v_as_840_, v_sz_boxed_844_, v_i_boxed_845_, v_b_843_);
lean_dec_ref(v_b_843_);
lean_dec_ref(v_as_840_);
lean_dec(v_name_839_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_847_, lean_object* v_self_848_){
_start:
{
lean_object* v_packages_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; lean_object* v_fst_855_; 
v_packages_849_ = lean_ctor_get(v_self_848_, 4);
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_852_ = lean_array_size(v_packages_849_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_847_, v_packages_849_, v_sz_852_, v___x_853_, v___x_851_);
v_fst_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_fst_855_);
lean_dec_ref(v___x_854_);
if (lean_obj_tag(v_fst_855_) == 0)
{
return v___x_850_;
}
else
{
lean_object* v_val_856_; 
v_val_856_ = lean_ctor_get(v_fst_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_fst_855_, 1);
return v_val_856_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_857_, lean_object* v_self_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lake_Workspace_findLeanExe_x3f(v_name_857_, v_self_858_);
lean_dec_ref(v_self_858_);
lean_dec(v_name_857_);
return v_res_859_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_860_, lean_object* v_as_861_, size_t v_sz_862_, size_t v_i_863_, lean_object* v_b_864_){
_start:
{
lean_object* v_a_866_; uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_lt(v_i_863_, v_sz_862_);
if (v___x_870_ == 0)
{
lean_inc_ref(v_b_864_);
return v_b_864_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_874_; 
v___x_871_ = lean_box(0);
v___x_872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_873_ = lean_array_uget_borrowed(v_as_861_, v_i_863_);
v___x_874_ = l_Lake_Package_findTargetDecl_x3f(v_name_860_, v_a_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
v_a_866_ = v___x_872_;
goto v___jp_865_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_890_; 
v_val_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_890_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_890_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_val_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_890_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_name_879_; lean_object* v_kind_880_; lean_object* v_config_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_name_879_ = lean_ctor_get(v_val_875_, 1);
lean_inc(v_name_879_);
v_kind_880_ = lean_ctor_get(v_val_875_, 2);
lean_inc(v_kind_880_);
v_config_881_ = lean_ctor_get(v_val_875_, 3);
lean_inc(v_config_881_);
lean_dec(v_val_875_);
v___x_882_ = l_Lake_ExternLib_keyword;
v___x_883_ = lean_name_eq(v_kind_880_, v___x_882_);
lean_dec(v_kind_880_);
if (v___x_883_ == 0)
{
lean_dec(v_config_881_);
lean_dec(v_name_879_);
lean_del_object(v___x_877_);
v_a_866_ = v___x_872_;
goto v___jp_865_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_inc(v_a_873_);
v___x_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_884_, 0, v_a_873_);
lean_ctor_set(v___x_884_, 1, v_name_879_);
lean_ctor_set(v___x_884_, 2, v_config_881_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_884_);
v___x_886_ = v___x_877_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_889_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v___x_871_);
return v___x_888_;
}
}
}
}
}
v___jp_865_:
{
size_t v___x_867_; size_t v___x_868_; 
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_863_, v___x_867_);
v_i_863_ = v___x_868_;
v_b_864_ = v_a_866_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_860_ = stack[0].m_obj;
lean_object* v_as_861_ = stack[1].m_obj;
size_t v_sz_862_ = stack[2].m_num;
size_t v_i_863_ = stack[3].m_num;
lean_object* v_b_864_ = stack[4].m_obj;
lean_object* v_res_891_;
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_860_, v_as_861_, v_sz_862_, v_i_863_, v_b_864_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_892_, lean_object* v_as_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_b_896_){
_start:
{
size_t v_sz_boxed_897_; size_t v_i_boxed_898_; lean_object* v_res_899_; 
v_sz_boxed_897_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_898_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_892_, v_as_893_, v_sz_boxed_897_, v_i_boxed_898_, v_b_896_);
lean_dec_ref(v_b_896_);
lean_dec_ref(v_as_893_);
lean_dec(v_name_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_900_, lean_object* v_self_901_){
_start:
{
lean_object* v_packages_902_; lean_object* v___x_903_; lean_object* v___x_904_; size_t v_sz_905_; size_t v___x_906_; lean_object* v___x_907_; lean_object* v_fst_908_; 
v_packages_902_ = lean_ctor_get(v_self_901_, 4);
v___x_903_ = lean_box(0);
v___x_904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_905_ = lean_array_size(v_packages_902_);
v___x_906_ = ((size_t)0ULL);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_900_, v_packages_902_, v_sz_905_, v___x_906_, v___x_904_);
v_fst_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_fst_908_);
lean_dec_ref(v___x_907_);
if (lean_obj_tag(v_fst_908_) == 0)
{
return v___x_903_;
}
else
{
lean_object* v_val_909_; 
v_val_909_ = lean_ctor_get(v_fst_908_, 0);
lean_inc(v_val_909_);
lean_dec_ref_known(v_fst_908_, 1);
return v_val_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_910_, lean_object* v_self_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lake_Workspace_findExternLib_x3f(v_name_910_, v_self_911_);
lean_dec_ref(v_self_911_);
lean_dec(v_name_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_913_, lean_object* v_f_914_){
_start:
{
if (lean_obj_tag(v_a_913_) == 0)
{
lean_object* v___x_915_; 
lean_dec(v_f_914_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
else
{
lean_object* v_val_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_val_916_ = lean_ctor_get(v_a_913_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v_a_913_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v_a_913_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_val_916_);
lean_dec(v_a_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_apply_1(v_f_914_, v_val_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_a_927_, lean_object* v_f_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_927_, v_f_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_930_, lean_object* v_x_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_a_930_);
lean_ctor_set(v___x_932_, 1, v_x_931_);
return v___x_932_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_936_, lean_object* v_as_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_b_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_lt(v_i_939_, v_sz_938_);
if (v___x_941_ == 0)
{
lean_inc_ref(v_b_940_);
return v_b_940_;
}
else
{
lean_object* v___x_942_; lean_object* v_a_943_; lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_942_ = lean_box(0);
v_a_943_ = lean_array_uget_borrowed(v_as_937_, v_i_939_);
lean_inc(v_a_943_);
v___f_944_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_944_, 0, v_a_943_);
v___x_945_ = l_Lake_Package_findTargetConfig_x3f(v_name_936_, v_a_943_);
v___x_946_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_945_, v___f_944_);
if (lean_obj_tag(v___x_946_) == 1)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_942_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; size_t v___x_950_; size_t v___x_951_; 
lean_dec(v___x_946_);
v___x_949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_939_, v___x_950_);
v_i_939_ = v___x_951_;
v_b_940_ = v___x_949_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_936_ = stack[0].m_obj;
lean_object* v_as_937_ = stack[1].m_obj;
size_t v_sz_938_ = stack[2].m_num;
size_t v_i_939_ = stack[3].m_num;
lean_object* v_b_940_ = stack[4].m_obj;
lean_object* v_res_953_;
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_936_, v_as_937_, v_sz_938_, v_i_939_, v_b_940_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_954_, lean_object* v_as_955_, lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_b_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_960_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_954_, v_as_955_, v_sz_boxed_959_, v_i_boxed_960_, v_b_958_);
lean_dec_ref(v_b_958_);
lean_dec_ref(v_as_955_);
lean_dec(v_name_954_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_962_, lean_object* v_self_963_){
_start:
{
lean_object* v_packages_964_; lean_object* v___x_965_; lean_object* v___x_966_; size_t v_sz_967_; size_t v___x_968_; lean_object* v___x_969_; lean_object* v_fst_970_; 
v_packages_964_ = lean_ctor_get(v_self_963_, 4);
v___x_965_ = lean_box(0);
v___x_966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_967_ = lean_array_size(v_packages_964_);
v___x_968_ = ((size_t)0ULL);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_962_, v_packages_964_, v_sz_967_, v___x_968_, v___x_966_);
v_fst_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_fst_970_);
lean_dec_ref(v___x_969_);
if (lean_obj_tag(v_fst_970_) == 0)
{
return v___x_965_;
}
else
{
lean_object* v_val_971_; 
v_val_971_ = lean_ctor_get(v_fst_970_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v_fst_970_, 1);
return v_val_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_972_, lean_object* v_self_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_972_, v_self_973_);
lean_dec_ref(v_self_973_);
lean_dec(v_name_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_a_975_);
lean_ctor_set(v___x_977_, 1, v_x_976_);
return v___x_977_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_978_, lean_object* v_as_979_, size_t v_sz_980_, size_t v_i_981_, lean_object* v_b_982_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_981_, v_sz_980_);
if (v___x_983_ == 0)
{
lean_inc_ref(v_b_982_);
return v_b_982_;
}
else
{
lean_object* v___x_984_; lean_object* v_a_985_; lean_object* v___f_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_984_ = lean_box(0);
v_a_985_ = lean_array_uget_borrowed(v_as_979_, v_i_981_);
lean_inc(v_a_985_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_986_, 0, v_a_985_);
v___x_987_ = l_Lake_Package_findTargetDecl_x3f(v_name_978_, v_a_985_);
v___x_988_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_987_, v___f_986_);
if (lean_obj_tag(v___x_988_) == 1)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_984_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; 
lean_dec(v___x_988_);
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_981_, v___x_992_);
v_i_981_ = v___x_993_;
v_b_982_ = v___x_991_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_978_ = stack[0].m_obj;
lean_object* v_as_979_ = stack[1].m_obj;
size_t v_sz_980_ = stack[2].m_num;
size_t v_i_981_ = stack[3].m_num;
lean_object* v_b_982_ = stack[4].m_obj;
lean_object* v_res_995_;
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_978_, v_as_979_, v_sz_980_, v_i_981_, v_b_982_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_996_, lean_object* v_as_997_, lean_object* v_sz_998_, lean_object* v_i_999_, lean_object* v_b_1000_){
_start:
{
size_t v_sz_boxed_1001_; size_t v_i_boxed_1002_; lean_object* v_res_1003_; 
v_sz_boxed_1001_ = lean_unbox_usize(v_sz_998_);
lean_dec(v_sz_998_);
v_i_boxed_1002_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_996_, v_as_997_, v_sz_boxed_1001_, v_i_boxed_1002_, v_b_1000_);
lean_dec_ref(v_b_1000_);
lean_dec_ref(v_as_997_);
lean_dec(v_name_996_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_1004_, lean_object* v_self_1005_){
_start:
{
lean_object* v_packages_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; size_t v_sz_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v_fst_1012_; 
v_packages_1006_ = lean_ctor_get(v_self_1005_, 4);
v___x_1007_ = lean_box(0);
v___x_1008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_1009_ = lean_array_size(v_packages_1006_);
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_1004_, v_packages_1006_, v_sz_1009_, v___x_1010_, v___x_1008_);
v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_fst_1012_);
lean_dec_ref(v___x_1011_);
if (lean_obj_tag(v_fst_1012_) == 0)
{
return v___x_1007_;
}
else
{
lean_object* v_val_1013_; 
v_val_1013_ = lean_ctor_get(v_fst_1012_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_fst_1012_, 1);
return v_val_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_1014_, lean_object* v_self_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_1014_, v_self_1015_);
lean_dec_ref(v_self_1015_);
lean_dec(v_name_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_1017_, lean_object* v_cfg_1018_, lean_object* v_self_1019_){
_start:
{
lean_object* v_lakeEnv_1020_; lean_object* v_lakeConfig_1021_; lean_object* v_lakeCache_1022_; lean_object* v_lakeArgs_x3f_1023_; lean_object* v_packages_1024_; lean_object* v_packageMap_1025_; lean_object* v_facetConfigs_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_lakeEnv_1020_ = lean_ctor_get(v_self_1019_, 0);
v_lakeConfig_1021_ = lean_ctor_get(v_self_1019_, 1);
v_lakeCache_1022_ = lean_ctor_get(v_self_1019_, 2);
v_lakeArgs_x3f_1023_ = lean_ctor_get(v_self_1019_, 3);
v_packages_1024_ = lean_ctor_get(v_self_1019_, 4);
v_packageMap_1025_ = lean_ctor_get(v_self_1019_, 5);
v_facetConfigs_1026_ = lean_ctor_get(v_self_1019_, 6);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_self_1019_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v_self_1019_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_facetConfigs_1026_);
lean_inc(v_packageMap_1025_);
lean_inc(v_packages_1024_);
lean_inc(v_lakeArgs_x3f_1023_);
lean_inc(v_lakeCache_1022_);
lean_inc(v_lakeConfig_1021_);
lean_inc(v_lakeEnv_1020_);
lean_dec(v_self_1019_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = l_Lake_FacetConfigMap_insert(v_name_1017_, v_cfg_1018_, v_facetConfigs_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 6, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_lakeEnv_1020_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_lakeConfig_1021_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v_lakeCache_1022_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v_lakeArgs_x3f_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v_packages_1024_);
lean_ctor_set(v_reuseFailAlloc_1033_, 5, v_packageMap_1025_);
lean_ctor_set(v_reuseFailAlloc_1033_, 6, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_1035_, lean_object* v_self_1036_){
_start:
{
lean_object* v_facetConfigs_1037_; lean_object* v___x_1038_; 
v_facetConfigs_1037_ = lean_ctor_get(v_self_1036_, 6);
v___x_1038_ = l_Lake_FacetConfigMap_get_x3f(v_name_1035_, v_facetConfigs_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_1039_, lean_object* v_self_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1039_, v_self_1040_);
lean_dec_ref(v_self_1040_);
lean_dec(v_name_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_1042_, lean_object* v_cfg_1043_, lean_object* v_self_1044_){
_start:
{
lean_object* v_lakeEnv_1045_; lean_object* v_lakeConfig_1046_; lean_object* v_lakeCache_1047_; lean_object* v_lakeArgs_x3f_1048_; lean_object* v_packages_1049_; lean_object* v_packageMap_1050_; lean_object* v_facetConfigs_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_lakeEnv_1045_ = lean_ctor_get(v_self_1044_, 0);
v_lakeConfig_1046_ = lean_ctor_get(v_self_1044_, 1);
v_lakeCache_1047_ = lean_ctor_get(v_self_1044_, 2);
v_lakeArgs_x3f_1048_ = lean_ctor_get(v_self_1044_, 3);
v_packages_1049_ = lean_ctor_get(v_self_1044_, 4);
v_packageMap_1050_ = lean_ctor_get(v_self_1044_, 5);
v_facetConfigs_1051_ = lean_ctor_get(v_self_1044_, 6);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_self_1044_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v_self_1044_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_facetConfigs_1051_);
lean_inc(v_packageMap_1050_);
lean_inc(v_packages_1049_);
lean_inc(v_lakeArgs_x3f_1048_);
lean_inc(v_lakeCache_1047_);
lean_inc(v_lakeConfig_1046_);
lean_inc(v_lakeEnv_1045_);
lean_dec(v_self_1044_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = l_Lake_FacetConfigMap_insert(v_name_1042_, v_cfg_1043_, v_facetConfigs_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 6, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_lakeEnv_1045_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_lakeConfig_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_lakeCache_1047_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_lakeArgs_x3f_1048_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_packages_1049_);
lean_ctor_set(v_reuseFailAlloc_1058_, 5, v_packageMap_1050_);
lean_ctor_set(v_reuseFailAlloc_1058_, 6, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_1060_, lean_object* v_self_1061_){
_start:
{
lean_object* v_facetConfigs_1062_; lean_object* v___x_1063_; 
v_facetConfigs_1062_ = lean_ctor_get(v_self_1061_, 6);
v___x_1063_ = l_Lake_FacetConfigMap_get_x3f(v_name_1060_, v_facetConfigs_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(0);
return v___x_1064_;
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_val_1065_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1066_ = l_Lake_Module_keyword;
v___x_1067_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1066_, v_val_1065_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1068_, lean_object* v_self_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1068_, v_self_1069_);
lean_dec_ref(v_self_1069_);
lean_dec(v_name_1068_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1071_, lean_object* v_cfg_1072_, lean_object* v_self_1073_){
_start:
{
lean_object* v_lakeEnv_1074_; lean_object* v_lakeConfig_1075_; lean_object* v_lakeCache_1076_; lean_object* v_lakeArgs_x3f_1077_; lean_object* v_packages_1078_; lean_object* v_packageMap_1079_; lean_object* v_facetConfigs_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1088_; 
v_lakeEnv_1074_ = lean_ctor_get(v_self_1073_, 0);
v_lakeConfig_1075_ = lean_ctor_get(v_self_1073_, 1);
v_lakeCache_1076_ = lean_ctor_get(v_self_1073_, 2);
v_lakeArgs_x3f_1077_ = lean_ctor_get(v_self_1073_, 3);
v_packages_1078_ = lean_ctor_get(v_self_1073_, 4);
v_packageMap_1079_ = lean_ctor_get(v_self_1073_, 5);
v_facetConfigs_1080_ = lean_ctor_get(v_self_1073_, 6);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_self_1073_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1082_ = v_self_1073_;
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_facetConfigs_1080_);
lean_inc(v_packageMap_1079_);
lean_inc(v_packages_1078_);
lean_inc(v_lakeArgs_x3f_1077_);
lean_inc(v_lakeCache_1076_);
lean_inc(v_lakeConfig_1075_);
lean_inc(v_lakeEnv_1074_);
lean_dec(v_self_1073_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = l_Lake_FacetConfigMap_insert(v_name_1071_, v_cfg_1072_, v_facetConfigs_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 6, v___x_1084_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_lakeEnv_1074_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_lakeConfig_1075_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_lakeCache_1076_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_lakeArgs_x3f_1077_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_packages_1078_);
lean_ctor_set(v_reuseFailAlloc_1087_, 5, v_packageMap_1079_);
lean_ctor_set(v_reuseFailAlloc_1087_, 6, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1089_, lean_object* v_self_1090_){
_start:
{
lean_object* v_facetConfigs_1091_; lean_object* v___x_1092_; 
v_facetConfigs_1091_ = lean_ctor_get(v_self_1090_, 6);
v___x_1092_ = l_Lake_FacetConfigMap_get_x3f(v_name_1089_, v_facetConfigs_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
else
{
lean_object* v_val_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_val_1094_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1094_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1095_ = l_Lake_Package_keyword;
v___x_1096_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1095_, v_val_1094_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1097_, lean_object* v_self_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1097_, v_self_1098_);
lean_dec_ref(v_self_1098_);
lean_dec(v_name_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1100_, lean_object* v_cfg_1101_, lean_object* v_self_1102_){
_start:
{
lean_object* v_lakeEnv_1103_; lean_object* v_lakeConfig_1104_; lean_object* v_lakeCache_1105_; lean_object* v_lakeArgs_x3f_1106_; lean_object* v_packages_1107_; lean_object* v_packageMap_1108_; lean_object* v_facetConfigs_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1117_; 
v_lakeEnv_1103_ = lean_ctor_get(v_self_1102_, 0);
v_lakeConfig_1104_ = lean_ctor_get(v_self_1102_, 1);
v_lakeCache_1105_ = lean_ctor_get(v_self_1102_, 2);
v_lakeArgs_x3f_1106_ = lean_ctor_get(v_self_1102_, 3);
v_packages_1107_ = lean_ctor_get(v_self_1102_, 4);
v_packageMap_1108_ = lean_ctor_get(v_self_1102_, 5);
v_facetConfigs_1109_ = lean_ctor_get(v_self_1102_, 6);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_self_1102_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1111_ = v_self_1102_;
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_facetConfigs_1109_);
lean_inc(v_packageMap_1108_);
lean_inc(v_packages_1107_);
lean_inc(v_lakeArgs_x3f_1106_);
lean_inc(v_lakeCache_1105_);
lean_inc(v_lakeConfig_1104_);
lean_inc(v_lakeEnv_1103_);
lean_dec(v_self_1102_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1117_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = l_Lake_FacetConfigMap_insert(v_name_1100_, v_cfg_1101_, v_facetConfigs_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 6, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_lakeEnv_1103_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_lakeConfig_1104_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_lakeCache_1105_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_lakeArgs_x3f_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_packages_1107_);
lean_ctor_set(v_reuseFailAlloc_1116_, 5, v_packageMap_1108_);
lean_ctor_set(v_reuseFailAlloc_1116_, 6, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1118_, lean_object* v_self_1119_){
_start:
{
lean_object* v_facetConfigs_1120_; lean_object* v___x_1121_; 
v_facetConfigs_1120_ = lean_ctor_get(v_self_1119_, 6);
v___x_1121_ = l_Lake_FacetConfigMap_get_x3f(v_name_1118_, v_facetConfigs_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_box(0);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_val_1123_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_val_1123_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1125_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1124_, v_val_1123_);
return v___x_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1126_, lean_object* v_self_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1126_, v_self_1127_);
lean_dec_ref(v_self_1127_);
lean_dec(v_name_1126_);
return v_res_1128_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1129_, size_t v_i_1130_, size_t v_stop_1131_, lean_object* v_b_1132_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_usize_dec_eq(v_i_1130_, v_stop_1131_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v_config_1135_; lean_object* v_dir_1136_; lean_object* v_buildDir_1137_; lean_object* v_binDir_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; 
v___x_1134_ = lean_array_uget_borrowed(v_as_1129_, v_i_1130_);
v_config_1135_ = lean_ctor_get(v___x_1134_, 6);
v_dir_1136_ = lean_ctor_get(v___x_1134_, 4);
v_buildDir_1137_ = lean_ctor_get(v_config_1135_, 5);
v_binDir_1138_ = lean_ctor_get(v_config_1135_, 8);
lean_inc_ref(v_buildDir_1137_);
v___x_1139_ = l_System_FilePath_normalize(v_buildDir_1137_);
lean_inc_ref(v_dir_1136_);
v___x_1140_ = l_Lake_joinRelative(v_dir_1136_, v___x_1139_);
lean_inc_ref(v_binDir_1138_);
v___x_1141_ = l_System_FilePath_normalize(v_binDir_1138_);
v___x_1142_ = l_Lake_joinRelative(v___x_1140_, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_b_1132_);
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1130_, v___x_1144_);
v_i_1130_ = v___x_1145_;
v_b_1132_ = v___x_1143_;
goto _start;
}
else
{
return v_b_1132_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1129_ = stack[0].m_obj;
size_t v_i_1130_ = stack[1].m_num;
size_t v_stop_1131_ = stack[2].m_num;
lean_object* v_b_1132_ = stack[3].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1129_, v_i_1130_, v_stop_1131_, v_b_1132_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1148_, lean_object* v_i_1149_, lean_object* v_stop_1150_, lean_object* v_b_1151_){
_start:
{
size_t v_i_boxed_1152_; size_t v_stop_boxed_1153_; lean_object* v_res_1154_; 
v_i_boxed_1152_ = lean_unbox_usize(v_i_1149_);
lean_dec(v_i_1149_);
v_stop_boxed_1153_ = lean_unbox_usize(v_stop_1150_);
lean_dec(v_stop_1150_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1148_, v_i_boxed_1152_, v_stop_boxed_1153_, v_b_1151_);
lean_dec_ref(v_as_1148_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1155_){
_start:
{
lean_object* v_packages_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_packages_1156_ = lean_ctor_get(v_self_1155_, 4);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = lean_array_get_size(v_packages_1156_);
v___x_1160_ = lean_nat_dec_lt(v___x_1158_, v___x_1159_);
if (v___x_1160_ == 0)
{
return v___x_1157_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_le(v___x_1159_, v___x_1159_);
if (v___x_1161_ == 0)
{
if (v___x_1160_ == 0)
{
return v___x_1157_;
}
else
{
size_t v___x_1162_; size_t v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = ((size_t)0ULL);
v___x_1163_ = lean_usize_of_nat(v___x_1159_);
v___x_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1156_, v___x_1162_, v___x_1163_, v___x_1157_);
return v___x_1164_;
}
}
else
{
size_t v___x_1165_; size_t v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = lean_usize_of_nat(v___x_1159_);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1156_, v___x_1165_, v___x_1166_, v___x_1157_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lake_Workspace_binPath(v_self_1168_);
lean_dec_ref(v_self_1168_);
return v_res_1169_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1170_, size_t v_i_1171_, size_t v_stop_1172_, lean_object* v_b_1173_){
_start:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_usize_dec_eq(v_i_1171_, v_stop_1172_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v_config_1176_; lean_object* v_dir_1177_; lean_object* v_buildDir_1178_; lean_object* v_leanLibDir_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; 
v___x_1175_ = lean_array_uget_borrowed(v_as_1170_, v_i_1171_);
v_config_1176_ = lean_ctor_get(v___x_1175_, 6);
v_dir_1177_ = lean_ctor_get(v___x_1175_, 4);
v_buildDir_1178_ = lean_ctor_get(v_config_1176_, 5);
v_leanLibDir_1179_ = lean_ctor_get(v_config_1176_, 6);
lean_inc_ref(v_buildDir_1178_);
v___x_1180_ = l_System_FilePath_normalize(v_buildDir_1178_);
lean_inc_ref(v_dir_1177_);
v___x_1181_ = l_Lake_joinRelative(v_dir_1177_, v___x_1180_);
lean_inc_ref(v_leanLibDir_1179_);
v___x_1182_ = l_System_FilePath_normalize(v_leanLibDir_1179_);
v___x_1183_ = l_Lake_joinRelative(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_b_1173_);
v___x_1185_ = ((size_t)1ULL);
v___x_1186_ = lean_usize_add(v_i_1171_, v___x_1185_);
v_i_1171_ = v___x_1186_;
v_b_1173_ = v___x_1184_;
goto _start;
}
else
{
return v_b_1173_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1170_ = stack[0].m_obj;
size_t v_i_1171_ = stack[1].m_num;
size_t v_stop_1172_ = stack[2].m_num;
lean_object* v_b_1173_ = stack[3].m_obj;
lean_object* v_res_1188_;
v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1170_, v_i_1171_, v_stop_1172_, v_b_1173_);
stack->m_obj
 = v_res_1188_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1189_, lean_object* v_i_1190_, lean_object* v_stop_1191_, lean_object* v_b_1192_){
_start:
{
size_t v_i_boxed_1193_; size_t v_stop_boxed_1194_; lean_object* v_res_1195_; 
v_i_boxed_1193_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_stop_boxed_1194_ = lean_unbox_usize(v_stop_1191_);
lean_dec(v_stop_1191_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1189_, v_i_boxed_1193_, v_stop_boxed_1194_, v_b_1192_);
lean_dec_ref(v_as_1189_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1196_){
_start:
{
lean_object* v_packages_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_packages_1197_ = lean_ctor_get(v_self_1196_, 4);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = lean_array_get_size(v_packages_1197_);
v___x_1201_ = lean_nat_dec_lt(v___x_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
return v___x_1198_;
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = lean_nat_dec_le(v___x_1200_, v___x_1200_);
if (v___x_1202_ == 0)
{
if (v___x_1201_ == 0)
{
return v___x_1198_;
}
else
{
size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = ((size_t)0ULL);
v___x_1204_ = lean_usize_of_nat(v___x_1200_);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1197_, v___x_1203_, v___x_1204_, v___x_1198_);
return v___x_1205_;
}
}
else
{
size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = lean_usize_of_nat(v___x_1200_);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1197_, v___x_1206_, v___x_1207_, v___x_1198_);
return v___x_1208_;
}
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1211_, lean_object* v_as_1212_, size_t v_i_1213_, size_t v_stop_1214_, lean_object* v_b_1215_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x2_1211_ = stack[0].m_obj;
lean_object* v_as_1212_ = stack[1].m_obj;
size_t v_i_1213_ = stack[2].m_num;
size_t v_stop_1214_ = stack[3].m_num;
lean_object* v_b_1215_ = stack[4].m_obj;
lean_object* v_res_1234_;
v_res_1234_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1211_, v_as_1212_, v_i_1213_, v_stop_1214_, v_b_1215_);
stack->m_obj
 = v_res_1234_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1235_, lean_object* v_as_1236_, lean_object* v_i_1237_, lean_object* v_stop_1238_, lean_object* v_b_1239_){
_start:
{
size_t v_i_boxed_1240_; size_t v_stop_boxed_1241_; lean_object* v_res_1242_; 
v_i_boxed_1240_ = lean_unbox_usize(v_i_1237_);
lean_dec(v_i_1237_);
v_stop_boxed_1241_ = lean_unbox_usize(v_stop_1238_);
lean_dec(v_stop_1238_);
v_res_1242_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1235_, v_as_1236_, v_i_boxed_1240_, v_stop_boxed_1241_, v_b_1239_);
lean_dec_ref(v_as_1236_);
return v_res_1242_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1243_, size_t v_i_1244_, size_t v_stop_1245_, lean_object* v_b_1246_){
_start:
{
lean_object* v___y_1248_; uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_eq(v_i_1244_, v_stop_1245_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v_targetDecls_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1253_ = lean_array_uget_borrowed(v_as_1243_, v_i_1244_);
v_targetDecls_1254_ = lean_ctor_get(v___x_1253_, 15);
v___x_1255_ = lean_array_get_size(v_targetDecls_1254_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_nat_dec_lt(v___x_1256_, v___x_1255_);
if (v___x_1257_ == 0)
{
v___y_1248_ = v_b_1246_;
goto v___jp_1247_;
}
else
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_usize_of_nat(v___x_1255_);
v___x_1259_ = ((size_t)0ULL);
lean_inc(v___x_1253_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1253_, v_targetDecls_1254_, v___x_1258_, v___x_1259_, v_b_1246_);
v___y_1248_ = v___x_1260_;
goto v___jp_1247_;
}
}
else
{
return v_b_1246_;
}
v___jp_1247_:
{
size_t v___x_1249_; size_t v___x_1250_; 
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_add(v_i_1244_, v___x_1249_);
v_i_1244_ = v___x_1250_;
v_b_1246_ = v___y_1248_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1243_ = stack[0].m_obj;
size_t v_i_1244_ = stack[1].m_num;
size_t v_stop_1245_ = stack[2].m_num;
lean_object* v_b_1246_ = stack[3].m_obj;
lean_object* v_res_1261_;
v_res_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1243_, v_i_1244_, v_stop_1245_, v_b_1246_);
stack->m_obj
 = v_res_1261_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1262_, lean_object* v_i_1263_, lean_object* v_stop_1264_, lean_object* v_b_1265_){
_start:
{
size_t v_i_boxed_1266_; size_t v_stop_boxed_1267_; lean_object* v_res_1268_; 
v_i_boxed_1266_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_stop_boxed_1267_ = lean_unbox_usize(v_stop_1264_);
lean_dec(v_stop_1264_);
v_res_1268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1262_, v_i_boxed_1266_, v_stop_boxed_1267_, v_b_1265_);
lean_dec_ref(v_as_1262_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1269_){
_start:
{
lean_object* v_packages_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v_packages_1270_ = lean_ctor_get(v_self_1269_, 4);
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_array_get_size(v_packages_1270_);
v___x_1274_ = lean_nat_dec_lt(v___x_1272_, v___x_1273_);
if (v___x_1274_ == 0)
{
return v___x_1271_;
}
else
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_nat_dec_le(v___x_1273_, v___x_1273_);
if (v___x_1275_ == 0)
{
if (v___x_1274_ == 0)
{
return v___x_1271_;
}
else
{
size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((size_t)0ULL);
v___x_1277_ = lean_usize_of_nat(v___x_1273_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1270_, v___x_1276_, v___x_1277_, v___x_1271_);
return v___x_1278_;
}
}
else
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = lean_usize_of_nat(v___x_1273_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1270_, v___x_1279_, v___x_1280_, v___x_1271_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lake_Workspace_leanSrcPath(v_self_1282_);
lean_dec_ref(v_self_1282_);
return v_res_1283_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1284_, size_t v_i_1285_, size_t v_stop_1286_, lean_object* v_b_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_usize_dec_eq(v_i_1285_, v_stop_1286_);
if (v___x_1288_ == 0)
{
size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; lean_object* v_config_1292_; lean_object* v_dir_1293_; lean_object* v_buildDir_1294_; lean_object* v_nativeLibDir_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_sub(v_i_1285_, v___x_1289_);
v___x_1291_ = lean_array_uget_borrowed(v_as_1284_, v___x_1290_);
v_config_1292_ = lean_ctor_get(v___x_1291_, 6);
v_dir_1293_ = lean_ctor_get(v___x_1291_, 4);
v_buildDir_1294_ = lean_ctor_get(v_config_1292_, 5);
v_nativeLibDir_1295_ = lean_ctor_get(v_config_1292_, 7);
lean_inc_ref(v_buildDir_1294_);
v___x_1296_ = l_System_FilePath_normalize(v_buildDir_1294_);
lean_inc_ref(v_dir_1293_);
v___x_1297_ = l_Lake_joinRelative(v_dir_1293_, v___x_1296_);
lean_inc_ref(v_nativeLibDir_1295_);
v___x_1298_ = l_System_FilePath_normalize(v_nativeLibDir_1295_);
v___x_1299_ = l_Lake_joinRelative(v___x_1297_, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v_b_1287_);
v_i_1285_ = v___x_1290_;
v_b_1287_ = v___x_1300_;
goto _start;
}
else
{
return v_b_1287_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1284_ = stack[0].m_obj;
size_t v_i_1285_ = stack[1].m_num;
size_t v_stop_1286_ = stack[2].m_num;
lean_object* v_b_1287_ = stack[3].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1284_, v_i_1285_, v_stop_1286_, v_b_1287_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1303_, lean_object* v_i_1304_, lean_object* v_stop_1305_, lean_object* v_b_1306_){
_start:
{
size_t v_i_boxed_1307_; size_t v_stop_boxed_1308_; lean_object* v_res_1309_; 
v_i_boxed_1307_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_stop_boxed_1308_ = lean_unbox_usize(v_stop_1305_);
lean_dec(v_stop_1305_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1303_, v_i_boxed_1307_, v_stop_boxed_1308_, v_b_1306_);
lean_dec_ref(v_as_1303_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1310_){
_start:
{
lean_object* v_packages_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_packages_1311_ = lean_ctor_get(v_self_1310_, 4);
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_array_get_size(v_packages_1311_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_nat_dec_lt(v___x_1314_, v___x_1313_);
if (v___x_1315_ == 0)
{
return v___x_1312_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_usize_of_nat(v___x_1313_);
v___x_1317_ = ((size_t)0ULL);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1311_, v___x_1316_, v___x_1317_, v___x_1312_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lake_Workspace_sharedLibPath(v_self_1319_);
lean_dec_ref(v_self_1319_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_System_Platform_isWindows;
if (v___x_1322_ == 0)
{
lean_object* v_lakeEnv_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_lakeEnv_1323_ = lean_ctor_get(v_self_1321_, 0);
v___x_1324_ = l_Lake_Workspace_binPath(v_self_1321_);
v___x_1325_ = l_Lake_Env_path(v_lakeEnv_1323_);
v___x_1326_ = l_List_appendTR___redArg(v___x_1324_, v___x_1325_);
return v___x_1326_;
}
else
{
lean_object* v_lakeEnv_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_lakeEnv_1327_ = lean_ctor_get(v_self_1321_, 0);
v___x_1328_ = l_Lake_Workspace_binPath(v_self_1321_);
v___x_1329_ = l_Lake_Workspace_sharedLibPath(v_self_1321_);
v___x_1330_ = l_List_appendTR___redArg(v___x_1328_, v___x_1329_);
v___x_1331_ = l_Lake_Env_path(v_lakeEnv_1327_);
v___x_1332_ = l_List_appendTR___redArg(v___x_1330_, v___x_1331_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lake_Workspace_augmentedPath(v_self_1333_);
lean_dec_ref(v_self_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1335_){
_start:
{
lean_object* v_lakeEnv_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_lakeEnv_1336_ = lean_ctor_get(v_self_1335_, 0);
v___x_1337_ = l_Lake_Workspace_leanPath(v_self_1335_);
v___x_1338_ = l_Lake_Env_leanPath(v_lakeEnv_1336_);
v___x_1339_ = l_List_appendTR___redArg(v___x_1337_, v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lake_Workspace_augmentedLeanPath(v_self_1340_);
lean_dec_ref(v_self_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1342_){
_start:
{
lean_object* v_lakeEnv_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_lakeEnv_1343_ = lean_ctor_get(v_self_1342_, 0);
v___x_1344_ = l_Lake_Workspace_leanSrcPath(v_self_1342_);
v___x_1345_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1343_);
v___x_1346_ = l_List_appendTR___redArg(v___x_1344_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1347_);
lean_dec_ref(v_self_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1349_){
_start:
{
lean_object* v_lakeEnv_1350_; lean_object* v_lean_1351_; lean_object* v_initSharedLibPath_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v_lakeEnv_1350_ = lean_ctor_get(v_self_1349_, 0);
v_lean_1351_ = lean_ctor_get(v_lakeEnv_1350_, 1);
v_initSharedLibPath_1352_ = lean_ctor_get(v_lakeEnv_1350_, 17);
lean_inc(v_initSharedLibPath_1352_);
v___x_1353_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1351_);
v___x_1354_ = l_Lake_Workspace_sharedLibPath(v_self_1349_);
lean_dec_ref(v_self_1349_);
v___x_1355_ = l_List_appendTR___redArg(v___x_1353_, v___x_1354_);
v___x_1356_ = l_List_appendTR___redArg(v___x_1355_, v_initSharedLibPath_1352_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0(lean_object* v_x_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__0___closed__1));
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__0___boxed(lean_object* v_x_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_x_1362_);
lean_dec(v_x_1362_);
return v_res_1363_;
}
}
lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1(uint8_t v_b_1370_){
_start:
{
if (v_b_1370_ == 0)
{
lean_object* v___x_1371_; 
v___x_1371_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__1));
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___lam__1___closed__3));
return v___x_1372_;
}
}
}
LEAN_EXPORT void l_Lake_Workspace_augmentedEnvVars___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1370_ = stack[0].m_num;
lean_object* v_res_1373_;
v_res_1373_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_b_1370_);
stack->m_obj
 = v_res_1373_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars___lam__1___boxed(lean_object* v_b_1374_){
_start:
{
uint8_t v_b_boxed_1375_; lean_object* v_res_1376_; 
v_b_boxed_1375_ = lean_unbox(v_b_1374_);
v_res_1376_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_b_boxed_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1384_){
_start:
{
lean_object* v_lakeEnv_1385_; lean_object* v_lakeCache_1386_; lean_object* v_packages_1387_; lean_object* v_enableArtifactCache_x3f_1388_; lean_object* v_restoreAllArtifacts_x3f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1448_; lean_object* v___y_1449_; uint8_t v_val_1450_; lean_object* v___x_1452_; lean_object* v___y_1454_; uint8_t v_val_1467_; 
v_lakeEnv_1385_ = lean_ctor_get(v_self_1384_, 0);
v_lakeCache_1386_ = lean_ctor_get(v_self_1384_, 2);
v_packages_1387_ = lean_ctor_get(v_self_1384_, 4);
v_enableArtifactCache_x3f_1388_ = lean_ctor_get(v_lakeEnv_1385_, 6);
v_restoreAllArtifacts_x3f_1389_ = lean_ctor_get(v_lakeEnv_1385_, 7);
lean_inc_ref(v_lakeEnv_1385_);
v___x_1390_ = l_Lake_Env_baseVars(v_lakeEnv_1385_);
v___x_1391_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1386_);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_lakeCache_1386_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1452_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (lean_obj_tag(v_enableArtifactCache_x3f_1388_) == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_config_1471_; lean_object* v_enableArtifactCache_x3f_1472_; 
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = lean_array_fget_borrowed(v_packages_1387_, v___x_1469_);
v_config_1471_ = lean_ctor_get(v___x_1470_, 6);
v_enableArtifactCache_x3f_1472_ = lean_ctor_get(v_config_1471_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1472_) == 1)
{
lean_object* v_val_1473_; uint8_t v___x_1474_; 
v_val_1473_ = lean_ctor_get(v_enableArtifactCache_x3f_1472_, 0);
v___x_1474_ = lean_unbox(v_val_1473_);
v_val_1467_ = v___x_1474_;
goto v___jp_1466_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_enableArtifactCache_x3f_1472_);
v___y_1454_ = v___x_1475_;
goto v___jp_1453_;
}
}
else
{
lean_object* v_val_1476_; uint8_t v___x_1477_; 
v_val_1476_ = lean_ctor_get(v_enableArtifactCache_x3f_1388_, 0);
v___x_1477_ = lean_unbox(v_val_1476_);
v_val_1467_ = v___x_1477_;
goto v___jp_1466_;
}
v___jp_1394_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_vars_1416_; uint8_t v___x_1417_; 
lean_inc_ref(v___y_1398_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___y_1398_);
lean_ctor_set(v___x_1401_, 1, v___y_1400_);
v___x_1402_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1403_ = l_Lake_Workspace_augmentedPath(v_self_1384_);
v___x_1404_ = l_System_SearchPath_toString(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1402_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = lean_unsigned_to_nat(7u);
v___x_1408_ = lean_mk_empty_array_with_capacity(v___x_1407_);
v___x_1409_ = lean_array_push(v___x_1408_, v___x_1393_);
v___x_1410_ = lean_array_push(v___x_1409_, v___y_1396_);
v___x_1411_ = lean_array_push(v___x_1410_, v___y_1399_);
v___x_1412_ = lean_array_push(v___x_1411_, v___y_1397_);
v___x_1413_ = lean_array_push(v___x_1412_, v___y_1395_);
v___x_1414_ = lean_array_push(v___x_1413_, v___x_1401_);
v___x_1415_ = lean_array_push(v___x_1414_, v___x_1406_);
v_vars_1416_ = l_Array_append___redArg(v___x_1390_, v___x_1415_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = l_System_Platform_isWindows;
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1418_ = l_Lake_sharedLibPathEnvVar;
v___x_1419_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1384_);
v___x_1420_ = l_System_SearchPath_toString(v___x_1419_);
v___x_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1418_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = lean_array_push(v_vars_1416_, v___x_1422_);
return v___x_1423_;
}
else
{
lean_dec_ref(v_self_1384_);
return v_vars_1416_;
}
}
v___jp_1424_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_config_1430_; uint8_t v_bootstrap_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_array_fget_borrowed(v_packages_1387_, v___x_1428_);
v_config_1430_ = lean_ctor_get(v___x_1429_, 6);
v_bootstrap_1431_ = lean_ctor_get_uint8(v_config_1430_, sizeof(void*)*28);
lean_inc_ref(v___y_1425_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___y_1425_);
lean_ctor_set(v___x_1432_, 1, v___y_1427_);
v___x_1433_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
v___x_1434_ = l_Lake_Workspace_augmentedLeanPath(v_self_1384_);
v___x_1435_ = l_System_SearchPath_toString(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1433_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1439_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1384_);
v___x_1440_ = l_System_SearchPath_toString(v___x_1439_);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1438_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
if (v_bootstrap_1431_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = l_Lake_Env_leanGithash(v_lakeEnv_1385_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
v___y_1395_ = v___x_1442_;
v___y_1396_ = v___y_1426_;
v___y_1397_ = v___x_1437_;
v___y_1398_ = v___x_1443_;
v___y_1399_ = v___x_1432_;
v___y_1400_ = v___x_1445_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_box(0);
v___y_1395_ = v___x_1442_;
v___y_1396_ = v___y_1426_;
v___y_1397_ = v___x_1437_;
v___y_1398_ = v___x_1443_;
v___y_1399_ = v___x_1432_;
v___y_1400_ = v___x_1446_;
goto v___jp_1394_;
}
}
v___jp_1447_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1450_);
v___y_1425_ = v___y_1448_;
v___y_1426_ = v___y_1449_;
v___y_1427_ = v___x_1451_;
goto v___jp_1424_;
}
v___jp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1452_);
lean_ctor_set(v___x_1455_, 1, v___y_1454_);
v___x_1456_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__6));
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1389_) == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_config_1459_; lean_object* v_restoreAllArtifacts_x3f_1460_; 
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_array_fget_borrowed(v_packages_1387_, v___x_1457_);
v_config_1459_ = lean_ctor_get(v___x_1458_, 6);
v_restoreAllArtifacts_x3f_1460_ = lean_ctor_get(v_config_1459_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_1460_) == 1)
{
lean_object* v_val_1461_; uint8_t v___x_1462_; 
v_val_1461_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1460_, 0);
v___x_1462_ = lean_unbox(v_val_1461_);
v___y_1448_ = v___x_1456_;
v___y_1449_ = v___x_1455_;
v_val_1450_ = v___x_1462_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lake_Workspace_augmentedEnvVars___lam__0(v_restoreAllArtifacts_x3f_1460_);
v___y_1425_ = v___x_1456_;
v___y_1426_ = v___x_1455_;
v___y_1427_ = v___x_1463_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_val_1464_; uint8_t v___x_1465_; 
v_val_1464_ = lean_ctor_get(v_restoreAllArtifacts_x3f_1389_, 0);
v___x_1465_ = lean_unbox(v_val_1464_);
v___y_1448_ = v___x_1456_;
v___y_1449_ = v___x_1455_;
v_val_1450_ = v___x_1465_;
goto v___jp_1447_;
}
}
v___jp_1466_:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lake_Workspace_augmentedEnvVars___lam__1(v_val_1467_);
v___y_1454_ = v___x_1468_;
goto v___jp_1453_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1478_, size_t v_i_1479_, size_t v_stop_1480_, lean_object* v_b_1481_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_usize_dec_eq(v_i_1479_, v_stop_1480_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_array_uget_borrowed(v_as_1478_, v_i_1479_);
lean_inc(v___x_1484_);
v___x_1485_ = l_Lake_Package_clean(v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; size_t v___x_1487_; size_t v___x_1488_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1479_, v___x_1487_);
v_i_1479_ = v___x_1488_;
v_b_1481_ = v_a_1486_;
goto _start;
}
else
{
return v___x_1485_;
}
}
else
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_b_1481_);
return v___x_1490_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1478_ = stack[0].m_obj;
size_t v_i_1479_ = stack[1].m_num;
size_t v_stop_1480_ = stack[2].m_num;
lean_object* v_b_1481_ = stack[3].m_obj;
lean_object* v_res_1491_;
v_res_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1478_, v_i_1479_, v_stop_1480_, v_b_1481_);
stack->m_obj
 = v_res_1491_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1492_, lean_object* v_i_1493_, lean_object* v_stop_1494_, lean_object* v_b_1495_, lean_object* v___y_1496_){
_start:
{
size_t v_i_boxed_1497_; size_t v_stop_boxed_1498_; lean_object* v_res_1499_; 
v_i_boxed_1497_ = lean_unbox_usize(v_i_1493_);
lean_dec(v_i_1493_);
v_stop_boxed_1498_ = lean_unbox_usize(v_stop_1494_);
lean_dec(v_stop_1494_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1492_, v_i_boxed_1497_, v_stop_boxed_1498_, v_b_1495_);
lean_dec_ref(v_as_1492_);
return v_res_1499_;
}
}
lean_object* l_Lake_Workspace_clean(lean_object* v_self_1500_){
_start:
{
lean_object* v_packages_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_packages_1502_ = lean_ctor_get(v_self_1500_, 4);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_array_get_size(v_packages_1502_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_nat_dec_lt(v___x_1503_, v___x_1504_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
return v___x_1507_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_nat_dec_le(v___x_1504_, v___x_1504_);
if (v___x_1508_ == 0)
{
if (v___x_1506_ == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1505_);
return v___x_1509_;
}
else
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = lean_usize_of_nat(v___x_1504_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1502_, v___x_1510_, v___x_1511_, v___x_1505_);
return v___x_1512_;
}
}
else
{
size_t v___x_1513_; size_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = lean_usize_of_nat(v___x_1504_);
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1502_, v___x_1513_, v___x_1514_, v___x_1505_);
return v___x_1515_;
}
}
}
}
LEAN_EXPORT void l_Lake_Workspace_clean_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1500_ = stack[0].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l_Lake_Workspace_clean(v_self_1500_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lake_Workspace_clean(v_self_1517_);
lean_dec_ref(v_self_1517_);
return v_res_1519_;
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

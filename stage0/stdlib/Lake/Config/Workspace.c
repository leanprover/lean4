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
v_bootstrap_5_ = lean_ctor_get_uint8(v_config_4_, sizeof(void*)*27);
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
lean_dec_ref(v___x_68_);
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
lean_dec_ref(v___x_57_);
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
v_defaultTargets_87_ = lean_ctor_get(v_self_86_, 16);
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
lean_object* v_packages_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_config_195_; lean_object* v_restoreAllArtifacts_x3f_196_; 
v_packages_192_ = lean_ctor_get(v_ws_191_, 4);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_array_fget_borrowed(v_packages_192_, v___x_193_);
v_config_195_ = lean_ctor_get(v___x_194_, 6);
v_restoreAllArtifacts_x3f_196_ = lean_ctor_get(v_config_195_, 25);
lean_inc(v_restoreAllArtifacts_x3f_196_);
return v_restoreAllArtifacts_x3f_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(lean_object* v_ws_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lake_Workspace_restoreAllArtifacts_x3f(v_ws_197_);
lean_dec_ref(v_ws_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain(lean_object* v_ws_199_){
_start:
{
lean_object* v_lakeEnv_200_; lean_object* v_toolchain_201_; 
v_lakeEnv_200_ = lean_ctor_get(v_ws_199_, 0);
v_toolchain_201_ = lean_ctor_get(v_lakeEnv_200_, 18);
lean_inc_ref(v_toolchain_201_);
return v_toolchain_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_cacheToolchain___boxed(lean_object* v_ws_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lake_Workspace_cacheToolchain(v_ws_202_);
lean_dec_ref(v_ws_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService(lean_object* v_ws_204_){
_start:
{
lean_object* v_lakeConfig_205_; lean_object* v_defaultCacheService_206_; 
v_lakeConfig_205_ = lean_ctor_get(v_ws_204_, 1);
v_defaultCacheService_206_ = lean_ctor_get(v_lakeConfig_205_, 1);
lean_inc_ref(v_defaultCacheService_206_);
return v_defaultCacheService_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheService___boxed(lean_object* v_ws_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lake_Workspace_defaultCacheService(v_ws_207_);
lean_dec_ref(v_ws_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f(lean_object* v_ws_209_){
_start:
{
lean_object* v_lakeConfig_210_; lean_object* v_defaultCacheUploadService_x3f_211_; 
v_lakeConfig_210_ = lean_ctor_get(v_ws_209_, 1);
v_defaultCacheUploadService_x3f_211_ = lean_ctor_get(v_lakeConfig_210_, 2);
lean_inc(v_defaultCacheUploadService_x3f_211_);
return v_defaultCacheUploadService_x3f_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(lean_object* v_ws_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lake_Workspace_defaultCacheUploadService_x3f(v_ws_212_);
lean_dec_ref(v_ws_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f(lean_object* v_ws_214_, lean_object* v_service_215_){
_start:
{
lean_object* v_lakeConfig_216_; lean_object* v_cacheServices_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_lakeConfig_216_ = lean_ctor_get(v_ws_214_, 1);
v_cacheServices_217_ = lean_ctor_get(v_lakeConfig_216_, 3);
v___x_218_ = lean_box(0);
v___x_219_ = l_Lean_Name_str___override(v___x_218_, v_service_215_);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_217_, v___x_219_);
lean_dec(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findCacheService_x3f___boxed(lean_object* v_ws_221_, lean_object* v_service_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lake_Workspace_findCacheService_x3f(v_ws_221_, v_service_222_);
lean_dec_ref(v_ws_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* v_self_224_){
_start:
{
lean_object* v_packages_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_config_228_; lean_object* v_toWorkspaceConfig_229_; lean_object* v___x_230_; 
v_packages_225_ = lean_ctor_get(v_self_224_, 4);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_array_fget_borrowed(v_packages_225_, v___x_226_);
v_config_228_ = lean_ctor_get(v___x_227_, 6);
v_toWorkspaceConfig_229_ = lean_ctor_get(v_config_228_, 0);
lean_inc_ref(v_toWorkspaceConfig_229_);
v___x_230_ = l_System_FilePath_normalize(v_toWorkspaceConfig_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir___boxed(lean_object* v_self_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_Workspace_relPkgsDir(v_self_231_);
lean_dec_ref(v_self_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* v_self_233_){
_start:
{
lean_object* v_packages_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_config_237_; lean_object* v_dir_238_; lean_object* v_toWorkspaceConfig_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_packages_234_ = lean_ctor_get(v_self_233_, 4);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_array_fget_borrowed(v_packages_234_, v___x_235_);
v_config_237_ = lean_ctor_get(v___x_236_, 6);
v_dir_238_ = lean_ctor_get(v___x_236_, 4);
v_toWorkspaceConfig_239_ = lean_ctor_get(v_config_237_, 0);
lean_inc_ref(v_toWorkspaceConfig_239_);
v___x_240_ = l_System_FilePath_normalize(v_toWorkspaceConfig_239_);
lean_inc_ref(v_dir_238_);
v___x_241_ = l_Lake_joinRelative(v_dir_238_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir___boxed(lean_object* v_self_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lake_Workspace_pkgsDir(v_self_242_);
lean_dec_ref(v_self_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs(lean_object* v_self_244_){
_start:
{
lean_object* v_packages_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_config_248_; lean_object* v_toLeanConfig_249_; lean_object* v_moreLeanArgs_250_; 
v_packages_245_ = lean_ctor_get(v_self_244_, 4);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_array_fget_borrowed(v_packages_245_, v___x_246_);
v_config_248_ = lean_ctor_get(v___x_247_, 6);
v_toLeanConfig_249_ = lean_ctor_get(v_config_248_, 1);
v_moreLeanArgs_250_ = lean_ctor_get(v_toLeanConfig_249_, 1);
lean_inc_ref(v_moreLeanArgs_250_);
return v_moreLeanArgs_250_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanArgs___boxed(lean_object* v_self_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_Workspace_leanArgs(v_self_251_);
lean_dec_ref(v_self_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* v_self_253_){
_start:
{
lean_object* v_packages_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_config_257_; lean_object* v_toLeanConfig_258_; lean_object* v_leanOptions_259_; lean_object* v___x_260_; 
v_packages_254_ = lean_ctor_get(v_self_253_, 4);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_array_fget_borrowed(v_packages_254_, v___x_255_);
v_config_257_ = lean_ctor_get(v___x_256_, 6);
v_toLeanConfig_258_ = lean_ctor_get(v_config_257_, 1);
v_leanOptions_259_ = lean_ctor_get(v_toLeanConfig_258_, 0);
v___x_260_ = l_Lean_LeanOptions_ofArray(v_leanOptions_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* v_self_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lake_Workspace_leanOptions(v_self_261_);
lean_dec_ref(v_self_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* v_self_263_){
_start:
{
lean_object* v_packages_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_config_267_; lean_object* v_toLeanConfig_268_; lean_object* v_leanOptions_269_; lean_object* v_moreServerOptions_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_packages_264_ = lean_ctor_get(v_self_263_, 4);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_array_fget_borrowed(v_packages_264_, v___x_265_);
v_config_267_ = lean_ctor_get(v___x_266_, 6);
v_toLeanConfig_268_ = lean_ctor_get(v_config_267_, 1);
v_leanOptions_269_ = lean_ctor_get(v_toLeanConfig_268_, 0);
v_moreServerOptions_270_ = lean_ctor_get(v_toLeanConfig_268_, 4);
v___x_271_ = l_Lean_LeanOptions_ofArray(v_leanOptions_269_);
v___x_272_ = l_Lean_LeanOptions_appendArray(v___x_271_, v_moreServerOptions_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* v_self_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lake_Workspace_serverOptions(v_self_273_);
lean_dec_ref(v_self_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots(lean_object* v_self_275_){
_start:
{
lean_object* v_packages_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_packages_276_ = lean_ctor_get(v_self_275_, 4);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_array_fget_borrowed(v_packages_276_, v___x_277_);
v___x_279_ = l_Lake_Package_defaultTargetRoots(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_defaultTargetRoots___boxed(lean_object* v_self_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lake_Workspace_defaultTargetRoots(v_self_280_);
lean_dec_ref(v_self_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* v_self_282_){
_start:
{
lean_object* v_packages_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_dir_286_; lean_object* v_relManifestFile_287_; lean_object* v___x_288_; 
v_packages_283_ = lean_ctor_get(v_self_282_, 4);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_array_fget_borrowed(v_packages_283_, v___x_284_);
v_dir_286_ = lean_ctor_get(v___x_285_, 4);
v_relManifestFile_287_ = lean_ctor_get(v___x_285_, 9);
lean_inc_ref(v_relManifestFile_287_);
lean_inc_ref(v_dir_286_);
v___x_288_ = l_Lake_joinRelative(v_dir_286_, v_relManifestFile_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile___boxed(lean_object* v_self_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lake_Workspace_manifestFile(v_self_289_);
lean_dec_ref(v_self_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* v_self_292_){
_start:
{
lean_object* v_packages_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_dir_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_packages_293_ = lean_ctor_get(v_self_292_, 4);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_array_fget_borrowed(v_packages_293_, v___x_294_);
v_dir_296_ = lean_ctor_get(v___x_295_, 4);
v___x_297_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_296_);
v___x_298_ = l_Lake_joinRelative(v_dir_296_, v___x_297_);
v___x_299_ = ((lean_object*)(l_Lake_Workspace_packageOverridesFile___closed__0));
v___x_300_ = l_Lake_joinRelative(v___x_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile___boxed(lean_object* v_self_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lake_Workspace_packageOverridesFile(v_self_301_);
lean_dec_ref(v_self_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27___redArg(lean_object* v_pkg_304_, lean_object* v_self_305_){
_start:
{
lean_object* v_lakeEnv_306_; lean_object* v_lakeConfig_307_; lean_object* v_lakeCache_308_; lean_object* v_lakeArgs_x3f_309_; lean_object* v_packages_310_; lean_object* v_packageMap_311_; lean_object* v_facetConfigs_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_323_; 
v_lakeEnv_306_ = lean_ctor_get(v_self_305_, 0);
v_lakeConfig_307_ = lean_ctor_get(v_self_305_, 1);
v_lakeCache_308_ = lean_ctor_get(v_self_305_, 2);
v_lakeArgs_x3f_309_ = lean_ctor_get(v_self_305_, 3);
v_packages_310_ = lean_ctor_get(v_self_305_, 4);
v_packageMap_311_ = lean_ctor_get(v_self_305_, 5);
v_facetConfigs_312_ = lean_ctor_get(v_self_305_, 6);
v_isSharedCheck_323_ = !lean_is_exclusive(v_self_305_);
if (v_isSharedCheck_323_ == 0)
{
v___x_314_ = v_self_305_;
v_isShared_315_ = v_isSharedCheck_323_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_facetConfigs_312_);
lean_inc(v_packageMap_311_);
lean_inc(v_packages_310_);
lean_inc(v_lakeArgs_x3f_309_);
lean_inc(v_lakeCache_308_);
lean_inc(v_lakeConfig_307_);
lean_inc(v_lakeEnv_306_);
lean_dec(v_self_305_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_323_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_keyName_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v_keyName_316_ = lean_ctor_get(v_pkg_304_, 2);
lean_inc(v_keyName_316_);
lean_inc_ref(v_pkg_304_);
v___x_317_ = lean_array_push(v_packages_310_, v_pkg_304_);
v___x_318_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_319_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_318_, v_keyName_316_, v_pkg_304_, v_packageMap_311_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 5, v___x_319_);
lean_ctor_set(v___x_314_, 4, v___x_317_);
v___x_321_ = v___x_314_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_lakeEnv_306_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_lakeConfig_307_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_lakeCache_308_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v_lakeArgs_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_322_, 4, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_322_, 5, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_322_, 6, v_facetConfigs_312_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage_x27(lean_object* v_pkg_324_, lean_object* v_self_325_, lean_object* v_h_326_){
_start:
{
lean_object* v_lakeEnv_327_; lean_object* v_lakeConfig_328_; lean_object* v_lakeCache_329_; lean_object* v_lakeArgs_x3f_330_; lean_object* v_packages_331_; lean_object* v_packageMap_332_; lean_object* v_facetConfigs_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_344_; 
v_lakeEnv_327_ = lean_ctor_get(v_self_325_, 0);
v_lakeConfig_328_ = lean_ctor_get(v_self_325_, 1);
v_lakeCache_329_ = lean_ctor_get(v_self_325_, 2);
v_lakeArgs_x3f_330_ = lean_ctor_get(v_self_325_, 3);
v_packages_331_ = lean_ctor_get(v_self_325_, 4);
v_packageMap_332_ = lean_ctor_get(v_self_325_, 5);
v_facetConfigs_333_ = lean_ctor_get(v_self_325_, 6);
v_isSharedCheck_344_ = !lean_is_exclusive(v_self_325_);
if (v_isSharedCheck_344_ == 0)
{
v___x_335_ = v_self_325_;
v_isShared_336_ = v_isSharedCheck_344_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_facetConfigs_333_);
lean_inc(v_packageMap_332_);
lean_inc(v_packages_331_);
lean_inc(v_lakeArgs_x3f_330_);
lean_inc(v_lakeCache_329_);
lean_inc(v_lakeConfig_328_);
lean_inc(v_lakeEnv_327_);
lean_dec(v_self_325_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_344_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v_keyName_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v_keyName_337_ = lean_ctor_get(v_pkg_324_, 2);
lean_inc(v_keyName_337_);
lean_inc_ref(v_pkg_324_);
v___x_338_ = lean_array_push(v_packages_331_, v_pkg_324_);
v___x_339_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_340_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_339_, v_keyName_337_, v_pkg_324_, v_packageMap_332_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 5, v___x_340_);
lean_ctor_set(v___x_335_, 4, v___x_338_);
v___x_342_ = v___x_335_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_lakeEnv_327_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_lakeConfig_328_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_lakeCache_329_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_lakeArgs_x3f_330_);
lean_ctor_set(v_reuseFailAlloc_343_, 4, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_343_, 5, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_343_, 6, v_facetConfigs_333_);
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
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* v_pkg_345_, lean_object* v_self_346_){
_start:
{
lean_object* v_lakeEnv_347_; lean_object* v_lakeConfig_348_; lean_object* v_lakeCache_349_; lean_object* v_lakeArgs_x3f_350_; lean_object* v_packages_351_; lean_object* v_packageMap_352_; lean_object* v_facetConfigs_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_394_; 
v_lakeEnv_347_ = lean_ctor_get(v_self_346_, 0);
v_lakeConfig_348_ = lean_ctor_get(v_self_346_, 1);
v_lakeCache_349_ = lean_ctor_get(v_self_346_, 2);
v_lakeArgs_x3f_350_ = lean_ctor_get(v_self_346_, 3);
v_packages_351_ = lean_ctor_get(v_self_346_, 4);
v_packageMap_352_ = lean_ctor_get(v_self_346_, 5);
v_facetConfigs_353_ = lean_ctor_get(v_self_346_, 6);
v_isSharedCheck_394_ = !lean_is_exclusive(v_self_346_);
if (v_isSharedCheck_394_ == 0)
{
v___x_355_ = v_self_346_;
v_isShared_356_ = v_isSharedCheck_394_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_facetConfigs_353_);
lean_inc(v_packageMap_352_);
lean_inc(v_packages_351_);
lean_inc(v_lakeArgs_x3f_350_);
lean_inc(v_lakeCache_349_);
lean_inc(v_lakeConfig_348_);
lean_inc(v_lakeEnv_347_);
lean_dec(v_self_346_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_394_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_baseName_357_; lean_object* v_keyName_358_; lean_object* v_origName_359_; lean_object* v_dir_360_; lean_object* v_relDir_361_; lean_object* v_config_362_; lean_object* v_configFile_363_; lean_object* v_relConfigFile_364_; lean_object* v_relManifestFile_365_; lean_object* v_scope_366_; lean_object* v_remoteUrl_367_; lean_object* v_depConfigs_368_; lean_object* v_depPkgs_369_; lean_object* v_targetDecls_370_; lean_object* v_targetDeclMap_371_; lean_object* v_defaultTargets_372_; lean_object* v_scripts_373_; lean_object* v_defaultScripts_374_; lean_object* v_postUpdateHooks_375_; lean_object* v_buildArchive_376_; lean_object* v_testDriver_377_; lean_object* v_lintDriver_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_392_; 
v_baseName_357_ = lean_ctor_get(v_pkg_345_, 1);
v_keyName_358_ = lean_ctor_get(v_pkg_345_, 2);
v_origName_359_ = lean_ctor_get(v_pkg_345_, 3);
v_dir_360_ = lean_ctor_get(v_pkg_345_, 4);
v_relDir_361_ = lean_ctor_get(v_pkg_345_, 5);
v_config_362_ = lean_ctor_get(v_pkg_345_, 6);
v_configFile_363_ = lean_ctor_get(v_pkg_345_, 7);
v_relConfigFile_364_ = lean_ctor_get(v_pkg_345_, 8);
v_relManifestFile_365_ = lean_ctor_get(v_pkg_345_, 9);
v_scope_366_ = lean_ctor_get(v_pkg_345_, 10);
v_remoteUrl_367_ = lean_ctor_get(v_pkg_345_, 11);
v_depConfigs_368_ = lean_ctor_get(v_pkg_345_, 12);
v_depPkgs_369_ = lean_ctor_get(v_pkg_345_, 13);
v_targetDecls_370_ = lean_ctor_get(v_pkg_345_, 14);
v_targetDeclMap_371_ = lean_ctor_get(v_pkg_345_, 15);
v_defaultTargets_372_ = lean_ctor_get(v_pkg_345_, 16);
v_scripts_373_ = lean_ctor_get(v_pkg_345_, 17);
v_defaultScripts_374_ = lean_ctor_get(v_pkg_345_, 18);
v_postUpdateHooks_375_ = lean_ctor_get(v_pkg_345_, 19);
v_buildArchive_376_ = lean_ctor_get(v_pkg_345_, 20);
v_testDriver_377_ = lean_ctor_get(v_pkg_345_, 21);
v_lintDriver_378_ = lean_ctor_get(v_pkg_345_, 22);
v_isSharedCheck_392_ = !lean_is_exclusive(v_pkg_345_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v_pkg_345_, 0);
lean_dec(v_unused_393_);
v___x_380_ = v_pkg_345_;
v_isShared_381_ = v_isSharedCheck_392_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_lintDriver_378_);
lean_inc(v_testDriver_377_);
lean_inc(v_buildArchive_376_);
lean_inc(v_postUpdateHooks_375_);
lean_inc(v_defaultScripts_374_);
lean_inc(v_scripts_373_);
lean_inc(v_defaultTargets_372_);
lean_inc(v_targetDeclMap_371_);
lean_inc(v_targetDecls_370_);
lean_inc(v_depPkgs_369_);
lean_inc(v_depConfigs_368_);
lean_inc(v_remoteUrl_367_);
lean_inc(v_scope_366_);
lean_inc(v_relManifestFile_365_);
lean_inc(v_relConfigFile_364_);
lean_inc(v_configFile_363_);
lean_inc(v_config_362_);
lean_inc(v_relDir_361_);
lean_inc(v_dir_360_);
lean_inc(v_origName_359_);
lean_inc(v_keyName_358_);
lean_inc(v_baseName_357_);
lean_dec(v_pkg_345_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_392_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_382_ = lean_array_get_size(v_packages_351_);
lean_inc(v_keyName_358_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 23, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_baseName_357_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_keyName_358_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v_origName_359_);
lean_ctor_set(v_reuseFailAlloc_391_, 4, v_dir_360_);
lean_ctor_set(v_reuseFailAlloc_391_, 5, v_relDir_361_);
lean_ctor_set(v_reuseFailAlloc_391_, 6, v_config_362_);
lean_ctor_set(v_reuseFailAlloc_391_, 7, v_configFile_363_);
lean_ctor_set(v_reuseFailAlloc_391_, 8, v_relConfigFile_364_);
lean_ctor_set(v_reuseFailAlloc_391_, 9, v_relManifestFile_365_);
lean_ctor_set(v_reuseFailAlloc_391_, 10, v_scope_366_);
lean_ctor_set(v_reuseFailAlloc_391_, 11, v_remoteUrl_367_);
lean_ctor_set(v_reuseFailAlloc_391_, 12, v_depConfigs_368_);
lean_ctor_set(v_reuseFailAlloc_391_, 13, v_depPkgs_369_);
lean_ctor_set(v_reuseFailAlloc_391_, 14, v_targetDecls_370_);
lean_ctor_set(v_reuseFailAlloc_391_, 15, v_targetDeclMap_371_);
lean_ctor_set(v_reuseFailAlloc_391_, 16, v_defaultTargets_372_);
lean_ctor_set(v_reuseFailAlloc_391_, 17, v_scripts_373_);
lean_ctor_set(v_reuseFailAlloc_391_, 18, v_defaultScripts_374_);
lean_ctor_set(v_reuseFailAlloc_391_, 19, v_postUpdateHooks_375_);
lean_ctor_set(v_reuseFailAlloc_391_, 20, v_buildArchive_376_);
lean_ctor_set(v_reuseFailAlloc_391_, 21, v_testDriver_377_);
lean_ctor_set(v_reuseFailAlloc_391_, 22, v_lintDriver_378_);
v___x_384_ = v_reuseFailAlloc_391_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
lean_inc_ref(v___x_384_);
v___x_385_ = lean_array_push(v_packages_351_, v___x_384_);
v___x_386_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_387_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___x_386_, v_keyName_358_, v___x_384_, v_packageMap_352_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 5, v___x_387_);
lean_ctor_set(v___x_355_, 4, v___x_385_);
v___x_389_ = v___x_355_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_lakeEnv_347_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_lakeConfig_348_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_lakeCache_349_);
lean_ctor_set(v_reuseFailAlloc_390_, 3, v_lakeArgs_x3f_350_);
lean_ctor_set(v_reuseFailAlloc_390_, 4, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_390_, 5, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_390_, 6, v_facetConfigs_353_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByKey_x3f(lean_object* v_keyName_395_, lean_object* v_self_396_){
_start:
{
lean_object* v_packageMap_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_packageMap_397_ = lean_ctor_get(v_self_396_, 5);
lean_inc(v_packageMap_397_);
lean_dec_ref(v_self_396_);
v___x_398_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_399_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_398_, v_packageMap_397_, v_keyName_395_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0(lean_object* v_name_400_, lean_object* v___x_401_, lean_object* v___x_402_, lean_object* v_a_403_, lean_object* v_x_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_baseName_406_; uint8_t v___x_407_; 
v_baseName_406_ = lean_ctor_get(v_a_403_, 1);
v___x_407_ = lean_name_eq(v_baseName_406_, v_name_400_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_a_403_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_401_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v___x_401_);
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_a_403_);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_402_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(lean_object* v_name_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_a_416_, lean_object* v_x_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(v_name_413_, v___x_414_, v___x_415_, v_a_416_, v_x_417_, v___y_418_);
lean_dec_ref(v___y_418_);
lean_dec(v_name_413_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageByName_x3f(lean_object* v_name_442_, lean_object* v_self_443_){
_start:
{
lean_object* v_packages_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___f_449_; size_t v_sz_450_; size_t v___x_451_; lean_object* v___x_452_; lean_object* v_fst_453_; 
v_packages_444_ = lean_ctor_get(v_self_443_, 4);
lean_inc_ref(v_packages_444_);
lean_dec_ref(v_self_443_);
v___x_445_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__9));
v___x_446_ = lean_box(0);
v___x_447_ = lean_box(0);
v___x_448_ = ((lean_object*)(l_Lake_Workspace_findPackageByName_x3f___closed__10));
v___f_449_ = lean_alloc_closure((void*)(l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed), 6, 3);
lean_closure_set(v___f_449_, 0, v_name_442_);
lean_closure_set(v___f_449_, 1, v___x_448_);
lean_closure_set(v___f_449_, 2, v___x_447_);
v_sz_450_ = lean_array_size(v_packages_444_);
v___x_451_ = ((size_t)0ULL);
v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_445_, v_packages_444_, v___f_449_, v_sz_450_, v___x_451_, v___x_448_);
v_fst_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_fst_453_);
lean_dec(v___x_452_);
if (lean_obj_tag(v_fst_453_) == 0)
{
return v___x_446_;
}
else
{
lean_object* v_val_454_; 
v_val_454_ = lean_ctor_get(v_fst_453_, 0);
lean_inc(v_val_454_);
lean_dec_ref(v_fst_453_);
return v_val_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* v_name_455_, lean_object* v_self_456_){
_start:
{
lean_object* v_packageMap_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_packageMap_457_ = lean_ctor_get(v_self_456_, 5);
lean_inc(v_packageMap_457_);
lean_dec_ref(v_self_456_);
v___x_458_ = ((lean_object*)(l_Lake_Workspace_addPackage_x27___redArg___closed__0));
v___x_459_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_458_, v_packageMap_457_, v_name_455_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(lean_object* v_script_463_, lean_object* v_as_464_, size_t v_sz_465_, size_t v_i_466_, lean_object* v_b_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_lt(v_i_466_, v_sz_465_);
if (v___x_468_ == 0)
{
lean_inc_ref(v_b_467_);
return v_b_467_;
}
else
{
lean_object* v_a_469_; lean_object* v_scripts_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_a_469_ = lean_array_uget_borrowed(v_as_464_, v_i_466_);
v_scripts_470_ = lean_ctor_get(v_a_469_, 17);
v___x_471_ = lean_box(0);
v___x_472_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_470_, v_script_463_);
if (lean_obj_tag(v___x_472_) == 1)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_471_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; size_t v___x_476_; size_t v___x_477_; 
lean_dec(v___x_472_);
v___x_475_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_add(v_i_466_, v___x_476_);
v_i_466_ = v___x_477_;
v_b_467_ = v___x_475_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* v_script_479_, lean_object* v_as_480_, lean_object* v_sz_481_, lean_object* v_i_482_, lean_object* v_b_483_){
_start:
{
size_t v_sz_boxed_484_; size_t v_i_boxed_485_; lean_object* v_res_486_; 
v_sz_boxed_484_ = lean_unbox_usize(v_sz_481_);
lean_dec(v_sz_481_);
v_i_boxed_485_ = lean_unbox_usize(v_i_482_);
lean_dec(v_i_482_);
v_res_486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_479_, v_as_480_, v_sz_boxed_484_, v_i_boxed_485_, v_b_483_);
lean_dec_ref(v_b_483_);
lean_dec_ref(v_as_480_);
lean_dec(v_script_479_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* v_script_487_, lean_object* v_self_488_){
_start:
{
lean_object* v_packages_489_; lean_object* v___x_490_; lean_object* v___x_491_; size_t v_sz_492_; size_t v___x_493_; lean_object* v___x_494_; lean_object* v_fst_495_; 
v_packages_489_ = lean_ctor_get(v_self_488_, 4);
v___x_490_ = lean_box(0);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0));
v_sz_492_ = lean_array_size(v_packages_489_);
v___x_493_ = ((size_t)0ULL);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_487_, v_packages_489_, v_sz_492_, v___x_493_, v___x_491_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
lean_dec_ref(v___x_494_);
if (lean_obj_tag(v_fst_495_) == 0)
{
return v___x_490_;
}
else
{
lean_object* v_val_496_; 
v_val_496_ = lean_ctor_get(v_fst_495_, 0);
lean_inc(v_val_496_);
lean_dec_ref(v_fst_495_);
return v_val_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* v_script_497_, lean_object* v_self_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lake_Workspace_findScript_x3f(v_script_497_, v_self_498_);
lean_dec_ref(v_self_498_);
lean_dec(v_script_497_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(lean_object* v_mod_500_, lean_object* v_as_501_, size_t v_i_502_, size_t v_stop_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_502_, v_stop_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_uget_borrowed(v_as_501_, v_i_502_);
v___x_506_ = l_Lake_Package_isLocalModule(v_mod_500_, v___x_505_);
if (v___x_506_ == 0)
{
size_t v___x_507_; size_t v___x_508_; 
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_502_, v___x_507_);
v_i_502_ = v___x_508_;
goto _start;
}
else
{
return v___x_506_;
}
}
else
{
uint8_t v___x_510_; 
v___x_510_ = 0;
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* v_mod_511_, lean_object* v_as_512_, lean_object* v_i_513_, lean_object* v_stop_514_){
_start:
{
size_t v_i_boxed_515_; size_t v_stop_boxed_516_; uint8_t v_res_517_; lean_object* v_r_518_; 
v_i_boxed_515_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_stop_boxed_516_ = lean_unbox_usize(v_stop_514_);
lean_dec(v_stop_514_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_511_, v_as_512_, v_i_boxed_515_, v_stop_boxed_516_);
lean_dec_ref(v_as_512_);
lean_dec(v_mod_511_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* v_mod_519_, lean_object* v_self_520_){
_start:
{
lean_object* v_packages_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_packages_521_ = lean_ctor_get(v_self_520_, 4);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_array_get_size(v_packages_521_);
v___x_524_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
return v___x_524_;
}
else
{
if (v___x_524_ == 0)
{
return v___x_524_;
}
else
{
size_t v___x_525_; size_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_523_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_519_, v_packages_521_, v___x_525_, v___x_526_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* v_mod_528_, lean_object* v_self_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Lake_Workspace_isLocalModule(v_mod_528_, v_self_529_);
lean_dec_ref(v_self_529_);
lean_dec(v_mod_528_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(lean_object* v_mod_532_, lean_object* v_as_533_, size_t v_i_534_, size_t v_stop_535_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = lean_usize_dec_eq(v_i_534_, v_stop_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_array_uget_borrowed(v_as_533_, v_i_534_);
v___x_538_ = l_Lake_Package_isBuildableModule(v_mod_532_, v___x_537_);
if (v___x_538_ == 0)
{
size_t v___x_539_; size_t v___x_540_; 
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_add(v_i_534_, v___x_539_);
v_i_534_ = v___x_540_;
goto _start;
}
else
{
return v___x_538_;
}
}
else
{
uint8_t v___x_542_; 
v___x_542_ = 0;
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* v_mod_543_, lean_object* v_as_544_, lean_object* v_i_545_, lean_object* v_stop_546_){
_start:
{
size_t v_i_boxed_547_; size_t v_stop_boxed_548_; uint8_t v_res_549_; lean_object* v_r_550_; 
v_i_boxed_547_ = lean_unbox_usize(v_i_545_);
lean_dec(v_i_545_);
v_stop_boxed_548_ = lean_unbox_usize(v_stop_546_);
lean_dec(v_stop_546_);
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_543_, v_as_544_, v_i_boxed_547_, v_stop_boxed_548_);
lean_dec_ref(v_as_544_);
lean_dec(v_mod_543_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* v_mod_551_, lean_object* v_self_552_){
_start:
{
lean_object* v_packages_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_packages_553_ = lean_ctor_get(v_self_552_, 4);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_array_get_size(v_packages_553_);
v___x_556_ = lean_nat_dec_lt(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
return v___x_556_;
}
else
{
if (v___x_556_ == 0)
{
return v___x_556_;
}
else
{
size_t v___x_557_; size_t v___x_558_; uint8_t v___x_559_; 
v___x_557_ = ((size_t)0ULL);
v___x_558_ = lean_usize_of_nat(v___x_555_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_551_, v_packages_553_, v___x_557_, v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* v_mod_560_, lean_object* v_self_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_Lake_Workspace_isBuildableModule(v_mod_560_, v_self_561_);
lean_dec_ref(v_self_561_);
lean_dec(v_mod_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(lean_object* v_mod_567_, lean_object* v_as_568_, size_t v_sz_569_, size_t v_i_570_, lean_object* v_b_571_){
_start:
{
uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_lt(v_i_570_, v_sz_569_);
if (v___x_572_ == 0)
{
lean_dec(v_mod_567_);
lean_inc_ref(v_b_571_);
return v_b_571_;
}
else
{
lean_object* v___x_573_; lean_object* v_a_574_; lean_object* v___x_575_; 
v___x_573_ = lean_box(0);
v_a_574_ = lean_array_uget_borrowed(v_as_568_, v_i_570_);
lean_inc(v_a_574_);
lean_inc(v_mod_567_);
v___x_575_ = l_Lake_Package_findModule_x3f(v_mod_567_, v_a_574_);
if (lean_obj_tag(v___x_575_) == 1)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_mod_567_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_573_);
return v___x_577_;
}
else
{
lean_object* v___x_578_; size_t v___x_579_; size_t v___x_580_; 
lean_dec(v___x_575_);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_570_, v___x_579_);
v_i_570_ = v___x_580_;
v_b_571_ = v___x_578_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* v_mod_582_, lean_object* v_as_583_, lean_object* v_sz_584_, lean_object* v_i_585_, lean_object* v_b_586_){
_start:
{
size_t v_sz_boxed_587_; size_t v_i_boxed_588_; lean_object* v_res_589_; 
v_sz_boxed_587_ = lean_unbox_usize(v_sz_584_);
lean_dec(v_sz_584_);
v_i_boxed_588_ = lean_unbox_usize(v_i_585_);
lean_dec(v_i_585_);
v_res_589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_582_, v_as_583_, v_sz_boxed_587_, v_i_boxed_588_, v_b_586_);
lean_dec_ref(v_b_586_);
lean_dec_ref(v_as_583_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* v_mod_590_, lean_object* v_self_591_){
_start:
{
lean_object* v_packages_592_; lean_object* v___x_593_; lean_object* v___x_594_; size_t v_sz_595_; size_t v___x_596_; lean_object* v___x_597_; lean_object* v_fst_598_; 
v_packages_592_ = lean_ctor_get(v_self_591_, 4);
v___x_593_ = lean_box(0);
v___x_594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_595_ = lean_array_size(v_packages_592_);
v___x_596_ = ((size_t)0ULL);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_590_, v_packages_592_, v_sz_595_, v___x_596_, v___x_594_);
v_fst_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_fst_598_);
lean_dec_ref(v___x_597_);
if (lean_obj_tag(v_fst_598_) == 0)
{
return v___x_593_;
}
else
{
lean_object* v_val_599_; 
v_val_599_ = lean_ctor_get(v_fst_598_, 0);
lean_inc(v_val_599_);
lean_dec_ref(v_fst_598_);
return v_val_599_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* v_mod_600_, lean_object* v_self_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lake_Workspace_findModule_x3f(v_mod_600_, v_self_601_);
lean_dec_ref(v_self_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(lean_object* v_mod_603_, lean_object* v_as_604_, size_t v_i_605_, size_t v_stop_606_, lean_object* v_b_607_){
_start:
{
lean_object* v___y_609_; uint8_t v___x_613_; 
v___x_613_ = lean_usize_dec_eq(v_i_605_, v_stop_606_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_array_uget_borrowed(v_as_604_, v_i_605_);
lean_inc(v___x_614_);
lean_inc(v_mod_603_);
v___x_615_ = l_Lake_Package_findModule_x3f(v_mod_603_, v___x_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
v___y_609_ = v_b_607_;
goto v___jp_608_;
}
else
{
lean_object* v_val_616_; lean_object* v___x_617_; 
v_val_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_616_);
lean_dec_ref(v___x_615_);
v___x_617_ = lean_array_push(v_b_607_, v_val_616_);
v___y_609_ = v___x_617_;
goto v___jp_608_;
}
}
else
{
lean_dec(v_mod_603_);
return v_b_607_;
}
v___jp_608_:
{
size_t v___x_610_; size_t v___x_611_; 
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_add(v_i_605_, v___x_610_);
v_i_605_ = v___x_611_;
v_b_607_ = v___y_609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(lean_object* v_mod_618_, lean_object* v_as_619_, lean_object* v_i_620_, lean_object* v_stop_621_, lean_object* v_b_622_){
_start:
{
size_t v_i_boxed_623_; size_t v_stop_boxed_624_; lean_object* v_res_625_; 
v_i_boxed_623_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_stop_boxed_624_ = lean_unbox_usize(v_stop_621_);
lean_dec(v_stop_621_);
v_res_625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_618_, v_as_619_, v_i_boxed_623_, v_stop_boxed_624_, v_b_622_);
lean_dec_ref(v_as_619_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(lean_object* v_mod_628_, lean_object* v_as_629_, lean_object* v_start_630_, lean_object* v_stop_631_){
_start:
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = ((lean_object*)(l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0));
v___x_633_ = lean_nat_dec_lt(v_start_630_, v_stop_631_);
if (v___x_633_ == 0)
{
lean_dec(v_mod_628_);
return v___x_632_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = lean_array_get_size(v_as_629_);
v___x_635_ = lean_nat_dec_le(v_stop_631_, v___x_634_);
if (v___x_635_ == 0)
{
uint8_t v___x_636_; 
v___x_636_ = lean_nat_dec_lt(v_start_630_, v___x_634_);
if (v___x_636_ == 0)
{
lean_dec(v_mod_628_);
return v___x_632_;
}
else
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_usize_of_nat(v_start_630_);
v___x_638_ = lean_usize_of_nat(v___x_634_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_628_, v_as_629_, v___x_637_, v___x_638_, v___x_632_);
return v___x_639_;
}
}
else
{
size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_usize_of_nat(v_start_630_);
v___x_641_ = lean_usize_of_nat(v_stop_631_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_628_, v_as_629_, v___x_640_, v___x_641_, v___x_632_);
return v___x_642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(lean_object* v_mod_643_, lean_object* v_as_644_, lean_object* v_start_645_, lean_object* v_stop_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_643_, v_as_644_, v_start_645_, v_stop_646_);
lean_dec(v_stop_646_);
lean_dec(v_start_645_);
lean_dec_ref(v_as_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules(lean_object* v_mod_648_, lean_object* v_self_649_){
_start:
{
lean_object* v_packages_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_packages_650_ = lean_ctor_get(v_self_649_, 4);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_packages_650_);
v___x_653_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(v_mod_648_, v_packages_650_, v___x_651_, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModules___boxed(lean_object* v_mod_654_, lean_object* v_self_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lake_Workspace_findModules(v_mod_654_, v_self_655_);
lean_dec_ref(v_self_655_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* v_mod_657_, lean_object* v_as_658_, size_t v_sz_659_, size_t v_i_660_, lean_object* v_b_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_lt(v_i_660_, v_sz_659_);
if (v___x_662_ == 0)
{
lean_dec(v_mod_657_);
lean_inc_ref(v_b_661_);
return v_b_661_;
}
else
{
lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_665_; 
v___x_663_ = lean_box(0);
v_a_664_ = lean_array_uget_borrowed(v_as_658_, v_i_660_);
lean_inc(v_a_664_);
lean_inc(v_mod_657_);
v___x_665_ = l_Lake_Package_findTargetModule_x3f(v_mod_657_, v_a_664_);
if (lean_obj_tag(v___x_665_) == 1)
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v_mod_657_);
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___x_663_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; size_t v___x_669_; size_t v___x_670_; 
lean_dec(v___x_665_);
v___x_668_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_660_, v___x_669_);
v_i_660_ = v___x_670_;
v_b_661_ = v___x_668_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* v_mod_672_, lean_object* v_as_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_b_676_){
_start:
{
size_t v_sz_boxed_677_; size_t v_i_boxed_678_; lean_object* v_res_679_; 
v_sz_boxed_677_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_672_, v_as_673_, v_sz_boxed_677_, v_i_boxed_678_, v_b_676_);
lean_dec_ref(v_b_676_);
lean_dec_ref(v_as_673_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* v_mod_680_, lean_object* v_self_681_){
_start:
{
lean_object* v_packages_682_; lean_object* v___x_683_; lean_object* v___x_684_; size_t v_sz_685_; size_t v___x_686_; lean_object* v___x_687_; lean_object* v_fst_688_; 
v_packages_682_ = lean_ctor_get(v_self_681_, 4);
v___x_683_ = lean_box(0);
v___x_684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_685_ = lean_array_size(v_packages_682_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_680_, v_packages_682_, v_sz_685_, v___x_686_, v___x_684_);
v_fst_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_fst_688_);
lean_dec_ref(v___x_687_);
if (lean_obj_tag(v_fst_688_) == 0)
{
return v___x_683_;
}
else
{
lean_object* v_val_689_; 
v_val_689_ = lean_ctor_get(v_fst_688_, 0);
lean_inc(v_val_689_);
lean_dec_ref(v_fst_688_);
return v_val_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* v_mod_690_, lean_object* v_self_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_690_, v_self_691_);
lean_dec_ref(v_self_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* v_path_693_, lean_object* v_as_694_, size_t v_sz_695_, size_t v_i_696_, lean_object* v_b_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_698_ == 0)
{
lean_dec_ref(v_path_693_);
lean_inc_ref(v_b_697_);
return v_b_697_;
}
else
{
lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_701_; 
v___x_699_ = lean_box(0);
v_a_700_ = lean_array_uget_borrowed(v_as_694_, v_i_696_);
lean_inc(v_a_700_);
lean_inc_ref(v_path_693_);
v___x_701_ = l_Lake_Package_findModuleBySrc_x3f(v_path_693_, v_a_700_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref(v_path_693_);
v___x_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_699_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; size_t v___x_705_; size_t v___x_706_; 
lean_dec(v___x_701_);
v___x_704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_696_, v___x_705_);
v_i_696_ = v___x_706_;
v_b_697_ = v___x_704_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* v_path_708_, lean_object* v_as_709_, lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_b_712_){
_start:
{
size_t v_sz_boxed_713_; size_t v_i_boxed_714_; lean_object* v_res_715_; 
v_sz_boxed_713_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_708_, v_as_709_, v_sz_boxed_713_, v_i_boxed_714_, v_b_712_);
lean_dec_ref(v_b_712_);
lean_dec_ref(v_as_709_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* v_path_716_, lean_object* v_self_717_){
_start:
{
lean_object* v_packages_718_; lean_object* v___x_719_; lean_object* v___x_720_; size_t v_sz_721_; size_t v___x_722_; lean_object* v___x_723_; lean_object* v_fst_724_; 
v_packages_718_ = lean_ctor_get(v_self_717_, 4);
v___x_719_ = lean_box(0);
v___x_720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0));
v_sz_721_ = lean_array_size(v_packages_718_);
v___x_722_ = ((size_t)0ULL);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_716_, v_packages_718_, v_sz_721_, v___x_722_, v___x_720_);
v_fst_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_fst_724_);
lean_dec_ref(v___x_723_);
if (lean_obj_tag(v_fst_724_) == 0)
{
return v___x_719_;
}
else
{
lean_object* v_val_725_; 
v_val_725_ = lean_ctor_get(v_fst_724_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v_fst_724_);
return v_val_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* v_path_726_, lean_object* v_self_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_726_, v_self_727_);
lean_dec_ref(v_self_727_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* v_name_732_, lean_object* v_as_733_, size_t v_sz_734_, size_t v_i_735_, lean_object* v_b_736_){
_start:
{
lean_object* v_a_738_; uint8_t v___x_742_; 
v___x_742_ = lean_usize_dec_lt(v_i_735_, v_sz_734_);
if (v___x_742_ == 0)
{
lean_inc_ref(v_b_736_);
return v_b_736_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_746_; 
v___x_743_ = lean_box(0);
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_745_ = lean_array_uget_borrowed(v_as_733_, v_i_735_);
v___x_746_ = l_Lake_Package_findTargetDecl_x3f(v_name_732_, v_a_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
v_a_738_ = v___x_744_;
goto v___jp_737_;
}
else
{
lean_object* v_val_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_762_; 
v_val_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_762_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_762_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_val_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_762_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_name_751_; lean_object* v_kind_752_; lean_object* v_config_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_name_751_ = lean_ctor_get(v_val_747_, 1);
lean_inc(v_name_751_);
v_kind_752_ = lean_ctor_get(v_val_747_, 2);
lean_inc(v_kind_752_);
v_config_753_ = lean_ctor_get(v_val_747_, 3);
lean_inc(v_config_753_);
lean_dec(v_val_747_);
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_755_ = lean_name_eq(v_kind_752_, v___x_754_);
lean_dec(v_kind_752_);
if (v___x_755_ == 0)
{
lean_dec(v_config_753_);
lean_dec(v_name_751_);
lean_del_object(v___x_749_);
v_a_738_ = v___x_744_;
goto v___jp_737_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc(v_a_745_);
v___x_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_756_, 0, v_a_745_);
lean_ctor_set(v___x_756_, 1, v_name_751_);
lean_ctor_set(v___x_756_, 2, v_config_753_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_756_);
v___x_758_ = v___x_749_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_761_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
lean_ctor_set(v___x_760_, 1, v___x_743_);
return v___x_760_;
}
}
}
}
}
v___jp_737_:
{
size_t v___x_739_; size_t v___x_740_; 
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_735_, v___x_739_);
v_i_735_ = v___x_740_;
v_b_736_ = v_a_738_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* v_name_763_, lean_object* v_as_764_, lean_object* v_sz_765_, lean_object* v_i_766_, lean_object* v_b_767_){
_start:
{
size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v_sz_boxed_768_ = lean_unbox_usize(v_sz_765_);
lean_dec(v_sz_765_);
v_i_boxed_769_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_763_, v_as_764_, v_sz_boxed_768_, v_i_boxed_769_, v_b_767_);
lean_dec_ref(v_b_767_);
lean_dec_ref(v_as_764_);
lean_dec(v_name_763_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* v_name_771_, lean_object* v_self_772_){
_start:
{
lean_object* v_packages_773_; lean_object* v___x_774_; lean_object* v___x_775_; size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; lean_object* v_fst_779_; 
v_packages_773_ = lean_ctor_get(v_self_772_, 4);
v___x_774_ = lean_box(0);
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_776_ = lean_array_size(v_packages_773_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_771_, v_packages_773_, v_sz_776_, v___x_777_, v___x_775_);
v_fst_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_fst_779_);
lean_dec_ref(v___x_778_);
if (lean_obj_tag(v_fst_779_) == 0)
{
return v___x_774_;
}
else
{
lean_object* v_val_780_; 
v_val_780_ = lean_ctor_get(v_fst_779_, 0);
lean_inc(v_val_780_);
lean_dec_ref(v_fst_779_);
return v_val_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* v_name_781_, lean_object* v_self_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lake_Workspace_findLeanLib_x3f(v_name_781_, v_self_782_);
lean_dec_ref(v_self_782_);
lean_dec(v_name_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* v_name_784_, lean_object* v_as_785_, size_t v_sz_786_, size_t v_i_787_, lean_object* v_b_788_){
_start:
{
lean_object* v_a_790_; uint8_t v___x_794_; 
v___x_794_ = lean_usize_dec_lt(v_i_787_, v_sz_786_);
if (v___x_794_ == 0)
{
lean_inc_ref(v_b_788_);
return v_b_788_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_798_; 
v___x_795_ = lean_box(0);
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_797_ = lean_array_uget_borrowed(v_as_785_, v_i_787_);
v___x_798_ = l_Lake_Package_findTargetDecl_x3f(v_name_784_, v_a_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
v_a_790_ = v___x_796_;
goto v___jp_789_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_814_; 
v_val_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_814_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_814_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_val_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_814_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_name_803_; lean_object* v_kind_804_; lean_object* v_config_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_name_803_ = lean_ctor_get(v_val_799_, 1);
lean_inc(v_name_803_);
v_kind_804_ = lean_ctor_get(v_val_799_, 2);
lean_inc(v_kind_804_);
v_config_805_ = lean_ctor_get(v_val_799_, 3);
lean_inc(v_config_805_);
lean_dec(v_val_799_);
v___x_806_ = l_Lake_LeanExe_keyword;
v___x_807_ = lean_name_eq(v_kind_804_, v___x_806_);
lean_dec(v_kind_804_);
if (v___x_807_ == 0)
{
lean_dec(v_config_805_);
lean_dec(v_name_803_);
lean_del_object(v___x_801_);
v_a_790_ = v___x_796_;
goto v___jp_789_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_inc(v_a_797_);
v___x_808_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_808_, 0, v_a_797_);
lean_ctor_set(v___x_808_, 1, v_name_803_);
lean_ctor_set(v___x_808_, 2, v_config_805_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_808_);
v___x_810_ = v___x_801_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_813_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___x_795_);
return v___x_812_;
}
}
}
}
}
v___jp_789_:
{
size_t v___x_791_; size_t v___x_792_; 
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_787_, v___x_791_);
v_i_787_ = v___x_792_;
v_b_788_ = v_a_790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* v_name_815_, lean_object* v_as_816_, lean_object* v_sz_817_, lean_object* v_i_818_, lean_object* v_b_819_){
_start:
{
size_t v_sz_boxed_820_; size_t v_i_boxed_821_; lean_object* v_res_822_; 
v_sz_boxed_820_ = lean_unbox_usize(v_sz_817_);
lean_dec(v_sz_817_);
v_i_boxed_821_ = lean_unbox_usize(v_i_818_);
lean_dec(v_i_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_815_, v_as_816_, v_sz_boxed_820_, v_i_boxed_821_, v_b_819_);
lean_dec_ref(v_b_819_);
lean_dec_ref(v_as_816_);
lean_dec(v_name_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* v_name_823_, lean_object* v_self_824_){
_start:
{
lean_object* v_packages_825_; lean_object* v___x_826_; lean_object* v___x_827_; size_t v_sz_828_; size_t v___x_829_; lean_object* v___x_830_; lean_object* v_fst_831_; 
v_packages_825_ = lean_ctor_get(v_self_824_, 4);
v___x_826_ = lean_box(0);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_828_ = lean_array_size(v_packages_825_);
v___x_829_ = ((size_t)0ULL);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_823_, v_packages_825_, v_sz_828_, v___x_829_, v___x_827_);
v_fst_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_fst_831_);
lean_dec_ref(v___x_830_);
if (lean_obj_tag(v_fst_831_) == 0)
{
return v___x_826_;
}
else
{
lean_object* v_val_832_; 
v_val_832_ = lean_ctor_get(v_fst_831_, 0);
lean_inc(v_val_832_);
lean_dec_ref(v_fst_831_);
return v_val_832_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* v_name_833_, lean_object* v_self_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lake_Workspace_findLeanExe_x3f(v_name_833_, v_self_834_);
lean_dec_ref(v_self_834_);
lean_dec(v_name_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(lean_object* v_name_836_, lean_object* v_as_837_, size_t v_sz_838_, size_t v_i_839_, lean_object* v_b_840_){
_start:
{
lean_object* v_a_842_; uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_lt(v_i_839_, v_sz_838_);
if (v___x_846_ == 0)
{
lean_inc_ref(v_b_840_);
return v_b_840_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_a_849_; lean_object* v___x_850_; 
v___x_847_ = lean_box(0);
v___x_848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_a_849_ = lean_array_uget_borrowed(v_as_837_, v_i_839_);
v___x_850_ = l_Lake_Package_findTargetDecl_x3f(v_name_836_, v_a_849_);
if (lean_obj_tag(v___x_850_) == 0)
{
v_a_842_ = v___x_848_;
goto v___jp_841_;
}
else
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_866_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_866_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_866_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_866_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_name_855_; lean_object* v_kind_856_; lean_object* v_config_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_name_855_ = lean_ctor_get(v_val_851_, 1);
lean_inc(v_name_855_);
v_kind_856_ = lean_ctor_get(v_val_851_, 2);
lean_inc(v_kind_856_);
v_config_857_ = lean_ctor_get(v_val_851_, 3);
lean_inc(v_config_857_);
lean_dec(v_val_851_);
v___x_858_ = l_Lake_ExternLib_keyword;
v___x_859_ = lean_name_eq(v_kind_856_, v___x_858_);
lean_dec(v_kind_856_);
if (v___x_859_ == 0)
{
lean_dec(v_config_857_);
lean_dec(v_name_855_);
lean_del_object(v___x_853_);
v_a_842_ = v___x_848_;
goto v___jp_841_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_inc(v_a_849_);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v_a_849_);
lean_ctor_set(v___x_860_, 1, v_name_855_);
lean_ctor_set(v___x_860_, 2, v_config_857_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_860_);
v___x_862_ = v___x_853_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_865_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_847_);
return v___x_864_;
}
}
}
}
}
v___jp_841_:
{
size_t v___x_843_; size_t v___x_844_; 
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_add(v_i_839_, v___x_843_);
v_i_839_ = v___x_844_;
v_b_840_ = v_a_842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* v_name_867_, lean_object* v_as_868_, lean_object* v_sz_869_, lean_object* v_i_870_, lean_object* v_b_871_){
_start:
{
size_t v_sz_boxed_872_; size_t v_i_boxed_873_; lean_object* v_res_874_; 
v_sz_boxed_872_ = lean_unbox_usize(v_sz_869_);
lean_dec(v_sz_869_);
v_i_boxed_873_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_867_, v_as_868_, v_sz_boxed_872_, v_i_boxed_873_, v_b_871_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_as_868_);
lean_dec(v_name_867_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* v_name_875_, lean_object* v_self_876_){
_start:
{
lean_object* v_packages_877_; lean_object* v___x_878_; lean_object* v___x_879_; size_t v_sz_880_; size_t v___x_881_; lean_object* v___x_882_; lean_object* v_fst_883_; 
v_packages_877_ = lean_ctor_get(v_self_876_, 4);
v___x_878_ = lean_box(0);
v___x_879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0));
v_sz_880_ = lean_array_size(v_packages_877_);
v___x_881_ = ((size_t)0ULL);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_875_, v_packages_877_, v_sz_880_, v___x_881_, v___x_879_);
v_fst_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_fst_883_);
lean_dec_ref(v___x_882_);
if (lean_obj_tag(v_fst_883_) == 0)
{
return v___x_878_;
}
else
{
lean_object* v_val_884_; 
v_val_884_ = lean_ctor_get(v_fst_883_, 0);
lean_inc(v_val_884_);
lean_dec_ref(v_fst_883_);
return v_val_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* v_name_885_, lean_object* v_self_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lake_Workspace_findExternLib_x3f(v_name_885_, v_self_886_);
lean_dec_ref(v_self_886_);
lean_dec(v_name_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* v_a_888_, lean_object* v_f_889_){
_start:
{
if (lean_obj_tag(v_a_888_) == 0)
{
lean_object* v___x_890_; 
lean_dec(v_f_889_);
v___x_890_ = lean_box(0);
return v___x_890_;
}
else
{
lean_object* v_val_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_899_; 
v_val_891_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_899_ == 0)
{
v___x_893_ = v_a_888_;
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_val_891_);
lean_dec(v_a_888_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_899_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_apply_1(v_f_889_, v_val_891_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_895_);
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_a_902_, lean_object* v_f_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v_a_902_, v_f_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* v_a_905_, lean_object* v_x_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_a_905_);
lean_ctor_set(v___x_907_, 1, v_x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* v_name_911_, lean_object* v_as_912_, size_t v_sz_913_, size_t v_i_914_, lean_object* v_b_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = lean_usize_dec_lt(v_i_914_, v_sz_913_);
if (v___x_916_ == 0)
{
lean_inc_ref(v_b_915_);
return v_b_915_;
}
else
{
lean_object* v___x_917_; lean_object* v_a_918_; lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_917_ = lean_box(0);
v_a_918_ = lean_array_uget_borrowed(v_as_912_, v_i_914_);
lean_inc(v_a_918_);
v___f_919_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_919_, 0, v_a_918_);
v___x_920_ = l_Lake_Package_findTargetConfig_x3f(v_name_911_, v_a_918_);
v___x_921_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_920_, v___f_919_);
if (lean_obj_tag(v___x_921_) == 1)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_917_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; size_t v___x_925_; size_t v___x_926_; 
lean_dec(v___x_921_);
v___x_924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_914_, v___x_925_);
v_i_914_ = v___x_926_;
v_b_915_ = v___x_924_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* v_name_928_, lean_object* v_as_929_, lean_object* v_sz_930_, lean_object* v_i_931_, lean_object* v_b_932_){
_start:
{
size_t v_sz_boxed_933_; size_t v_i_boxed_934_; lean_object* v_res_935_; 
v_sz_boxed_933_ = lean_unbox_usize(v_sz_930_);
lean_dec(v_sz_930_);
v_i_boxed_934_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_928_, v_as_929_, v_sz_boxed_933_, v_i_boxed_934_, v_b_932_);
lean_dec_ref(v_b_932_);
lean_dec_ref(v_as_929_);
lean_dec(v_name_928_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* v_name_936_, lean_object* v_self_937_){
_start:
{
lean_object* v_packages_938_; lean_object* v___x_939_; lean_object* v___x_940_; size_t v_sz_941_; size_t v___x_942_; lean_object* v___x_943_; lean_object* v_fst_944_; 
v_packages_938_ = lean_ctor_get(v_self_937_, 4);
v___x_939_ = lean_box(0);
v___x_940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_941_ = lean_array_size(v_packages_938_);
v___x_942_ = ((size_t)0ULL);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_936_, v_packages_938_, v_sz_941_, v___x_942_, v___x_940_);
v_fst_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_fst_944_);
lean_dec_ref(v___x_943_);
if (lean_obj_tag(v_fst_944_) == 0)
{
return v___x_939_;
}
else
{
lean_object* v_val_945_; 
v_val_945_ = lean_ctor_get(v_fst_944_, 0);
lean_inc(v_val_945_);
lean_dec_ref(v_fst_944_);
return v_val_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* v_name_946_, lean_object* v_self_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_946_, v_self_947_);
lean_dec_ref(v_self_947_);
lean_dec(v_name_946_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_a_949_);
lean_ctor_set(v___x_951_, 1, v_x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* v_name_952_, lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_957_ == 0)
{
lean_inc_ref(v_b_956_);
return v_b_956_;
}
else
{
lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___f_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_958_ = lean_box(0);
v_a_959_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
lean_inc(v_a_959_);
v___f_960_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_960_, 0, v_a_959_);
v___x_961_ = l_Lake_Package_findTargetDecl_x3f(v_name_952_, v_a_959_);
v___x_962_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_961_, v___f_960_);
if (lean_obj_tag(v___x_962_) == 1)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_958_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; size_t v___x_966_; size_t v___x_967_; 
lean_dec(v___x_962_);
v___x_965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v___x_966_ = ((size_t)1ULL);
v___x_967_ = lean_usize_add(v_i_955_, v___x_966_);
v_i_955_ = v___x_967_;
v_b_956_ = v___x_965_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* v_name_969_, lean_object* v_as_970_, lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_b_973_){
_start:
{
size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_sz_boxed_974_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_969_, v_as_970_, v_sz_boxed_974_, v_i_boxed_975_, v_b_973_);
lean_dec_ref(v_b_973_);
lean_dec_ref(v_as_970_);
lean_dec(v_name_969_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* v_name_977_, lean_object* v_self_978_){
_start:
{
lean_object* v_packages_979_; lean_object* v___x_980_; lean_object* v___x_981_; size_t v_sz_982_; size_t v___x_983_; lean_object* v___x_984_; lean_object* v_fst_985_; 
v_packages_979_ = lean_ctor_get(v_self_978_, 4);
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0));
v_sz_982_ = lean_array_size(v_packages_979_);
v___x_983_ = ((size_t)0ULL);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_977_, v_packages_979_, v_sz_982_, v___x_983_, v___x_981_);
v_fst_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_985_);
lean_dec_ref(v___x_984_);
if (lean_obj_tag(v_fst_985_) == 0)
{
return v___x_980_;
}
else
{
lean_object* v_val_986_; 
v_val_986_ = lean_ctor_get(v_fst_985_, 0);
lean_inc(v_val_986_);
lean_dec_ref(v_fst_985_);
return v_val_986_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* v_name_987_, lean_object* v_self_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_987_, v_self_988_);
lean_dec_ref(v_self_988_);
lean_dec(v_name_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* v_name_990_, lean_object* v_cfg_991_, lean_object* v_self_992_){
_start:
{
lean_object* v_lakeEnv_993_; lean_object* v_lakeConfig_994_; lean_object* v_lakeCache_995_; lean_object* v_lakeArgs_x3f_996_; lean_object* v_packages_997_; lean_object* v_packageMap_998_; lean_object* v_facetConfigs_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_lakeEnv_993_ = lean_ctor_get(v_self_992_, 0);
v_lakeConfig_994_ = lean_ctor_get(v_self_992_, 1);
v_lakeCache_995_ = lean_ctor_get(v_self_992_, 2);
v_lakeArgs_x3f_996_ = lean_ctor_get(v_self_992_, 3);
v_packages_997_ = lean_ctor_get(v_self_992_, 4);
v_packageMap_998_ = lean_ctor_get(v_self_992_, 5);
v_facetConfigs_999_ = lean_ctor_get(v_self_992_, 6);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_self_992_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1001_ = v_self_992_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_facetConfigs_999_);
lean_inc(v_packageMap_998_);
lean_inc(v_packages_997_);
lean_inc(v_lakeArgs_x3f_996_);
lean_inc(v_lakeCache_995_);
lean_inc(v_lakeConfig_994_);
lean_inc(v_lakeEnv_993_);
lean_dec(v_self_992_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = l_Lake_FacetConfigMap_insert(v_name_990_, v_cfg_991_, v_facetConfigs_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 6, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_lakeEnv_993_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_lakeConfig_994_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_lakeCache_995_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v_lakeArgs_x3f_996_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_packages_997_);
lean_ctor_set(v_reuseFailAlloc_1006_, 5, v_packageMap_998_);
lean_ctor_set(v_reuseFailAlloc_1006_, 6, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* v_name_1008_, lean_object* v_self_1009_){
_start:
{
lean_object* v_facetConfigs_1010_; lean_object* v___x_1011_; 
v_facetConfigs_1010_ = lean_ctor_get(v_self_1009_, 6);
v___x_1011_ = l_Lake_FacetConfigMap_get_x3f(v_name_1008_, v_facetConfigs_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* v_name_1012_, lean_object* v_self_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_1012_, v_self_1013_);
lean_dec_ref(v_self_1013_);
lean_dec(v_name_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* v_name_1015_, lean_object* v_cfg_1016_, lean_object* v_self_1017_){
_start:
{
lean_object* v_lakeEnv_1018_; lean_object* v_lakeConfig_1019_; lean_object* v_lakeCache_1020_; lean_object* v_lakeArgs_x3f_1021_; lean_object* v_packages_1022_; lean_object* v_packageMap_1023_; lean_object* v_facetConfigs_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1032_; 
v_lakeEnv_1018_ = lean_ctor_get(v_self_1017_, 0);
v_lakeConfig_1019_ = lean_ctor_get(v_self_1017_, 1);
v_lakeCache_1020_ = lean_ctor_get(v_self_1017_, 2);
v_lakeArgs_x3f_1021_ = lean_ctor_get(v_self_1017_, 3);
v_packages_1022_ = lean_ctor_get(v_self_1017_, 4);
v_packageMap_1023_ = lean_ctor_get(v_self_1017_, 5);
v_facetConfigs_1024_ = lean_ctor_get(v_self_1017_, 6);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_self_1017_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1026_ = v_self_1017_;
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_facetConfigs_1024_);
lean_inc(v_packageMap_1023_);
lean_inc(v_packages_1022_);
lean_inc(v_lakeArgs_x3f_1021_);
lean_inc(v_lakeCache_1020_);
lean_inc(v_lakeConfig_1019_);
lean_inc(v_lakeEnv_1018_);
lean_dec(v_self_1017_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = l_Lake_FacetConfigMap_insert(v_name_1015_, v_cfg_1016_, v_facetConfigs_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 6, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_lakeEnv_1018_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_lakeConfig_1019_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_lakeCache_1020_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_lakeArgs_x3f_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_packages_1022_);
lean_ctor_set(v_reuseFailAlloc_1031_, 5, v_packageMap_1023_);
lean_ctor_set(v_reuseFailAlloc_1031_, 6, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* v_name_1033_, lean_object* v_self_1034_){
_start:
{
lean_object* v_facetConfigs_1035_; lean_object* v___x_1036_; 
v_facetConfigs_1035_ = lean_ctor_get(v_self_1034_, 6);
v___x_1036_ = l_Lake_FacetConfigMap_get_x3f(v_name_1033_, v_facetConfigs_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
else
{
lean_object* v_val_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_val_1038_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_val_1038_);
lean_dec_ref(v___x_1036_);
v___x_1039_ = l_Lake_Module_keyword;
v___x_1040_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1039_, v_val_1038_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* v_name_1041_, lean_object* v_self_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_1041_, v_self_1042_);
lean_dec_ref(v_self_1042_);
lean_dec(v_name_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* v_name_1044_, lean_object* v_cfg_1045_, lean_object* v_self_1046_){
_start:
{
lean_object* v_lakeEnv_1047_; lean_object* v_lakeConfig_1048_; lean_object* v_lakeCache_1049_; lean_object* v_lakeArgs_x3f_1050_; lean_object* v_packages_1051_; lean_object* v_packageMap_1052_; lean_object* v_facetConfigs_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_lakeEnv_1047_ = lean_ctor_get(v_self_1046_, 0);
v_lakeConfig_1048_ = lean_ctor_get(v_self_1046_, 1);
v_lakeCache_1049_ = lean_ctor_get(v_self_1046_, 2);
v_lakeArgs_x3f_1050_ = lean_ctor_get(v_self_1046_, 3);
v_packages_1051_ = lean_ctor_get(v_self_1046_, 4);
v_packageMap_1052_ = lean_ctor_get(v_self_1046_, 5);
v_facetConfigs_1053_ = lean_ctor_get(v_self_1046_, 6);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_self_1046_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v_self_1046_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_facetConfigs_1053_);
lean_inc(v_packageMap_1052_);
lean_inc(v_packages_1051_);
lean_inc(v_lakeArgs_x3f_1050_);
lean_inc(v_lakeCache_1049_);
lean_inc(v_lakeConfig_1048_);
lean_inc(v_lakeEnv_1047_);
lean_dec(v_self_1046_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lake_FacetConfigMap_insert(v_name_1044_, v_cfg_1045_, v_facetConfigs_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 6, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_lakeEnv_1047_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_lakeConfig_1048_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_lakeCache_1049_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_lakeArgs_x3f_1050_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_packages_1051_);
lean_ctor_set(v_reuseFailAlloc_1060_, 5, v_packageMap_1052_);
lean_ctor_set(v_reuseFailAlloc_1060_, 6, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* v_name_1062_, lean_object* v_self_1063_){
_start:
{
lean_object* v_facetConfigs_1064_; lean_object* v___x_1065_; 
v_facetConfigs_1064_ = lean_ctor_get(v_self_1063_, 6);
v___x_1065_ = l_Lake_FacetConfigMap_get_x3f(v_name_1062_, v_facetConfigs_1064_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_box(0);
return v___x_1066_;
}
else
{
lean_object* v_val_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_val_1067_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_val_1067_);
lean_dec_ref(v___x_1065_);
v___x_1068_ = l_Lake_Package_keyword;
v___x_1069_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1068_, v_val_1067_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* v_name_1070_, lean_object* v_self_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_1070_, v_self_1071_);
lean_dec_ref(v_self_1071_);
lean_dec(v_name_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* v_name_1073_, lean_object* v_cfg_1074_, lean_object* v_self_1075_){
_start:
{
lean_object* v_lakeEnv_1076_; lean_object* v_lakeConfig_1077_; lean_object* v_lakeCache_1078_; lean_object* v_lakeArgs_x3f_1079_; lean_object* v_packages_1080_; lean_object* v_packageMap_1081_; lean_object* v_facetConfigs_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_lakeEnv_1076_ = lean_ctor_get(v_self_1075_, 0);
v_lakeConfig_1077_ = lean_ctor_get(v_self_1075_, 1);
v_lakeCache_1078_ = lean_ctor_get(v_self_1075_, 2);
v_lakeArgs_x3f_1079_ = lean_ctor_get(v_self_1075_, 3);
v_packages_1080_ = lean_ctor_get(v_self_1075_, 4);
v_packageMap_1081_ = lean_ctor_get(v_self_1075_, 5);
v_facetConfigs_1082_ = lean_ctor_get(v_self_1075_, 6);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_self_1075_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1084_ = v_self_1075_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_facetConfigs_1082_);
lean_inc(v_packageMap_1081_);
lean_inc(v_packages_1080_);
lean_inc(v_lakeArgs_x3f_1079_);
lean_inc(v_lakeCache_1078_);
lean_inc(v_lakeConfig_1077_);
lean_inc(v_lakeEnv_1076_);
lean_dec(v_self_1075_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = l_Lake_FacetConfigMap_insert(v_name_1073_, v_cfg_1074_, v_facetConfigs_1082_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 6, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_lakeEnv_1076_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_lakeConfig_1077_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_lakeCache_1078_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_lakeArgs_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_packages_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v_packageMap_1081_);
lean_ctor_set(v_reuseFailAlloc_1089_, 6, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* v_name_1091_, lean_object* v_self_1092_){
_start:
{
lean_object* v_facetConfigs_1093_; lean_object* v___x_1094_; 
v_facetConfigs_1093_ = lean_ctor_get(v_self_1092_, 6);
v___x_1094_ = l_Lake_FacetConfigMap_get_x3f(v_name_1091_, v_facetConfigs_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
else
{
lean_object* v_val_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_val_1096_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_val_1096_);
lean_dec_ref(v___x_1094_);
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1098_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_1097_, v_val_1096_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* v_name_1099_, lean_object* v_self_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_1099_, v_self_1100_);
lean_dec_ref(v_self_1100_);
lean_dec(v_name_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(lean_object* v_as_1102_, size_t v_i_1103_, size_t v_stop_1104_, lean_object* v_b_1105_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_usize_dec_eq(v_i_1103_, v_stop_1104_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v_config_1108_; lean_object* v_dir_1109_; lean_object* v_buildDir_1110_; lean_object* v_binDir_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; 
v___x_1107_ = lean_array_uget_borrowed(v_as_1102_, v_i_1103_);
v_config_1108_ = lean_ctor_get(v___x_1107_, 6);
v_dir_1109_ = lean_ctor_get(v___x_1107_, 4);
v_buildDir_1110_ = lean_ctor_get(v_config_1108_, 5);
v_binDir_1111_ = lean_ctor_get(v_config_1108_, 8);
lean_inc_ref(v_buildDir_1110_);
v___x_1112_ = l_System_FilePath_normalize(v_buildDir_1110_);
lean_inc_ref(v_dir_1109_);
v___x_1113_ = l_Lake_joinRelative(v_dir_1109_, v___x_1112_);
lean_inc_ref(v_binDir_1111_);
v___x_1114_ = l_System_FilePath_normalize(v_binDir_1111_);
v___x_1115_ = l_Lake_joinRelative(v___x_1113_, v___x_1114_);
v___x_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_b_1105_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_add(v_i_1103_, v___x_1117_);
v_i_1103_ = v___x_1118_;
v_b_1105_ = v___x_1116_;
goto _start;
}
else
{
return v_b_1105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(lean_object* v_as_1120_, lean_object* v_i_1121_, lean_object* v_stop_1122_, lean_object* v_b_1123_){
_start:
{
size_t v_i_boxed_1124_; size_t v_stop_boxed_1125_; lean_object* v_res_1126_; 
v_i_boxed_1124_ = lean_unbox_usize(v_i_1121_);
lean_dec(v_i_1121_);
v_stop_boxed_1125_ = lean_unbox_usize(v_stop_1122_);
lean_dec(v_stop_1122_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_1120_, v_i_boxed_1124_, v_stop_boxed_1125_, v_b_1123_);
lean_dec_ref(v_as_1120_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* v_self_1127_){
_start:
{
lean_object* v_packages_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_packages_1128_ = lean_ctor_get(v_self_1127_, 4);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_array_get_size(v_packages_1128_);
v___x_1132_ = lean_nat_dec_lt(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
return v___x_1129_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_le(v___x_1131_, v___x_1131_);
if (v___x_1133_ == 0)
{
if (v___x_1132_ == 0)
{
return v___x_1129_;
}
else
{
size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = ((size_t)0ULL);
v___x_1135_ = lean_usize_of_nat(v___x_1131_);
v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1128_, v___x_1134_, v___x_1135_, v___x_1129_);
return v___x_1136_;
}
}
else
{
size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = lean_usize_of_nat(v___x_1131_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_1128_, v___x_1137_, v___x_1138_, v___x_1129_);
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* v_self_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lake_Workspace_binPath(v_self_1140_);
lean_dec_ref(v_self_1140_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(lean_object* v_as_1142_, size_t v_i_1143_, size_t v_stop_1144_, lean_object* v_b_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_eq(v_i_1143_, v_stop_1144_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v_config_1148_; lean_object* v_dir_1149_; lean_object* v_buildDir_1150_; lean_object* v_leanLibDir_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; size_t v___x_1157_; size_t v___x_1158_; 
v___x_1147_ = lean_array_uget_borrowed(v_as_1142_, v_i_1143_);
v_config_1148_ = lean_ctor_get(v___x_1147_, 6);
v_dir_1149_ = lean_ctor_get(v___x_1147_, 4);
v_buildDir_1150_ = lean_ctor_get(v_config_1148_, 5);
v_leanLibDir_1151_ = lean_ctor_get(v_config_1148_, 6);
lean_inc_ref(v_buildDir_1150_);
v___x_1152_ = l_System_FilePath_normalize(v_buildDir_1150_);
lean_inc_ref(v_dir_1149_);
v___x_1153_ = l_Lake_joinRelative(v_dir_1149_, v___x_1152_);
lean_inc_ref(v_leanLibDir_1151_);
v___x_1154_ = l_System_FilePath_normalize(v_leanLibDir_1151_);
v___x_1155_ = l_Lake_joinRelative(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v_b_1145_);
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_add(v_i_1143_, v___x_1157_);
v_i_1143_ = v___x_1158_;
v_b_1145_ = v___x_1156_;
goto _start;
}
else
{
return v_b_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(lean_object* v_as_1160_, lean_object* v_i_1161_, lean_object* v_stop_1162_, lean_object* v_b_1163_){
_start:
{
size_t v_i_boxed_1164_; size_t v_stop_boxed_1165_; lean_object* v_res_1166_; 
v_i_boxed_1164_ = lean_unbox_usize(v_i_1161_);
lean_dec(v_i_1161_);
v_stop_boxed_1165_ = lean_unbox_usize(v_stop_1162_);
lean_dec(v_stop_1162_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_1160_, v_i_boxed_1164_, v_stop_boxed_1165_, v_b_1163_);
lean_dec_ref(v_as_1160_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* v_self_1167_){
_start:
{
lean_object* v_packages_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_packages_1168_ = lean_ctor_get(v_self_1167_, 4);
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_array_get_size(v_packages_1168_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
return v___x_1169_;
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_le(v___x_1171_, v___x_1171_);
if (v___x_1173_ == 0)
{
if (v___x_1172_ == 0)
{
return v___x_1169_;
}
else
{
size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = lean_usize_of_nat(v___x_1171_);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1168_, v___x_1174_, v___x_1175_, v___x_1169_);
return v___x_1176_;
}
}
else
{
size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = ((size_t)0ULL);
v___x_1178_ = lean_usize_of_nat(v___x_1171_);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_1168_, v___x_1177_, v___x_1178_, v___x_1169_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* v_self_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lake_Workspace_leanPath(v_self_1180_);
lean_dec_ref(v_self_1180_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(lean_object* v_x2_1182_, lean_object* v_as_1183_, size_t v_i_1184_, size_t v_stop_1185_, lean_object* v_b_1186_){
_start:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_usize_dec_eq(v_i_1184_, v_stop_1185_);
if (v___x_1187_ == 0)
{
size_t v___x_1188_; size_t v___x_1189_; lean_object* v___x_1190_; lean_object* v_kind_1191_; lean_object* v_config_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_sub(v_i_1184_, v___x_1188_);
v___x_1190_ = lean_array_uget_borrowed(v_as_1183_, v___x_1189_);
v_kind_1191_ = lean_ctor_get(v___x_1190_, 2);
v_config_1192_ = lean_ctor_get(v___x_1190_, 3);
v___x_1193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2));
v___x_1194_ = lean_name_eq(v_kind_1191_, v___x_1193_);
if (v___x_1194_ == 0)
{
v_i_1184_ = v___x_1189_;
goto _start;
}
else
{
lean_object* v_config_1196_; lean_object* v_dir_1197_; lean_object* v_srcDir_1198_; lean_object* v_srcDir_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_config_1196_ = lean_ctor_get(v_x2_1182_, 6);
v_dir_1197_ = lean_ctor_get(v_x2_1182_, 4);
v_srcDir_1198_ = lean_ctor_get(v_config_1196_, 4);
v_srcDir_1199_ = lean_ctor_get(v_config_1192_, 1);
lean_inc_ref(v_srcDir_1198_);
v___x_1200_ = l_System_FilePath_normalize(v_srcDir_1198_);
lean_inc_ref(v_dir_1197_);
v___x_1201_ = l_Lake_joinRelative(v_dir_1197_, v___x_1200_);
lean_inc_ref(v_srcDir_1199_);
v___x_1202_ = l_Lake_joinRelative(v___x_1201_, v_srcDir_1199_);
v___x_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v_b_1186_);
v_i_1184_ = v___x_1189_;
v_b_1186_ = v___x_1203_;
goto _start;
}
}
else
{
lean_dec_ref(v_x2_1182_);
return v_b_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* v_x2_1205_, lean_object* v_as_1206_, lean_object* v_i_1207_, lean_object* v_stop_1208_, lean_object* v_b_1209_){
_start:
{
size_t v_i_boxed_1210_; size_t v_stop_boxed_1211_; lean_object* v_res_1212_; 
v_i_boxed_1210_ = lean_unbox_usize(v_i_1207_);
lean_dec(v_i_1207_);
v_stop_boxed_1211_ = lean_unbox_usize(v_stop_1208_);
lean_dec(v_stop_1208_);
v_res_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_1205_, v_as_1206_, v_i_boxed_1210_, v_stop_boxed_1211_, v_b_1209_);
lean_dec_ref(v_as_1206_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(lean_object* v_as_1213_, size_t v_i_1214_, size_t v_stop_1215_, lean_object* v_b_1216_){
_start:
{
lean_object* v___y_1218_; uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_eq(v_i_1214_, v_stop_1215_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v_targetDecls_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1223_ = lean_array_uget_borrowed(v_as_1213_, v_i_1214_);
v_targetDecls_1224_ = lean_ctor_get(v___x_1223_, 14);
v___x_1225_ = lean_array_get_size(v_targetDecls_1224_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_nat_dec_lt(v___x_1226_, v___x_1225_);
if (v___x_1227_ == 0)
{
v___y_1218_ = v_b_1216_;
goto v___jp_1217_;
}
else
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_usize_of_nat(v___x_1225_);
v___x_1229_ = ((size_t)0ULL);
lean_inc(v___x_1223_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_1223_, v_targetDecls_1224_, v___x_1228_, v___x_1229_, v_b_1216_);
v___y_1218_ = v___x_1230_;
goto v___jp_1217_;
}
}
else
{
return v_b_1216_;
}
v___jp_1217_:
{
size_t v___x_1219_; size_t v___x_1220_; 
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_add(v_i_1214_, v___x_1219_);
v_i_1214_ = v___x_1220_;
v_b_1216_ = v___y_1218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* v_as_1231_, lean_object* v_i_1232_, lean_object* v_stop_1233_, lean_object* v_b_1234_){
_start:
{
size_t v_i_boxed_1235_; size_t v_stop_boxed_1236_; lean_object* v_res_1237_; 
v_i_boxed_1235_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_stop_boxed_1236_ = lean_unbox_usize(v_stop_1233_);
lean_dec(v_stop_1233_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_1231_, v_i_boxed_1235_, v_stop_boxed_1236_, v_b_1234_);
lean_dec_ref(v_as_1231_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* v_self_1238_){
_start:
{
lean_object* v_packages_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_packages_1239_ = lean_ctor_get(v_self_1238_, 4);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_array_get_size(v_packages_1239_);
v___x_1243_ = lean_nat_dec_lt(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
return v___x_1240_;
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_nat_dec_le(v___x_1242_, v___x_1242_);
if (v___x_1244_ == 0)
{
if (v___x_1243_ == 0)
{
return v___x_1240_;
}
else
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = lean_usize_of_nat(v___x_1242_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1239_, v___x_1245_, v___x_1246_, v___x_1240_);
return v___x_1247_;
}
}
else
{
size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = lean_usize_of_nat(v___x_1242_);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_1239_, v___x_1248_, v___x_1249_, v___x_1240_);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* v_self_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lake_Workspace_leanSrcPath(v_self_1251_);
lean_dec_ref(v_self_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(lean_object* v_as_1253_, size_t v_i_1254_, size_t v_stop_1255_, lean_object* v_b_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_eq(v_i_1254_, v_stop_1255_);
if (v___x_1257_ == 0)
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; lean_object* v_config_1261_; lean_object* v_dir_1262_; lean_object* v_buildDir_1263_; lean_object* v_nativeLibDir_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_sub(v_i_1254_, v___x_1258_);
v___x_1260_ = lean_array_uget_borrowed(v_as_1253_, v___x_1259_);
v_config_1261_ = lean_ctor_get(v___x_1260_, 6);
v_dir_1262_ = lean_ctor_get(v___x_1260_, 4);
v_buildDir_1263_ = lean_ctor_get(v_config_1261_, 5);
v_nativeLibDir_1264_ = lean_ctor_get(v_config_1261_, 7);
lean_inc_ref(v_buildDir_1263_);
v___x_1265_ = l_System_FilePath_normalize(v_buildDir_1263_);
lean_inc_ref(v_dir_1262_);
v___x_1266_ = l_Lake_joinRelative(v_dir_1262_, v___x_1265_);
lean_inc_ref(v_nativeLibDir_1264_);
v___x_1267_ = l_System_FilePath_normalize(v_nativeLibDir_1264_);
v___x_1268_ = l_Lake_joinRelative(v___x_1266_, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v_b_1256_);
v_i_1254_ = v___x_1259_;
v_b_1256_ = v___x_1269_;
goto _start;
}
else
{
return v_b_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* v_as_1271_, lean_object* v_i_1272_, lean_object* v_stop_1273_, lean_object* v_b_1274_){
_start:
{
size_t v_i_boxed_1275_; size_t v_stop_boxed_1276_; lean_object* v_res_1277_; 
v_i_boxed_1275_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_stop_boxed_1276_ = lean_unbox_usize(v_stop_1273_);
lean_dec(v_stop_1273_);
v_res_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_1271_, v_i_boxed_1275_, v_stop_boxed_1276_, v_b_1274_);
lean_dec_ref(v_as_1271_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* v_self_1278_){
_start:
{
lean_object* v_packages_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_packages_1279_ = lean_ctor_get(v_self_1278_, 4);
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_array_get_size(v_packages_1279_);
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_nat_dec_lt(v___x_1282_, v___x_1281_);
if (v___x_1283_ == 0)
{
return v___x_1280_;
}
else
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_usize_of_nat(v___x_1281_);
v___x_1285_ = ((size_t)0ULL);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_1279_, v___x_1284_, v___x_1285_, v___x_1280_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* v_self_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lake_Workspace_sharedLibPath(v_self_1287_);
lean_dec_ref(v_self_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* v_self_1289_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = l_System_Platform_isWindows;
if (v___x_1290_ == 0)
{
lean_object* v_lakeEnv_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_lakeEnv_1291_ = lean_ctor_get(v_self_1289_, 0);
v___x_1292_ = l_Lake_Workspace_binPath(v_self_1289_);
v___x_1293_ = l_Lake_Env_path(v_lakeEnv_1291_);
v___x_1294_ = l_List_appendTR___redArg(v___x_1292_, v___x_1293_);
return v___x_1294_;
}
else
{
lean_object* v_lakeEnv_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_lakeEnv_1295_ = lean_ctor_get(v_self_1289_, 0);
v___x_1296_ = l_Lake_Workspace_binPath(v_self_1289_);
v___x_1297_ = l_Lake_Workspace_sharedLibPath(v_self_1289_);
v___x_1298_ = l_List_appendTR___redArg(v___x_1296_, v___x_1297_);
v___x_1299_ = l_Lake_Env_path(v_lakeEnv_1295_);
v___x_1300_ = l_List_appendTR___redArg(v___x_1298_, v___x_1299_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* v_self_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lake_Workspace_augmentedPath(v_self_1301_);
lean_dec_ref(v_self_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* v_self_1303_){
_start:
{
lean_object* v_lakeEnv_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_lakeEnv_1304_ = lean_ctor_get(v_self_1303_, 0);
v___x_1305_ = l_Lake_Workspace_leanPath(v_self_1303_);
v___x_1306_ = l_Lake_Env_leanPath(v_lakeEnv_1304_);
v___x_1307_ = l_List_appendTR___redArg(v___x_1305_, v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* v_self_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lake_Workspace_augmentedLeanPath(v_self_1308_);
lean_dec_ref(v_self_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* v_self_1310_){
_start:
{
lean_object* v_lakeEnv_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_lakeEnv_1311_ = lean_ctor_get(v_self_1310_, 0);
v___x_1312_ = l_Lake_Workspace_leanSrcPath(v_self_1310_);
v___x_1313_ = l_Lake_Env_leanSrcPath(v_lakeEnv_1311_);
v___x_1314_ = l_List_appendTR___redArg(v___x_1312_, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* v_self_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1315_);
lean_dec_ref(v_self_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* v_self_1317_){
_start:
{
lean_object* v_lakeEnv_1318_; lean_object* v_lean_1319_; lean_object* v_initSharedLibPath_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_lakeEnv_1318_ = lean_ctor_get(v_self_1317_, 0);
v_lean_1319_ = lean_ctor_get(v_lakeEnv_1318_, 1);
v_initSharedLibPath_1320_ = lean_ctor_get(v_lakeEnv_1318_, 16);
lean_inc(v_initSharedLibPath_1320_);
v___x_1321_ = l_Lake_LeanInstall_sharedLibPath(v_lean_1319_);
v___x_1322_ = l_Lake_Workspace_sharedLibPath(v_self_1317_);
lean_dec_ref(v_self_1317_);
v___x_1323_ = l_List_appendTR___redArg(v___x_1321_, v___x_1322_);
v___x_1324_ = l_List_appendTR___redArg(v___x_1323_, v_initSharedLibPath_1320_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* v_self_1340_){
_start:
{
lean_object* v_lakeEnv_1341_; lean_object* v_lakeCache_1342_; lean_object* v_packages_1343_; lean_object* v_enableArtifactCache_x3f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___x_1377_; lean_object* v___y_1379_; uint8_t v_val_1400_; 
v_lakeEnv_1341_ = lean_ctor_get(v_self_1340_, 0);
v_lakeCache_1342_ = lean_ctor_get(v_self_1340_, 2);
v_packages_1343_ = lean_ctor_get(v_self_1340_, 4);
v_enableArtifactCache_x3f_1344_ = lean_ctor_get(v_lakeEnv_1341_, 6);
lean_inc_ref(v_lakeEnv_1341_);
v___x_1345_ = l_Lake_Env_baseVars(v_lakeEnv_1341_);
v___x_1346_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__0));
lean_inc_ref(v_lakeCache_1342_);
v___x_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_lakeCache_1342_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1377_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__2));
if (lean_obj_tag(v_enableArtifactCache_x3f_1344_) == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_config_1405_; lean_object* v_enableArtifactCache_x3f_1406_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_array_fget_borrowed(v_packages_1343_, v___x_1403_);
v_config_1405_ = lean_ctor_get(v___x_1404_, 6);
v_enableArtifactCache_x3f_1406_ = lean_ctor_get(v_config_1405_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_1406_) == 1)
{
lean_object* v_val_1407_; uint8_t v___x_1408_; 
v_val_1407_ = lean_ctor_get(v_enableArtifactCache_x3f_1406_, 0);
v___x_1408_ = lean_unbox(v_val_1407_);
v_val_1400_ = v___x_1408_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1409_; 
v___x_1409_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__11));
v___y_1379_ = v___x_1409_;
goto v___jp_1378_;
}
}
else
{
lean_object* v_val_1410_; uint8_t v___x_1411_; 
v_val_1410_ = lean_ctor_get(v_enableArtifactCache_x3f_1344_, 0);
v___x_1411_ = lean_unbox(v_val_1410_);
v_val_1400_ = v___x_1411_;
goto v___jp_1399_;
}
v___jp_1349_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_vars_1369_; uint8_t v___x_1370_; 
lean_inc_ref(v___y_1351_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___y_1351_);
lean_ctor_set(v___x_1355_, 1, v___y_1354_);
v___x_1356_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__1));
v___x_1357_ = l_Lake_Workspace_augmentedPath(v_self_1340_);
v___x_1358_ = l_System_SearchPath_toString(v___x_1357_);
v___x_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1356_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(6u);
v___x_1362_ = lean_mk_empty_array_with_capacity(v___x_1361_);
v___x_1363_ = lean_array_push(v___x_1362_, v___x_1348_);
v___x_1364_ = lean_array_push(v___x_1363_, v___y_1350_);
v___x_1365_ = lean_array_push(v___x_1364_, v___y_1353_);
v___x_1366_ = lean_array_push(v___x_1365_, v___y_1352_);
v___x_1367_ = lean_array_push(v___x_1366_, v___x_1355_);
v___x_1368_ = lean_array_push(v___x_1367_, v___x_1360_);
v_vars_1369_ = l_Array_append___redArg(v___x_1345_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = l_System_Platform_isWindows;
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1371_ = l_Lake_sharedLibPathEnvVar;
v___x_1372_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_1340_);
v___x_1373_ = l_System_SearchPath_toString(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1371_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_array_push(v_vars_1369_, v___x_1375_);
return v___x_1376_;
}
else
{
lean_dec_ref(v_self_1340_);
return v_vars_1369_;
}
}
v___jp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_config_1382_; uint8_t v_bootstrap_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_array_fget_borrowed(v_packages_1343_, v___x_1380_);
v_config_1382_ = lean_ctor_get(v___x_1381_, 6);
v_bootstrap_1383_ = lean_ctor_get_uint8(v_config_1382_, sizeof(void*)*27);
lean_inc(v___y_1379_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1377_);
lean_ctor_set(v___x_1384_, 1, v___y_1379_);
v___x_1385_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__3));
v___x_1386_ = l_Lake_Workspace_augmentedLeanPath(v_self_1340_);
v___x_1387_ = l_System_SearchPath_toString(v___x_1386_);
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1385_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__4));
v___x_1391_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_1340_);
v___x_1392_ = l_System_SearchPath_toString(v___x_1391_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1390_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__5));
if (v_bootstrap_1383_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = l_Lake_Env_leanGithash(v_lakeEnv_1341_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___y_1350_ = v___x_1384_;
v___y_1351_ = v___x_1395_;
v___y_1352_ = v___x_1394_;
v___y_1353_ = v___x_1389_;
v___y_1354_ = v___x_1397_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_box(0);
v___y_1350_ = v___x_1384_;
v___y_1351_ = v___x_1395_;
v___y_1352_ = v___x_1394_;
v___y_1353_ = v___x_1389_;
v___y_1354_ = v___x_1398_;
goto v___jp_1349_;
}
}
v___jp_1399_:
{
if (v_val_1400_ == 0)
{
lean_object* v___x_1401_; 
v___x_1401_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__7));
v___y_1379_ = v___x_1401_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1402_; 
v___x_1402_ = ((lean_object*)(l_Lake_Workspace_augmentedEnvVars___closed__9));
v___y_1379_ = v___x_1402_;
goto v___jp_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(lean_object* v_as_1412_, size_t v_i_1413_, size_t v_stop_1414_, lean_object* v_b_1415_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_eq(v_i_1413_, v_stop_1414_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_array_uget_borrowed(v_as_1412_, v_i_1413_);
lean_inc(v___x_1418_);
v___x_1419_ = l_Lake_Package_clean(v___x_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; size_t v___x_1421_; size_t v___x_1422_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1413_, v___x_1421_);
v_i_1413_ = v___x_1422_;
v_b_1415_ = v_a_1420_;
goto _start;
}
else
{
return v___x_1419_;
}
}
else
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_b_1415_);
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(lean_object* v_as_1425_, lean_object* v_i_1426_, lean_object* v_stop_1427_, lean_object* v_b_1428_, lean_object* v___y_1429_){
_start:
{
size_t v_i_boxed_1430_; size_t v_stop_boxed_1431_; lean_object* v_res_1432_; 
v_i_boxed_1430_ = lean_unbox_usize(v_i_1426_);
lean_dec(v_i_1426_);
v_stop_boxed_1431_ = lean_unbox_usize(v_stop_1427_);
lean_dec(v_stop_1427_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_1425_, v_i_boxed_1430_, v_stop_boxed_1431_, v_b_1428_);
lean_dec_ref(v_as_1425_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* v_self_1433_){
_start:
{
lean_object* v_packages_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_packages_1435_ = lean_ctor_get(v_self_1433_, 4);
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_array_get_size(v_packages_1435_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_nat_dec_lt(v___x_1436_, v___x_1437_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
return v___x_1440_;
}
else
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_le(v___x_1437_, v___x_1437_);
if (v___x_1441_ == 0)
{
if (v___x_1439_ == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1438_);
return v___x_1442_;
}
else
{
size_t v___x_1443_; size_t v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = ((size_t)0ULL);
v___x_1444_ = lean_usize_of_nat(v___x_1437_);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1435_, v___x_1443_, v___x_1444_, v___x_1438_);
return v___x_1445_;
}
}
else
{
size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = lean_usize_of_nat(v___x_1437_);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_1435_, v___x_1446_, v___x_1447_, v___x_1438_);
return v___x_1448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* v_self_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lake_Workspace_clean(v_self_1449_);
lean_dec_ref(v_self_1449_);
return v_res_1451_;
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

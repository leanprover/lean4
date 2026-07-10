// Lean compiler output
// Module: Lake.Config.Monad
// Imports: public import Lake.Config.Workspace
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
lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* l_Lake_Env_sharedLibPath(lean_object*);
lean_object* l_Lake_Cache_getArtifact_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object*);
lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
lean_object* l_Lake_Workspace_findModules(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object*);
lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Workspace_leanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLakeContext(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLakeContext___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0 = (const lean_object*)&l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Context_workspace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Context_workspace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0 = (const lean_object*)&l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0 = (const lean_object*)&l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getRootPackage___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getRootPackage___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getRootPackage___redArg___closed__0 = (const lean_object*)&l_Lake_getRootPackage___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getRootPackage(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0_value),((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7_value),((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2_value),((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3_value),((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4_value),((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8_value),((lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10 = (const lean_object*)&l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModule_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModules___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModules___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModules___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModules(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getServerOptions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getServerOptions___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getServerOptions___redArg___closed__0 = (const lean_object*)&l_Lake_getServerOptions___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getServerOptions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanOptions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanOptions___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanOptions___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanOptions___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanOptions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanArgs___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanArgs___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanArgs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanArgs(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getLeanPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Workspace_leanPath___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanPath___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getLeanSrcPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Workspace_leanSrcPath___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanSrcPath___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanSrcPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getSharedLibPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Workspace_sharedLibPath___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getSharedLibPath___redArg___closed__0 = (const lean_object*)&l_Lake_getSharedLibPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getAugmentedLeanPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Workspace_augmentedLeanPath___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getAugmentedLeanPath___redArg___closed__0 = (const lean_object*)&l_Lake_getAugmentedLeanPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getAugmentedLeanSrcPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Workspace_augmentedLeanSrcPath___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getAugmentedLeanSrcPath___redArg___closed__0 = (const lean_object*)&l_Lake_getAugmentedLeanSrcPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getAugmentedSharedLibPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Workspace_augmentedSharedLibPath, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getAugmentedSharedLibPath___redArg___closed__0 = (const lean_object*)&l_Lake_getAugmentedSharedLibPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getAugmentedEnv___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Workspace_augmentedEnvVars, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getAugmentedEnv___redArg___closed__0 = (const lean_object*)&l_Lake_getAugmentedEnv___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLakeCache___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLakeCache___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLakeCache___redArg___closed__0 = (const lean_object*)&l_Lake_getLakeCache___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_restoreAllArtifacts___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getNoCache___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getNoCache___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getNoCache___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getNoCache___redArg___closed__0 = (const lean_object*)&l_Lake_getNoCache___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getTryCache___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getTryCache___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getTryCache___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getTryCache___redArg___closed__0 = (const lean_object*)&l_Lake_getTryCache___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTryCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getPkgUrlMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getPkgUrlMap___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getPkgUrlMap___redArg___closed__0 = (const lean_object*)&l_Lake_getPkgUrlMap___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getElanToolchain___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getElanToolchain___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getElanToolchain___redArg___closed__0 = (const lean_object*)&l_Lake_getElanToolchain___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getEnvLeanPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Env_leanPath___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getEnvLeanPath___redArg___closed__0 = (const lean_object*)&l_Lake_getEnvLeanPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getEnvLeanSrcPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Env_leanSrcPath___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getEnvLeanSrcPath___redArg___closed__0 = (const lean_object*)&l_Lake_getEnvLeanSrcPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getEnvSharedLibPath___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Env_sharedLibPath, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getEnvSharedLibPath___redArg___closed__0 = (const lean_object*)&l_Lake_getEnvSharedLibPath___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getElanInstall_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getElanInstall_x3f___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getElanInstall_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getElanInstall_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_getElanHome_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getElanHome_x3f___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getElanHome_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getElanHome_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lake_getElan_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getElan_x3f___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getElan_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getElan_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanInstall___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanInstall___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanInstall___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanInstall___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanSysroot___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanSysroot___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanSysroot___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanSysroot___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanSrcDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanSrcDir___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanSrcDir___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanSrcDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanLibDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanLibDir___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanLibDir___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanLibDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanIncludeDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanIncludeDir___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanIncludeDir___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanIncludeDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanSystemLibDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanSystemLibDir___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanSystemLibDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLean___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLean___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLean___redArg___closed__0 = (const lean_object*)&l_Lake_getLean___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLean___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanir___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanir___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanc___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanc___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanc___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeantar___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeantar___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeantar___redArg___closed__0 = (const lean_object*)&l_Lake_getLeantar___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeantar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanSharedDynlib___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanSharedDynlib___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanSharedDynlib___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanSharedDynlib___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanSharedDynlibs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanSharedDynlibs___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanSharedDynlibs___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanSharedDynlibs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanSharedLib___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanSharedLib___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanSharedLib___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanSharedLib___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanAr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanAr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanAr___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanAr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanCc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanCc___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanCc___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanCc___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_getLeanCc_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanInstall_leanCc_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanCc_x3f___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanCc_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLeanLinkSharedFlags___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLeanLinkSharedFlags___redArg___closed__0 = (const lean_object*)&l_Lake_getLeanLinkSharedFlags___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLakeInstall___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLakeInstall___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLakeInstall___redArg___closed__0 = (const lean_object*)&l_Lake_getLakeInstall___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLakeHome___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLakeHome___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLakeHome___redArg___closed__0 = (const lean_object*)&l_Lake_getLakeHome___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLakeSrcDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLakeSrcDir___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLakeSrcDir___redArg___closed__0 = (const lean_object*)&l_Lake_getLakeSrcDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLakeLibDir___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLakeLibDir___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLakeLibDir___redArg___closed__0 = (const lean_object*)&l_Lake_getLakeLibDir___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLake___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLake___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLake___redArg___closed__0 = (const lean_object*)&l_Lake_getLake___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLake___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run___redArg(lean_object* v_env_1_, lean_object* v_self_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_self_2_, v_env_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run(lean_object* v_m_4_, lean_object* v_00_u03b1_5_, lean_object* v_env_6_, lean_object* v_self_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_self_7_, v_env_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg(lean_object* v_inst_9_){
_start:
{
lean_inc(v_inst_9_);
return v_inst_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg___boxed(lean_object* v_inst_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg(v_inst_10_);
lean_dec(v_inst_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace(lean_object* v_m_12_, lean_object* v_inst_13_){
_start:
{
lean_inc(v_inst_13_);
return v_inst_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___boxed(lean_object* v_m_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace(v_m_14_, v_inst_15_);
lean_dec(v_inst_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg(lean_object* v_inst_17_){
_start:
{
lean_object* v_get_18_; 
v_get_18_ = lean_ctor_get(v_inst_17_, 0);
lean_inc(v_get_18_);
return v_get_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg___boxed(lean_object* v_inst_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg(v_inst_19_);
lean_dec_ref(v_inst_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace(lean_object* v_m_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_get_23_; 
v_get_23_ = lean_ctor_get(v_inst_22_, 0);
lean_inc(v_get_23_);
return v_get_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___boxed(lean_object* v_m_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace(v_m_24_, v_inst_25_);
lean_dec_ref(v_inst_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLakeContext(lean_object* v_ws_27_){
_start:
{
lean_inc_ref(v_ws_27_);
return v_ws_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLakeContext___boxed(lean_object* v_ws_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_mkLakeContext(v_ws_28_);
lean_dec_ref(v_ws_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT___redArg(lean_object* v_ws_30_, lean_object* v_x_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_1(v_x_31_, v_ws_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT(lean_object* v_m_33_, lean_object* v_00_u03b1_34_, lean_object* v_ws_35_, lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_apply_1(v_x_36_, v_ws_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0(lean_object* v_x_38_){
_start:
{
lean_inc_ref(v_x_38_);
return v_x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed(lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0(v_x_39_);
lean_dec_ref(v_x_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(lean_object* v_inst_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_map_44_; lean_object* v___f_45_; lean_object* v___x_46_; 
v_map_44_ = lean_ctor_get(v_inst_43_, 0);
lean_inc(v_map_44_);
lean_dec_ref(v_inst_43_);
v___f_45_ = ((lean_object*)(l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0));
v___x_46_ = lean_apply_4(v_map_44_, lean_box(0), lean_box(0), v___f_45_, v_inst_42_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor(lean_object* v_m_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v_inst_48_, v_inst_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_Context_workspace(lean_object* v_self_51_){
_start:
{
lean_inc(v_self_51_);
return v_self_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Context_workspace___boxed(lean_object* v_self_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lake_Context_workspace(v_self_52_);
lean_dec(v_self_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0(lean_object* v_x_54_){
_start:
{
lean_inc(v_x_54_);
return v_x_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0___boxed(lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0(v_x_55_);
lean_dec(v_x_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(lean_object* v_inst_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v_map_60_; lean_object* v___f_61_; lean_object* v___x_62_; 
v_map_60_ = lean_ctor_get(v_inst_59_, 0);
lean_inc(v_map_60_);
lean_dec_ref(v_inst_59_);
v___f_61_ = ((lean_object*)(l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0));
v___x_62_ = lean_apply_4(v_map_60_, lean_box(0), lean_box(0), v___f_61_, v_inst_58_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor(lean_object* v_m_63_, lean_object* v_inst_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v_inst_64_, v_inst_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0(lean_object* v_x_67_){
_start:
{
lean_object* v_lakeEnv_68_; 
v_lakeEnv_68_ = lean_ctor_get(v_x_67_, 0);
lean_inc_ref(v_lakeEnv_68_);
return v_lakeEnv_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed(lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0(v_x_69_);
lean_dec_ref(v_x_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v_map_74_; lean_object* v___f_75_; lean_object* v___x_76_; 
v_map_74_ = lean_ctor_get(v_inst_73_, 0);
lean_inc(v_map_74_);
lean_dec_ref(v_inst_73_);
v___f_75_ = ((lean_object*)(l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0));
v___x_76_ = lean_apply_4(v_map_74_, lean_box(0), lean_box(0), v___f_75_, v_inst_72_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor(lean_object* v_m_77_, lean_object* v_inst_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(v_inst_78_, v_inst_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg___lam__0(lean_object* v_x_81_){
_start:
{
lean_object* v_packages_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_packages_82_ = lean_ctor_get(v_x_81_, 4);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_array_fget_borrowed(v_packages_82_, v___x_83_);
lean_inc(v___x_84_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg___lam__0___boxed(lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lake_getRootPackage___redArg___lam__0(v_x_85_);
lean_dec_ref(v_x_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg(lean_object* v_inst_88_, lean_object* v_inst_89_){
_start:
{
lean_object* v_map_90_; lean_object* v___f_91_; lean_object* v___x_92_; 
v_map_90_ = lean_ctor_get(v_inst_89_, 0);
lean_inc(v_map_90_);
lean_dec_ref(v_inst_89_);
v___f_91_ = ((lean_object*)(l_Lake_getRootPackage___redArg___closed__0));
v___x_92_ = lean_apply_4(v_map_90_, lean_box(0), lean_box(0), v___f_91_, v_inst_88_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage(lean_object* v_m_93_, lean_object* v_inst_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v_map_96_; lean_object* v___f_97_; lean_object* v___x_98_; 
v_map_96_ = lean_ctor_get(v_inst_95_, 0);
lean_inc(v_map_96_);
lean_dec_ref(v_inst_95_);
v___f_97_ = ((lean_object*)(l_Lake_getRootPackage___redArg___closed__0));
v___x_98_ = lean_apply_4(v_map_96_, lean_box(0), lean_box(0), v___f_97_, v_inst_94_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f___redArg___lam__0(lean_object* v_keyName_100_, lean_object* v_x_101_){
_start:
{
lean_object* v_packageMap_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_packageMap_102_ = lean_ctor_get(v_x_101_, 5);
lean_inc(v_packageMap_102_);
lean_dec_ref(v_x_101_);
v___x_103_ = ((lean_object*)(l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0));
v___x_104_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_103_, v_packageMap_102_, v_keyName_100_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f___redArg(lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_keyName_107_){
_start:
{
lean_object* v_map_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v_map_108_ = lean_ctor_get(v_inst_106_, 0);
lean_inc(v_map_108_);
lean_dec_ref(v_inst_106_);
v___f_109_ = lean_alloc_closure((void*)(l_Lake_findPackageByKey_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_109_, 0, v_keyName_107_);
v___x_110_ = lean_apply_4(v_map_108_, lean_box(0), lean_box(0), v___f_109_, v_inst_105_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f(lean_object* v_m_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_keyName_114_){
_start:
{
lean_object* v_map_115_; lean_object* v___f_116_; lean_object* v___x_117_; 
v_map_115_ = lean_ctor_get(v_inst_113_, 0);
lean_inc(v_map_115_);
lean_dec_ref(v_inst_113_);
v___f_116_ = lean_alloc_closure((void*)(l_Lake_findPackageByKey_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_116_, 0, v_keyName_114_);
v___x_117_ = lean_apply_4(v_map_115_, lean_box(0), lean_box(0), v___f_116_, v_inst_112_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__0(lean_object* v_name_118_, lean_object* v___x_119_, lean_object* v___x_120_, lean_object* v_a_121_, lean_object* v_x_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_baseName_124_; uint8_t v___x_125_; 
v_baseName_124_ = lean_ctor_get(v_a_121_, 1);
v___x_125_ = lean_name_eq(v_baseName_124_, v_name_118_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec_ref(v_a_121_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_119_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec_ref(v___x_119_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_a_121_);
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_120_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__0___boxed(lean_object* v_name_131_, lean_object* v___x_132_, lean_object* v___x_133_, lean_object* v_a_134_, lean_object* v_x_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_findPackageByName_x3f___redArg___lam__0(v_name_131_, v___x_132_, v___x_133_, v_a_134_, v_x_135_, v___y_136_);
lean_dec_ref(v___y_136_);
lean_dec(v_name_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1(lean_object* v_name_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_packages_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___f_167_; size_t v_sz_168_; size_t v___x_169_; lean_object* v___x_170_; lean_object* v_fst_171_; 
v_packages_162_ = lean_ctor_get(v_x_161_, 4);
lean_inc_ref(v_packages_162_);
lean_dec_ref(v_x_161_);
v___x_163_ = ((lean_object*)(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9));
v___x_164_ = lean_box(0);
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10));
v___f_167_ = lean_alloc_closure((void*)(l_Lake_findPackageByName_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_167_, 0, v_name_160_);
lean_closure_set(v___f_167_, 1, v___x_166_);
lean_closure_set(v___f_167_, 2, v___x_165_);
v_sz_168_ = lean_array_size(v_packages_162_);
v___x_169_ = ((size_t)0ULL);
v___x_170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_163_, v_packages_162_, v___f_167_, v_sz_168_, v___x_169_, v___x_166_);
v_fst_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_fst_171_);
lean_dec(v___x_170_);
if (lean_obj_tag(v_fst_171_) == 0)
{
return v___x_164_;
}
else
{
lean_object* v_val_172_; 
v_val_172_ = lean_ctor_get(v_fst_171_, 0);
lean_inc(v_val_172_);
lean_dec_ref_known(v_fst_171_, 1);
return v_val_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_name_175_){
_start:
{
lean_object* v_map_176_; lean_object* v___f_177_; lean_object* v___x_178_; 
v_map_176_ = lean_ctor_get(v_inst_174_, 0);
lean_inc(v_map_176_);
lean_dec_ref(v_inst_174_);
v___f_177_ = lean_alloc_closure((void*)(l_Lake_findPackageByName_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_177_, 0, v_name_175_);
v___x_178_ = lean_apply_4(v_map_176_, lean_box(0), lean_box(0), v___f_177_, v_inst_173_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f(lean_object* v_m_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_name_182_){
_start:
{
lean_object* v_map_183_; lean_object* v___f_184_; lean_object* v___x_185_; 
v_map_183_ = lean_ctor_get(v_inst_181_, 0);
lean_inc(v_map_183_);
lean_dec_ref(v_inst_181_);
v___f_184_ = lean_alloc_closure((void*)(l_Lake_findPackageByName_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_184_, 0, v_name_182_);
v___x_185_ = lean_apply_4(v_map_183_, lean_box(0), lean_box(0), v___f_184_, v_inst_180_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___redArg___lam__0(lean_object* v_name_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_packageMap_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_packageMap_188_ = lean_ctor_get(v_x_187_, 5);
lean_inc(v_packageMap_188_);
lean_dec_ref(v_x_187_);
v___x_189_ = ((lean_object*)(l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0));
v___x_190_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_189_, v_packageMap_188_, v_name_186_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___redArg(lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_name_193_){
_start:
{
lean_object* v_map_194_; lean_object* v___f_195_; lean_object* v___x_196_; 
v_map_194_ = lean_ctor_get(v_inst_192_, 0);
lean_inc(v_map_194_);
lean_dec_ref(v_inst_192_);
v___f_195_ = lean_alloc_closure((void*)(l_Lake_findPackage_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_195_, 0, v_name_193_);
v___x_196_ = lean_apply_4(v_map_194_, lean_box(0), lean_box(0), v___f_195_, v_inst_191_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f(lean_object* v_m_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_name_200_){
_start:
{
lean_object* v_map_201_; lean_object* v___f_202_; lean_object* v___x_203_; 
v_map_201_ = lean_ctor_get(v_inst_199_, 0);
lean_inc(v_map_201_);
lean_dec_ref(v_inst_199_);
v___f_202_ = lean_alloc_closure((void*)(l_Lake_findPackage_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_202_, 0, v_name_200_);
v___x_203_ = lean_apply_4(v_map_201_, lean_box(0), lean_box(0), v___f_202_, v_inst_198_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg___lam__0(lean_object* v_name_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lake_Workspace_findModule_x3f(v_name_204_, v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg___lam__0___boxed(lean_object* v_name_207_, lean_object* v_x_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lake_findModule_x3f___redArg___lam__0(v_name_207_, v_x_208_);
lean_dec_ref(v_x_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_name_212_){
_start:
{
lean_object* v_map_213_; lean_object* v___f_214_; lean_object* v___x_215_; 
v_map_213_ = lean_ctor_get(v_inst_211_, 0);
lean_inc(v_map_213_);
lean_dec_ref(v_inst_211_);
v___f_214_ = lean_alloc_closure((void*)(l_Lake_findModule_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_214_, 0, v_name_212_);
v___x_215_ = lean_apply_4(v_map_213_, lean_box(0), lean_box(0), v___f_214_, v_inst_210_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f(lean_object* v_m_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_name_219_){
_start:
{
lean_object* v_map_220_; lean_object* v___f_221_; lean_object* v___x_222_; 
v_map_220_ = lean_ctor_get(v_inst_218_, 0);
lean_inc(v_map_220_);
lean_dec_ref(v_inst_218_);
v___f_221_ = lean_alloc_closure((void*)(l_Lake_findModule_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_221_, 0, v_name_219_);
v___x_222_ = lean_apply_4(v_map_220_, lean_box(0), lean_box(0), v___f_221_, v_inst_217_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules___redArg___lam__0(lean_object* v_name_223_, lean_object* v_x_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lake_Workspace_findModules(v_name_223_, v_x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules___redArg___lam__0___boxed(lean_object* v_name_226_, lean_object* v_x_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lake_findModules___redArg___lam__0(v_name_226_, v_x_227_);
lean_dec_ref(v_x_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules___redArg(lean_object* v_inst_229_, lean_object* v_inst_230_, lean_object* v_name_231_){
_start:
{
lean_object* v_map_232_; lean_object* v___f_233_; lean_object* v___x_234_; 
v_map_232_ = lean_ctor_get(v_inst_230_, 0);
lean_inc(v_map_232_);
lean_dec_ref(v_inst_230_);
v___f_233_ = lean_alloc_closure((void*)(l_Lake_findModules___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_233_, 0, v_name_231_);
v___x_234_ = lean_apply_4(v_map_232_, lean_box(0), lean_box(0), v___f_233_, v_inst_229_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules(lean_object* v_m_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_name_238_){
_start:
{
lean_object* v_map_239_; lean_object* v___f_240_; lean_object* v___x_241_; 
v_map_239_ = lean_ctor_get(v_inst_237_, 0);
lean_inc(v_map_239_);
lean_dec_ref(v_inst_237_);
v___f_240_ = lean_alloc_closure((void*)(l_Lake_findModules___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_240_, 0, v_name_238_);
v___x_241_ = lean_apply_4(v_map_239_, lean_box(0), lean_box(0), v___f_240_, v_inst_236_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg___lam__0(lean_object* v_path_242_, lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_242_, v_x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed(lean_object* v_path_245_, lean_object* v_x_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_findModuleBySrc_x3f___redArg___lam__0(v_path_245_, v_x_246_);
lean_dec_ref(v_x_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg(lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_path_250_){
_start:
{
lean_object* v_map_251_; lean_object* v___f_252_; lean_object* v___x_253_; 
v_map_251_ = lean_ctor_get(v_inst_249_, 0);
lean_inc(v_map_251_);
lean_dec_ref(v_inst_249_);
v___f_252_ = lean_alloc_closure((void*)(l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_252_, 0, v_path_250_);
v___x_253_ = lean_apply_4(v_map_251_, lean_box(0), lean_box(0), v___f_252_, v_inst_248_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f(lean_object* v_m_254_, lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_path_257_){
_start:
{
lean_object* v_map_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v_map_258_ = lean_ctor_get(v_inst_256_, 0);
lean_inc(v_map_258_);
lean_dec_ref(v_inst_256_);
v___f_259_ = lean_alloc_closure((void*)(l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_259_, 0, v_path_257_);
v___x_260_ = lean_apply_4(v_map_258_, lean_box(0), lean_box(0), v___f_259_, v_inst_255_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg___lam__0(lean_object* v_name_261_, lean_object* v_x_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lake_Workspace_findLeanExe_x3f(v_name_261_, v_x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg___lam__0___boxed(lean_object* v_name_264_, lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lake_findLeanExe_x3f___redArg___lam__0(v_name_264_, v_x_265_);
lean_dec_ref(v_x_265_);
lean_dec(v_name_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg(lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_name_269_){
_start:
{
lean_object* v_map_270_; lean_object* v___f_271_; lean_object* v___x_272_; 
v_map_270_ = lean_ctor_get(v_inst_268_, 0);
lean_inc(v_map_270_);
lean_dec_ref(v_inst_268_);
v___f_271_ = lean_alloc_closure((void*)(l_Lake_findLeanExe_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_271_, 0, v_name_269_);
v___x_272_ = lean_apply_4(v_map_270_, lean_box(0), lean_box(0), v___f_271_, v_inst_267_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f(lean_object* v_m_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_name_276_){
_start:
{
lean_object* v_map_277_; lean_object* v___f_278_; lean_object* v___x_279_; 
v_map_277_ = lean_ctor_get(v_inst_275_, 0);
lean_inc(v_map_277_);
lean_dec_ref(v_inst_275_);
v___f_278_ = lean_alloc_closure((void*)(l_Lake_findLeanExe_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_278_, 0, v_name_276_);
v___x_279_ = lean_apply_4(v_map_277_, lean_box(0), lean_box(0), v___f_278_, v_inst_274_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg___lam__0(lean_object* v_name_280_, lean_object* v_x_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lake_Workspace_findLeanLib_x3f(v_name_280_, v_x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg___lam__0___boxed(lean_object* v_name_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lake_findLeanLib_x3f___redArg___lam__0(v_name_283_, v_x_284_);
lean_dec_ref(v_x_284_);
lean_dec(v_name_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg(lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_name_288_){
_start:
{
lean_object* v_map_289_; lean_object* v___f_290_; lean_object* v___x_291_; 
v_map_289_ = lean_ctor_get(v_inst_287_, 0);
lean_inc(v_map_289_);
lean_dec_ref(v_inst_287_);
v___f_290_ = lean_alloc_closure((void*)(l_Lake_findLeanLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_290_, 0, v_name_288_);
v___x_291_ = lean_apply_4(v_map_289_, lean_box(0), lean_box(0), v___f_290_, v_inst_286_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f(lean_object* v_m_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_name_295_){
_start:
{
lean_object* v_map_296_; lean_object* v___f_297_; lean_object* v___x_298_; 
v_map_296_ = lean_ctor_get(v_inst_294_, 0);
lean_inc(v_map_296_);
lean_dec_ref(v_inst_294_);
v___f_297_ = lean_alloc_closure((void*)(l_Lake_findLeanLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_297_, 0, v_name_295_);
v___x_298_ = lean_apply_4(v_map_296_, lean_box(0), lean_box(0), v___f_297_, v_inst_293_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg___lam__0(lean_object* v_name_299_, lean_object* v_x_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lake_Workspace_findExternLib_x3f(v_name_299_, v_x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg___lam__0___boxed(lean_object* v_name_302_, lean_object* v_x_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lake_findExternLib_x3f___redArg___lam__0(v_name_302_, v_x_303_);
lean_dec_ref(v_x_303_);
lean_dec(v_name_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_name_307_){
_start:
{
lean_object* v_map_308_; lean_object* v___f_309_; lean_object* v___x_310_; 
v_map_308_ = lean_ctor_get(v_inst_306_, 0);
lean_inc(v_map_308_);
lean_dec_ref(v_inst_306_);
v___f_309_ = lean_alloc_closure((void*)(l_Lake_findExternLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_309_, 0, v_name_307_);
v___x_310_ = lean_apply_4(v_map_308_, lean_box(0), lean_box(0), v___f_309_, v_inst_305_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f(lean_object* v_m_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_name_314_){
_start:
{
lean_object* v_map_315_; lean_object* v___f_316_; lean_object* v___x_317_; 
v_map_315_ = lean_ctor_get(v_inst_313_, 0);
lean_inc(v_map_315_);
lean_dec_ref(v_inst_313_);
v___f_316_ = lean_alloc_closure((void*)(l_Lake_findExternLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_316_, 0, v_name_314_);
v___x_317_ = lean_apply_4(v_map_315_, lean_box(0), lean_box(0), v___f_316_, v_inst_312_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg___lam__0(lean_object* v_x_318_){
_start:
{
lean_object* v_packages_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_config_322_; lean_object* v_toLeanConfig_323_; lean_object* v_leanOptions_324_; lean_object* v_moreServerOptions_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_packages_319_ = lean_ctor_get(v_x_318_, 4);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_array_fget_borrowed(v_packages_319_, v___x_320_);
v_config_322_ = lean_ctor_get(v___x_321_, 6);
v_toLeanConfig_323_ = lean_ctor_get(v_config_322_, 1);
v_leanOptions_324_ = lean_ctor_get(v_toLeanConfig_323_, 0);
v_moreServerOptions_325_ = lean_ctor_get(v_toLeanConfig_323_, 4);
v___x_326_ = l_Lean_LeanOptions_ofArray(v_leanOptions_324_);
v___x_327_ = l_Lean_LeanOptions_appendArray(v___x_326_, v_moreServerOptions_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg___lam__0___boxed(lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lake_getServerOptions___redArg___lam__0(v_x_328_);
lean_dec_ref(v_x_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg(lean_object* v_inst_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v_map_333_; lean_object* v___f_334_; lean_object* v___x_335_; 
v_map_333_ = lean_ctor_get(v_inst_332_, 0);
lean_inc(v_map_333_);
lean_dec_ref(v_inst_332_);
v___f_334_ = ((lean_object*)(l_Lake_getServerOptions___redArg___closed__0));
v___x_335_ = lean_apply_4(v_map_333_, lean_box(0), lean_box(0), v___f_334_, v_inst_331_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions(lean_object* v_m_336_, lean_object* v_inst_337_, lean_object* v_inst_338_){
_start:
{
lean_object* v_map_339_; lean_object* v___f_340_; lean_object* v___x_341_; 
v_map_339_ = lean_ctor_get(v_inst_338_, 0);
lean_inc(v_map_339_);
lean_dec_ref(v_inst_338_);
v___f_340_ = ((lean_object*)(l_Lake_getServerOptions___redArg___closed__0));
v___x_341_ = lean_apply_4(v_map_339_, lean_box(0), lean_box(0), v___f_340_, v_inst_337_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg___lam__0(lean_object* v_x_342_){
_start:
{
lean_object* v_packages_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_config_346_; lean_object* v_toLeanConfig_347_; lean_object* v_leanOptions_348_; lean_object* v___x_349_; 
v_packages_343_ = lean_ctor_get(v_x_342_, 4);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_array_fget_borrowed(v_packages_343_, v___x_344_);
v_config_346_ = lean_ctor_get(v___x_345_, 6);
v_toLeanConfig_347_ = lean_ctor_get(v_config_346_, 1);
v_leanOptions_348_ = lean_ctor_get(v_toLeanConfig_347_, 0);
v___x_349_ = l_Lean_LeanOptions_ofArray(v_leanOptions_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg___lam__0___boxed(lean_object* v_x_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lake_getLeanOptions___redArg___lam__0(v_x_350_);
lean_dec_ref(v_x_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg(lean_object* v_inst_353_, lean_object* v_inst_354_){
_start:
{
lean_object* v_map_355_; lean_object* v___f_356_; lean_object* v___x_357_; 
v_map_355_ = lean_ctor_get(v_inst_354_, 0);
lean_inc(v_map_355_);
lean_dec_ref(v_inst_354_);
v___f_356_ = ((lean_object*)(l_Lake_getLeanOptions___redArg___closed__0));
v___x_357_ = lean_apply_4(v_map_355_, lean_box(0), lean_box(0), v___f_356_, v_inst_353_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions(lean_object* v_m_358_, lean_object* v_inst_359_, lean_object* v_inst_360_){
_start:
{
lean_object* v_map_361_; lean_object* v___f_362_; lean_object* v___x_363_; 
v_map_361_ = lean_ctor_get(v_inst_360_, 0);
lean_inc(v_map_361_);
lean_dec_ref(v_inst_360_);
v___f_362_ = ((lean_object*)(l_Lake_getLeanOptions___redArg___closed__0));
v___x_363_ = lean_apply_4(v_map_361_, lean_box(0), lean_box(0), v___f_362_, v_inst_359_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg___lam__0(lean_object* v_x_364_){
_start:
{
lean_object* v_packages_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_config_368_; lean_object* v_toLeanConfig_369_; lean_object* v_moreLeanArgs_370_; 
v_packages_365_ = lean_ctor_get(v_x_364_, 4);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_array_fget_borrowed(v_packages_365_, v___x_366_);
v_config_368_ = lean_ctor_get(v___x_367_, 6);
v_toLeanConfig_369_ = lean_ctor_get(v_config_368_, 1);
v_moreLeanArgs_370_ = lean_ctor_get(v_toLeanConfig_369_, 1);
lean_inc_ref(v_moreLeanArgs_370_);
return v_moreLeanArgs_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg___lam__0___boxed(lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lake_getLeanArgs___redArg___lam__0(v_x_371_);
lean_dec_ref(v_x_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg(lean_object* v_inst_374_, lean_object* v_inst_375_){
_start:
{
lean_object* v_map_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
v_map_376_ = lean_ctor_get(v_inst_375_, 0);
lean_inc(v_map_376_);
lean_dec_ref(v_inst_375_);
v___f_377_ = ((lean_object*)(l_Lake_getLeanArgs___redArg___closed__0));
v___x_378_ = lean_apply_4(v_map_376_, lean_box(0), lean_box(0), v___f_377_, v_inst_374_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanArgs(lean_object* v_m_379_, lean_object* v_inst_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v_map_382_; lean_object* v___f_383_; lean_object* v___x_384_; 
v_map_382_ = lean_ctor_get(v_inst_381_, 0);
lean_inc(v_map_382_);
lean_dec_ref(v_inst_381_);
v___f_383_ = ((lean_object*)(l_Lake_getLeanArgs___redArg___closed__0));
v___x_384_ = lean_apply_4(v_map_382_, lean_box(0), lean_box(0), v___f_383_, v_inst_380_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanPath___redArg(lean_object* v_inst_386_, lean_object* v_inst_387_){
_start:
{
lean_object* v_map_388_; lean_object* v___f_389_; lean_object* v___x_390_; 
v_map_388_ = lean_ctor_get(v_inst_387_, 0);
lean_inc(v_map_388_);
lean_dec_ref(v_inst_387_);
v___f_389_ = ((lean_object*)(l_Lake_getLeanPath___redArg___closed__0));
v___x_390_ = lean_apply_4(v_map_388_, lean_box(0), lean_box(0), v___f_389_, v_inst_386_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanPath(lean_object* v_m_391_, lean_object* v_inst_392_, lean_object* v_inst_393_){
_start:
{
lean_object* v_map_394_; lean_object* v___f_395_; lean_object* v___x_396_; 
v_map_394_ = lean_ctor_get(v_inst_393_, 0);
lean_inc(v_map_394_);
lean_dec_ref(v_inst_393_);
v___f_395_ = ((lean_object*)(l_Lake_getLeanPath___redArg___closed__0));
v___x_396_ = lean_apply_4(v_map_394_, lean_box(0), lean_box(0), v___f_395_, v_inst_392_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath___redArg(lean_object* v_inst_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v_map_400_; lean_object* v___f_401_; lean_object* v___x_402_; 
v_map_400_ = lean_ctor_get(v_inst_399_, 0);
lean_inc(v_map_400_);
lean_dec_ref(v_inst_399_);
v___f_401_ = ((lean_object*)(l_Lake_getLeanSrcPath___redArg___closed__0));
v___x_402_ = lean_apply_4(v_map_400_, lean_box(0), lean_box(0), v___f_401_, v_inst_398_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath(lean_object* v_m_403_, lean_object* v_inst_404_, lean_object* v_inst_405_){
_start:
{
lean_object* v_map_406_; lean_object* v___f_407_; lean_object* v___x_408_; 
v_map_406_ = lean_ctor_get(v_inst_405_, 0);
lean_inc(v_map_406_);
lean_dec_ref(v_inst_405_);
v___f_407_ = ((lean_object*)(l_Lake_getLeanSrcPath___redArg___closed__0));
v___x_408_ = lean_apply_4(v_map_406_, lean_box(0), lean_box(0), v___f_407_, v_inst_404_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath___redArg(lean_object* v_inst_410_, lean_object* v_inst_411_){
_start:
{
lean_object* v_map_412_; lean_object* v___f_413_; lean_object* v___x_414_; 
v_map_412_ = lean_ctor_get(v_inst_411_, 0);
lean_inc(v_map_412_);
lean_dec_ref(v_inst_411_);
v___f_413_ = ((lean_object*)(l_Lake_getSharedLibPath___redArg___closed__0));
v___x_414_ = lean_apply_4(v_map_412_, lean_box(0), lean_box(0), v___f_413_, v_inst_410_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath(lean_object* v_m_415_, lean_object* v_inst_416_, lean_object* v_inst_417_){
_start:
{
lean_object* v_map_418_; lean_object* v___f_419_; lean_object* v___x_420_; 
v_map_418_ = lean_ctor_get(v_inst_417_, 0);
lean_inc(v_map_418_);
lean_dec_ref(v_inst_417_);
v___f_419_ = ((lean_object*)(l_Lake_getSharedLibPath___redArg___closed__0));
v___x_420_ = lean_apply_4(v_map_418_, lean_box(0), lean_box(0), v___f_419_, v_inst_416_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath___redArg(lean_object* v_inst_422_, lean_object* v_inst_423_){
_start:
{
lean_object* v_map_424_; lean_object* v___f_425_; lean_object* v___x_426_; 
v_map_424_ = lean_ctor_get(v_inst_423_, 0);
lean_inc(v_map_424_);
lean_dec_ref(v_inst_423_);
v___f_425_ = ((lean_object*)(l_Lake_getAugmentedLeanPath___redArg___closed__0));
v___x_426_ = lean_apply_4(v_map_424_, lean_box(0), lean_box(0), v___f_425_, v_inst_422_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath(lean_object* v_m_427_, lean_object* v_inst_428_, lean_object* v_inst_429_){
_start:
{
lean_object* v_map_430_; lean_object* v___f_431_; lean_object* v___x_432_; 
v_map_430_ = lean_ctor_get(v_inst_429_, 0);
lean_inc(v_map_430_);
lean_dec_ref(v_inst_429_);
v___f_431_ = ((lean_object*)(l_Lake_getAugmentedLeanPath___redArg___closed__0));
v___x_432_ = lean_apply_4(v_map_430_, lean_box(0), lean_box(0), v___f_431_, v_inst_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath___redArg(lean_object* v_inst_434_, lean_object* v_inst_435_){
_start:
{
lean_object* v_map_436_; lean_object* v___f_437_; lean_object* v___x_438_; 
v_map_436_ = lean_ctor_get(v_inst_435_, 0);
lean_inc(v_map_436_);
lean_dec_ref(v_inst_435_);
v___f_437_ = ((lean_object*)(l_Lake_getAugmentedLeanSrcPath___redArg___closed__0));
v___x_438_ = lean_apply_4(v_map_436_, lean_box(0), lean_box(0), v___f_437_, v_inst_434_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath(lean_object* v_m_439_, lean_object* v_inst_440_, lean_object* v_inst_441_){
_start:
{
lean_object* v_map_442_; lean_object* v___f_443_; lean_object* v___x_444_; 
v_map_442_ = lean_ctor_get(v_inst_441_, 0);
lean_inc(v_map_442_);
lean_dec_ref(v_inst_441_);
v___f_443_ = ((lean_object*)(l_Lake_getAugmentedLeanSrcPath___redArg___closed__0));
v___x_444_ = lean_apply_4(v_map_442_, lean_box(0), lean_box(0), v___f_443_, v_inst_440_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath___redArg(lean_object* v_inst_446_, lean_object* v_inst_447_){
_start:
{
lean_object* v_map_448_; lean_object* v___f_449_; lean_object* v___x_450_; 
v_map_448_ = lean_ctor_get(v_inst_447_, 0);
lean_inc(v_map_448_);
lean_dec_ref(v_inst_447_);
v___f_449_ = ((lean_object*)(l_Lake_getAugmentedSharedLibPath___redArg___closed__0));
v___x_450_ = lean_apply_4(v_map_448_, lean_box(0), lean_box(0), v___f_449_, v_inst_446_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath(lean_object* v_m_451_, lean_object* v_inst_452_, lean_object* v_inst_453_){
_start:
{
lean_object* v_map_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v_map_454_ = lean_ctor_get(v_inst_453_, 0);
lean_inc(v_map_454_);
lean_dec_ref(v_inst_453_);
v___f_455_ = ((lean_object*)(l_Lake_getAugmentedSharedLibPath___redArg___closed__0));
v___x_456_ = lean_apply_4(v_map_454_, lean_box(0), lean_box(0), v___f_455_, v_inst_452_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv___redArg(lean_object* v_inst_458_, lean_object* v_inst_459_){
_start:
{
lean_object* v_map_460_; lean_object* v___f_461_; lean_object* v___x_462_; 
v_map_460_ = lean_ctor_get(v_inst_459_, 0);
lean_inc(v_map_460_);
lean_dec_ref(v_inst_459_);
v___f_461_ = ((lean_object*)(l_Lake_getAugmentedEnv___redArg___closed__0));
v___x_462_ = lean_apply_4(v_map_460_, lean_box(0), lean_box(0), v___f_461_, v_inst_458_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv(lean_object* v_m_463_, lean_object* v_inst_464_, lean_object* v_inst_465_){
_start:
{
lean_object* v_map_466_; lean_object* v___f_467_; lean_object* v___x_468_; 
v_map_466_ = lean_ctor_get(v_inst_465_, 0);
lean_inc(v_map_466_);
lean_dec_ref(v_inst_465_);
v___f_467_ = ((lean_object*)(l_Lake_getAugmentedEnv___redArg___closed__0));
v___x_468_ = lean_apply_4(v_map_466_, lean_box(0), lean_box(0), v___f_467_, v_inst_464_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg___lam__0(lean_object* v_x_469_){
_start:
{
lean_object* v_lakeCache_470_; 
v_lakeCache_470_ = lean_ctor_get(v_x_469_, 2);
lean_inc_ref(v_lakeCache_470_);
return v_lakeCache_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg___lam__0___boxed(lean_object* v_x_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lake_getLakeCache___redArg___lam__0(v_x_471_);
lean_dec_ref(v_x_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg(lean_object* v_inst_474_, lean_object* v_inst_475_){
_start:
{
lean_object* v_map_476_; lean_object* v___f_477_; lean_object* v___x_478_; 
v_map_476_ = lean_ctor_get(v_inst_475_, 0);
lean_inc(v_map_476_);
lean_dec_ref(v_inst_475_);
v___f_477_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___x_478_ = lean_apply_4(v_map_476_, lean_box(0), lean_box(0), v___f_477_, v_inst_474_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache(lean_object* v_m_479_, lean_object* v_inst_480_, lean_object* v_inst_481_){
_start:
{
lean_object* v_map_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
v_map_482_ = lean_ctor_get(v_inst_481_, 0);
lean_inc(v_map_482_);
lean_dec_ref(v_inst_481_);
v___f_483_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___x_484_ = lean_apply_4(v_map_482_, lean_box(0), lean_box(0), v___f_483_, v_inst_480_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f___redArg___lam__1(lean_object* v_descr_485_, lean_object* v_inst_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_alloc_closure((void*)(l_Lake_Cache_getArtifact_x3f___boxed), 3, 2);
lean_closure_set(v___x_488_, 0, v_x_487_);
lean_closure_set(v___x_488_, 1, v_descr_485_);
v___x_489_ = lean_apply_2(v_inst_486_, lean_box(0), v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f___redArg(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_descr_494_){
_start:
{
lean_object* v_map_495_; lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_map_495_ = lean_ctor_get(v_inst_491_, 0);
lean_inc(v_map_495_);
lean_dec_ref(v_inst_491_);
v___f_496_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___f_497_ = lean_alloc_closure((void*)(l_Lake_getArtifact_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_497_, 0, v_descr_494_);
lean_closure_set(v___f_497_, 1, v_inst_493_);
v___x_498_ = lean_apply_4(v_map_495_, lean_box(0), lean_box(0), v___f_496_, v_inst_490_);
v___x_499_ = lean_apply_4(v_inst_492_, lean_box(0), lean_box(0), v___x_498_, v___f_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f(lean_object* v_m_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_descr_505_){
_start:
{
lean_object* v_map_506_; lean_object* v___f_507_; lean_object* v___f_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_map_506_ = lean_ctor_get(v_inst_502_, 0);
lean_inc(v_map_506_);
lean_dec_ref(v_inst_502_);
v___f_507_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___f_508_ = lean_alloc_closure((void*)(l_Lake_getArtifact_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_508_, 0, v_descr_505_);
lean_closure_set(v___f_508_, 1, v_inst_504_);
v___x_509_ = lean_apply_4(v_map_506_, lean_box(0), lean_box(0), v___f_507_, v_inst_501_);
v___x_510_ = lean_apply_4(v_inst_503_, lean_box(0), lean_box(0), v___x_509_, v___f_508_);
return v___x_510_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_restoreAllArtifacts___redArg___lam__0(lean_object* v_self_511_, lean_object* v_x_512_){
_start:
{
lean_object* v_config_513_; lean_object* v_restoreAllArtifacts_x3f_514_; 
v_config_513_ = lean_ctor_get(v_self_511_, 6);
v_restoreAllArtifacts_x3f_514_ = lean_ctor_get(v_config_513_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_514_) == 0)
{
lean_object* v_lakeEnv_515_; lean_object* v_restoreAllArtifacts_x3f_516_; 
v_lakeEnv_515_ = lean_ctor_get(v_x_512_, 0);
v_restoreAllArtifacts_x3f_516_ = lean_ctor_get(v_lakeEnv_515_, 7);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_516_) == 0)
{
lean_object* v_packages_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_config_520_; lean_object* v_restoreAllArtifacts_x3f_521_; 
v_packages_517_ = lean_ctor_get(v_x_512_, 4);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_array_fget_borrowed(v_packages_517_, v___x_518_);
v_config_520_ = lean_ctor_get(v___x_519_, 6);
v_restoreAllArtifacts_x3f_521_ = lean_ctor_get(v_config_520_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_521_) == 0)
{
uint8_t v___x_522_; 
v___x_522_ = 0;
return v___x_522_;
}
else
{
lean_object* v_val_523_; uint8_t v___x_524_; 
v_val_523_ = lean_ctor_get(v_restoreAllArtifacts_x3f_521_, 0);
v___x_524_ = lean_unbox(v_val_523_);
return v___x_524_;
}
}
else
{
lean_object* v_val_525_; uint8_t v___x_526_; 
v_val_525_ = lean_ctor_get(v_restoreAllArtifacts_x3f_516_, 0);
v___x_526_ = lean_unbox(v_val_525_);
return v___x_526_;
}
}
else
{
lean_object* v_val_527_; uint8_t v___x_528_; 
v_val_527_ = lean_ctor_get(v_restoreAllArtifacts_x3f_514_, 0);
v___x_528_ = lean_unbox(v_val_527_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed(lean_object* v_self_529_, lean_object* v_x_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Lake_Package_restoreAllArtifacts___redArg___lam__0(v_self_529_, v_x_530_);
lean_dec_ref(v_x_530_);
lean_dec_ref(v_self_529_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg(lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_self_535_){
_start:
{
lean_object* v_map_536_; lean_object* v___f_537_; lean_object* v___x_538_; 
v_map_536_ = lean_ctor_get(v_inst_533_, 0);
lean_inc(v_map_536_);
lean_dec_ref(v_inst_533_);
v___f_537_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_537_, 0, v_self_535_);
v___x_538_ = lean_apply_4(v_map_536_, lean_box(0), lean_box(0), v___f_537_, v_inst_534_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts(lean_object* v_m_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_self_542_){
_start:
{
lean_object* v_map_543_; lean_object* v___f_544_; lean_object* v___x_545_; 
v_map_543_ = lean_ctor_get(v_inst_540_, 0);
lean_inc(v_map_543_);
lean_dec_ref(v_inst_540_);
v___f_544_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_544_, 0, v_self_542_);
v___x_545_ = lean_apply_4(v_map_543_, lean_box(0), lean_box(0), v___f_544_, v_inst_541_);
return v___x_545_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(lean_object* v_self_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_config_548_; lean_object* v_enableArtifactCache_x3f_549_; 
v_config_548_ = lean_ctor_get(v_self_546_, 6);
v_enableArtifactCache_x3f_549_ = lean_ctor_get(v_config_548_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_549_) == 0)
{
lean_object* v_lakeEnv_550_; lean_object* v_enableArtifactCache_x3f_551_; 
v_lakeEnv_550_ = lean_ctor_get(v_x_547_, 0);
v_enableArtifactCache_x3f_551_ = lean_ctor_get(v_lakeEnv_550_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_551_) == 0)
{
lean_object* v_packages_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_config_555_; lean_object* v_enableArtifactCache_x3f_556_; 
v_packages_552_ = lean_ctor_get(v_x_547_, 4);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_array_fget_borrowed(v_packages_552_, v___x_553_);
v_config_555_ = lean_ctor_get(v___x_554_, 6);
v_enableArtifactCache_x3f_556_ = lean_ctor_get(v_config_555_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_556_) == 0)
{
uint8_t v___x_557_; 
v___x_557_ = 1;
return v___x_557_;
}
else
{
lean_object* v_val_558_; uint8_t v___x_559_; 
v_val_558_ = lean_ctor_get(v_enableArtifactCache_x3f_556_, 0);
v___x_559_ = lean_unbox(v_val_558_);
return v___x_559_;
}
}
else
{
lean_object* v_val_560_; uint8_t v___x_561_; 
v_val_560_ = lean_ctor_get(v_enableArtifactCache_x3f_551_, 0);
v___x_561_ = lean_unbox(v_val_560_);
return v___x_561_;
}
}
else
{
lean_object* v_val_562_; uint8_t v___x_563_; 
v_val_562_ = lean_ctor_get(v_enableArtifactCache_x3f_549_, 0);
v___x_563_ = lean_unbox(v_val_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed(lean_object* v_self_564_, lean_object* v_x_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(v_self_564_, v_x_565_);
lean_dec_ref(v_x_565_);
lean_dec_ref(v_self_564_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg(lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_self_570_){
_start:
{
lean_object* v_map_571_; lean_object* v___f_572_; lean_object* v___x_573_; 
v_map_571_ = lean_ctor_get(v_inst_568_, 0);
lean_inc(v_map_571_);
lean_dec_ref(v_inst_568_);
v___f_572_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_572_, 0, v_self_570_);
v___x_573_ = lean_apply_4(v_map_571_, lean_box(0), lean_box(0), v___f_572_, v_inst_569_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable(lean_object* v_m_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_self_577_){
_start:
{
lean_object* v_map_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v_map_578_ = lean_ctor_get(v_inst_575_, 0);
lean_inc(v_map_578_);
lean_dec_ref(v_inst_575_);
v___f_579_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_579_, 0, v_self_577_);
v___x_580_ = lean_apply_4(v_map_578_, lean_box(0), lean_box(0), v___f_579_, v_inst_576_);
return v___x_580_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(lean_object* v_self_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_config_583_; lean_object* v_enableArtifactCache_x3f_584_; 
v_config_583_ = lean_ctor_get(v_self_581_, 6);
v_enableArtifactCache_x3f_584_ = lean_ctor_get(v_config_583_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_584_) == 0)
{
lean_object* v_lakeEnv_585_; lean_object* v_enableArtifactCache_x3f_586_; 
v_lakeEnv_585_ = lean_ctor_get(v_x_582_, 0);
v_enableArtifactCache_x3f_586_ = lean_ctor_get(v_lakeEnv_585_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_586_) == 0)
{
lean_object* v_packages_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_config_590_; lean_object* v_enableArtifactCache_x3f_591_; 
v_packages_587_ = lean_ctor_get(v_x_582_, 4);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_array_fget_borrowed(v_packages_587_, v___x_588_);
v_config_590_ = lean_ctor_get(v___x_589_, 6);
v_enableArtifactCache_x3f_591_ = lean_ctor_get(v_config_590_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_591_) == 0)
{
uint8_t v___x_592_; 
v___x_592_ = 0;
return v___x_592_;
}
else
{
lean_object* v_val_593_; uint8_t v___x_594_; 
v_val_593_ = lean_ctor_get(v_enableArtifactCache_x3f_591_, 0);
v___x_594_ = lean_unbox(v_val_593_);
return v___x_594_;
}
}
else
{
lean_object* v_val_595_; uint8_t v___x_596_; 
v_val_595_ = lean_ctor_get(v_enableArtifactCache_x3f_586_, 0);
v___x_596_ = lean_unbox(v_val_595_);
return v___x_596_;
}
}
else
{
lean_object* v_val_597_; uint8_t v___x_598_; 
v_val_597_ = lean_ctor_get(v_enableArtifactCache_x3f_584_, 0);
v___x_598_ = lean_unbox(v_val_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed(lean_object* v_self_599_, lean_object* v_x_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(v_self_599_, v_x_600_);
lean_dec_ref(v_x_600_);
lean_dec_ref(v_self_599_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg(lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_self_605_){
_start:
{
lean_object* v_map_606_; lean_object* v___f_607_; lean_object* v___x_608_; 
v_map_606_ = lean_ctor_get(v_inst_603_, 0);
lean_inc(v_map_606_);
lean_dec_ref(v_inst_603_);
v___f_607_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_607_, 0, v_self_605_);
v___x_608_ = lean_apply_4(v_map_606_, lean_box(0), lean_box(0), v___f_607_, v_inst_604_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable(lean_object* v_m_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_self_612_){
_start:
{
lean_object* v_map_613_; lean_object* v___f_614_; lean_object* v___x_615_; 
v_map_613_ = lean_ctor_get(v_inst_610_, 0);
lean_inc(v_map_613_);
lean_dec_ref(v_inst_610_);
v___f_614_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_614_, 0, v_self_612_);
v___x_615_ = lean_apply_4(v_map_613_, lean_box(0), lean_box(0), v___f_614_, v_inst_611_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___redArg(lean_object* v_inst_616_, lean_object* v_inst_617_, lean_object* v_self_618_){
_start:
{
lean_object* v_map_619_; lean_object* v___f_620_; lean_object* v___x_621_; 
v_map_619_ = lean_ctor_get(v_inst_616_, 0);
lean_inc(v_map_619_);
lean_dec_ref(v_inst_616_);
v___f_620_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_620_, 0, v_self_618_);
v___x_621_ = lean_apply_4(v_map_619_, lean_box(0), lean_box(0), v___f_620_, v_inst_617_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled(lean_object* v_m_622_, lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_self_625_){
_start:
{
lean_object* v_map_626_; lean_object* v___f_627_; lean_object* v___x_628_; 
v_map_626_ = lean_ctor_get(v_inst_623_, 0);
lean_inc(v_map_626_);
lean_dec_ref(v_inst_623_);
v___f_627_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_627_, 0, v_self_625_);
v___x_628_ = lean_apply_4(v_map_626_, lean_box(0), lean_box(0), v___f_627_, v_inst_624_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg(lean_object* v_inst_629_){
_start:
{
lean_inc(v_inst_629_);
return v_inst_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg___boxed(lean_object* v_inst_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lake_getLakeEnv___redArg(v_inst_630_);
lean_dec(v_inst_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv(lean_object* v_m_632_, lean_object* v_inst_633_){
_start:
{
lean_inc(v_inst_633_);
return v_inst_633_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___boxed(lean_object* v_m_634_, lean_object* v_inst_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lake_getLakeEnv(v_m_634_, v_inst_635_);
lean_dec(v_inst_635_);
return v_res_636_;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoCache___redArg___lam__0(lean_object* v_x_637_){
_start:
{
uint8_t v_noCache_638_; 
v_noCache_638_ = lean_ctor_get_uint8(v_x_637_, sizeof(void*)*20);
return v_noCache_638_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg___lam__0___boxed(lean_object* v_x_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Lake_getNoCache___redArg___lam__0(v_x_639_);
lean_dec_ref(v_x_639_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg(lean_object* v_inst_643_, lean_object* v_inst_644_){
_start:
{
lean_object* v_map_645_; lean_object* v___f_646_; lean_object* v___x_647_; 
v_map_645_ = lean_ctor_get(v_inst_644_, 0);
lean_inc(v_map_645_);
lean_dec_ref(v_inst_644_);
v___f_646_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_647_ = lean_apply_4(v_map_645_, lean_box(0), lean_box(0), v___f_646_, v_inst_643_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache(lean_object* v_m_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_inst_651_){
_start:
{
lean_object* v_map_652_; lean_object* v___f_653_; lean_object* v___x_654_; 
v_map_652_ = lean_ctor_get(v_inst_650_, 0);
lean_inc(v_map_652_);
lean_dec_ref(v_inst_650_);
v___f_653_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_654_ = lean_apply_4(v_map_652_, lean_box(0), lean_box(0), v___f_653_, v_inst_649_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___boxed(lean_object* v_m_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_getNoCache(v_m_655_, v_inst_656_, v_inst_657_, v_inst_658_);
lean_dec(v_inst_658_);
return v_res_659_;
}
}
LEAN_EXPORT uint8_t l_Lake_getTryCache___redArg___lam__0(lean_object* v_x_660_){
_start:
{
uint8_t v_noCache_661_; uint8_t v___x_662_; 
v_noCache_661_ = lean_ctor_get_uint8(v_x_660_, sizeof(void*)*20);
v___x_662_ = lean_bool_not(v_noCache_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg___lam__0___boxed(lean_object* v_x_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_Lake_getTryCache___redArg___lam__0(v_x_663_);
lean_dec_ref(v_x_663_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg(lean_object* v_inst_667_, lean_object* v_inst_668_){
_start:
{
lean_object* v_map_669_; lean_object* v___f_670_; lean_object* v___x_671_; 
v_map_669_ = lean_ctor_get(v_inst_668_, 0);
lean_inc(v_map_669_);
lean_dec_ref(v_inst_668_);
v___f_670_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_671_ = lean_apply_4(v_map_669_, lean_box(0), lean_box(0), v___f_670_, v_inst_667_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object* v_m_672_, lean_object* v_inst_673_, lean_object* v_inst_674_, lean_object* v_inst_675_){
_start:
{
lean_object* v_map_676_; lean_object* v___f_677_; lean_object* v___x_678_; 
v_map_676_ = lean_ctor_get(v_inst_674_, 0);
lean_inc(v_map_676_);
lean_dec_ref(v_inst_674_);
v___f_677_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_678_ = lean_apply_4(v_map_676_, lean_box(0), lean_box(0), v___f_677_, v_inst_673_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___boxed(lean_object* v_m_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lake_getTryCache(v_m_679_, v_inst_680_, v_inst_681_, v_inst_682_);
lean_dec(v_inst_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0(lean_object* v_x_684_){
_start:
{
lean_object* v_pkgUrlMap_685_; 
v_pkgUrlMap_685_ = lean_ctor_get(v_x_684_, 5);
lean_inc(v_pkgUrlMap_685_);
return v_pkgUrlMap_685_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0___boxed(lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lake_getPkgUrlMap___redArg___lam__0(v_x_686_);
lean_dec_ref(v_x_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg(lean_object* v_inst_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v_map_691_; lean_object* v___f_692_; lean_object* v___x_693_; 
v_map_691_ = lean_ctor_get(v_inst_690_, 0);
lean_inc(v_map_691_);
lean_dec_ref(v_inst_690_);
v___f_692_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_693_ = lean_apply_4(v_map_691_, lean_box(0), lean_box(0), v___f_692_, v_inst_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object* v_m_694_, lean_object* v_inst_695_, lean_object* v_inst_696_){
_start:
{
lean_object* v_map_697_; lean_object* v___f_698_; lean_object* v___x_699_; 
v_map_697_ = lean_ctor_get(v_inst_696_, 0);
lean_inc(v_map_697_);
lean_dec_ref(v_inst_696_);
v___f_698_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_699_ = lean_apply_4(v_map_697_, lean_box(0), lean_box(0), v___f_698_, v_inst_695_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0(lean_object* v_x_700_){
_start:
{
lean_object* v_toolchain_701_; 
v_toolchain_701_ = lean_ctor_get(v_x_700_, 19);
lean_inc_ref(v_toolchain_701_);
return v_toolchain_701_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0___boxed(lean_object* v_x_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lake_getElanToolchain___redArg___lam__0(v_x_702_);
lean_dec_ref(v_x_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg(lean_object* v_inst_705_, lean_object* v_inst_706_){
_start:
{
lean_object* v_map_707_; lean_object* v___f_708_; lean_object* v___x_709_; 
v_map_707_ = lean_ctor_get(v_inst_706_, 0);
lean_inc(v_map_707_);
lean_dec_ref(v_inst_706_);
v___f_708_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_709_ = lean_apply_4(v_map_707_, lean_box(0), lean_box(0), v___f_708_, v_inst_705_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object* v_m_710_, lean_object* v_inst_711_, lean_object* v_inst_712_){
_start:
{
lean_object* v_map_713_; lean_object* v___f_714_; lean_object* v___x_715_; 
v_map_713_ = lean_ctor_get(v_inst_712_, 0);
lean_inc(v_map_713_);
lean_dec_ref(v_inst_712_);
v___f_714_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_715_ = lean_apply_4(v_map_713_, lean_box(0), lean_box(0), v___f_714_, v_inst_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___redArg(lean_object* v_inst_717_, lean_object* v_inst_718_){
_start:
{
lean_object* v_map_719_; lean_object* v___f_720_; lean_object* v___x_721_; 
v_map_719_ = lean_ctor_get(v_inst_718_, 0);
lean_inc(v_map_719_);
lean_dec_ref(v_inst_718_);
v___f_720_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_721_ = lean_apply_4(v_map_719_, lean_box(0), lean_box(0), v___f_720_, v_inst_717_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object* v_m_722_, lean_object* v_inst_723_, lean_object* v_inst_724_){
_start:
{
lean_object* v_map_725_; lean_object* v___f_726_; lean_object* v___x_727_; 
v_map_725_ = lean_ctor_get(v_inst_724_, 0);
lean_inc(v_map_725_);
lean_dec_ref(v_inst_724_);
v___f_726_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_727_ = lean_apply_4(v_map_725_, lean_box(0), lean_box(0), v___f_726_, v_inst_723_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___redArg(lean_object* v_inst_729_, lean_object* v_inst_730_){
_start:
{
lean_object* v_map_731_; lean_object* v___f_732_; lean_object* v___x_733_; 
v_map_731_ = lean_ctor_get(v_inst_730_, 0);
lean_inc(v_map_731_);
lean_dec_ref(v_inst_730_);
v___f_732_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_733_ = lean_apply_4(v_map_731_, lean_box(0), lean_box(0), v___f_732_, v_inst_729_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object* v_m_734_, lean_object* v_inst_735_, lean_object* v_inst_736_){
_start:
{
lean_object* v_map_737_; lean_object* v___f_738_; lean_object* v___x_739_; 
v_map_737_ = lean_ctor_get(v_inst_736_, 0);
lean_inc(v_map_737_);
lean_dec_ref(v_inst_736_);
v___f_738_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_739_ = lean_apply_4(v_map_737_, lean_box(0), lean_box(0), v___f_738_, v_inst_735_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___redArg(lean_object* v_inst_741_, lean_object* v_inst_742_){
_start:
{
lean_object* v_map_743_; lean_object* v___f_744_; lean_object* v___x_745_; 
v_map_743_ = lean_ctor_get(v_inst_742_, 0);
lean_inc(v_map_743_);
lean_dec_ref(v_inst_742_);
v___f_744_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_745_ = lean_apply_4(v_map_743_, lean_box(0), lean_box(0), v___f_744_, v_inst_741_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object* v_m_746_, lean_object* v_inst_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v_map_749_; lean_object* v___f_750_; lean_object* v___x_751_; 
v_map_749_ = lean_ctor_get(v_inst_748_, 0);
lean_inc(v_map_749_);
lean_dec_ref(v_inst_748_);
v___f_750_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_751_ = lean_apply_4(v_map_749_, lean_box(0), lean_box(0), v___f_750_, v_inst_747_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0(lean_object* v_x_752_){
_start:
{
lean_object* v_elan_x3f_753_; 
v_elan_x3f_753_ = lean_ctor_get(v_x_752_, 2);
lean_inc(v_elan_x3f_753_);
return v_elan_x3f_753_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0___boxed(lean_object* v_x_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lake_getElanInstall_x3f___redArg___lam__0(v_x_754_);
lean_dec_ref(v_x_754_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v_map_759_; lean_object* v___f_760_; lean_object* v___x_761_; 
v_map_759_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_map_759_);
lean_dec_ref(v_inst_758_);
v___f_760_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_761_ = lean_apply_4(v_map_759_, lean_box(0), lean_box(0), v___f_760_, v_inst_757_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object* v_m_762_, lean_object* v_inst_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v_map_765_; lean_object* v___f_766_; lean_object* v___x_767_; 
v_map_765_ = lean_ctor_get(v_inst_764_, 0);
lean_inc(v_map_765_);
lean_dec_ref(v_inst_764_);
v___f_766_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_767_ = lean_apply_4(v_map_765_, lean_box(0), lean_box(0), v___f_766_, v_inst_763_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg___lam__0(lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v___x_769_; 
v___x_769_ = lean_box(0);
return v___x_769_;
}
else
{
lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
v_val_770_ = lean_ctor_get(v_x_768_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_778_ == 0)
{
v___x_772_ = v_x_768_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v_x_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_home_774_; lean_object* v___x_776_; 
v_home_774_ = lean_ctor_get(v_val_770_, 0);
lean_inc_ref(v_home_774_);
lean_dec(v_val_770_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_home_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_home_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg(lean_object* v_inst_780_, lean_object* v_inst_781_){
_start:
{
lean_object* v_map_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_map_782_ = lean_ctor_get(v_inst_781_, 0);
lean_inc_n(v_map_782_, 2);
lean_dec_ref(v_inst_781_);
v___f_783_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_784_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_785_ = lean_apply_4(v_map_782_, lean_box(0), lean_box(0), v___f_784_, v_inst_780_);
v___x_786_ = lean_apply_4(v_map_782_, lean_box(0), lean_box(0), v___f_783_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_inst_789_){
_start:
{
lean_object* v_map_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_map_790_ = lean_ctor_get(v_inst_789_, 0);
lean_inc_n(v_map_790_, 2);
lean_dec_ref(v_inst_789_);
v___f_791_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_792_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_793_ = lean_apply_4(v_map_790_, lean_box(0), lean_box(0), v___f_792_, v_inst_788_);
v___x_794_ = lean_apply_4(v_map_790_, lean_box(0), lean_box(0), v___f_791_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg___lam__0(lean_object* v_x_795_){
_start:
{
if (lean_obj_tag(v_x_795_) == 0)
{
lean_object* v___x_796_; 
v___x_796_ = lean_box(0);
return v___x_796_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_val_797_ = lean_ctor_get(v_x_795_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_x_795_);
if (v_isSharedCheck_805_ == 0)
{
v___x_799_ = v_x_795_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_val_797_);
lean_dec(v_x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_elan_801_; lean_object* v___x_803_; 
v_elan_801_ = lean_ctor_get(v_val_797_, 1);
lean_inc_ref(v_elan_801_);
lean_dec(v_val_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_elan_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_elan_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg(lean_object* v_inst_807_, lean_object* v_inst_808_){
_start:
{
lean_object* v_map_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_map_809_ = lean_ctor_get(v_inst_808_, 0);
lean_inc_n(v_map_809_, 2);
lean_dec_ref(v_inst_808_);
v___f_810_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_811_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_812_ = lean_apply_4(v_map_809_, lean_box(0), lean_box(0), v___f_811_, v_inst_807_);
v___x_813_ = lean_apply_4(v_map_809_, lean_box(0), lean_box(0), v___f_810_, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object* v_m_814_, lean_object* v_inst_815_, lean_object* v_inst_816_){
_start:
{
lean_object* v_map_817_; lean_object* v___f_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_map_817_ = lean_ctor_get(v_inst_816_, 0);
lean_inc_n(v_map_817_, 2);
lean_dec_ref(v_inst_816_);
v___f_818_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_819_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_820_ = lean_apply_4(v_map_817_, lean_box(0), lean_box(0), v___f_819_, v_inst_815_);
v___x_821_ = lean_apply_4(v_map_817_, lean_box(0), lean_box(0), v___f_818_, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0(lean_object* v_x_822_){
_start:
{
lean_object* v_lean_823_; 
v_lean_823_ = lean_ctor_get(v_x_822_, 1);
lean_inc_ref(v_lean_823_);
return v_lean_823_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0___boxed(lean_object* v_x_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lake_getLeanInstall___redArg___lam__0(v_x_824_);
lean_dec_ref(v_x_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg(lean_object* v_inst_827_, lean_object* v_inst_828_){
_start:
{
lean_object* v_map_829_; lean_object* v___f_830_; lean_object* v___x_831_; 
v_map_829_ = lean_ctor_get(v_inst_828_, 0);
lean_inc(v_map_829_);
lean_dec_ref(v_inst_828_);
v___f_830_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_831_ = lean_apply_4(v_map_829_, lean_box(0), lean_box(0), v___f_830_, v_inst_827_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object* v_m_832_, lean_object* v_inst_833_, lean_object* v_inst_834_){
_start:
{
lean_object* v_map_835_; lean_object* v___f_836_; lean_object* v___x_837_; 
v_map_835_ = lean_ctor_get(v_inst_834_, 0);
lean_inc(v_map_835_);
lean_dec_ref(v_inst_834_);
v___f_836_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_837_ = lean_apply_4(v_map_835_, lean_box(0), lean_box(0), v___f_836_, v_inst_833_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0(lean_object* v_x_838_){
_start:
{
lean_object* v_sysroot_839_; 
v_sysroot_839_ = lean_ctor_get(v_x_838_, 0);
lean_inc_ref(v_sysroot_839_);
return v_sysroot_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0___boxed(lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lake_getLeanSysroot___redArg___lam__0(v_x_840_);
lean_dec_ref(v_x_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg(lean_object* v_inst_843_, lean_object* v_inst_844_){
_start:
{
lean_object* v_map_845_; lean_object* v___f_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_map_845_ = lean_ctor_get(v_inst_844_, 0);
lean_inc_n(v_map_845_, 2);
lean_dec_ref(v_inst_844_);
v___f_846_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_847_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_848_ = lean_apply_4(v_map_845_, lean_box(0), lean_box(0), v___f_847_, v_inst_843_);
v___x_849_ = lean_apply_4(v_map_845_, lean_box(0), lean_box(0), v___f_846_, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object* v_m_850_, lean_object* v_inst_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v_map_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_map_853_ = lean_ctor_get(v_inst_852_, 0);
lean_inc_n(v_map_853_, 2);
lean_dec_ref(v_inst_852_);
v___f_854_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_855_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_856_ = lean_apply_4(v_map_853_, lean_box(0), lean_box(0), v___f_855_, v_inst_851_);
v___x_857_ = lean_apply_4(v_map_853_, lean_box(0), lean_box(0), v___f_854_, v___x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0(lean_object* v_x_858_){
_start:
{
lean_object* v_srcDir_859_; 
v_srcDir_859_ = lean_ctor_get(v_x_858_, 2);
lean_inc_ref(v_srcDir_859_);
return v_srcDir_859_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0___boxed(lean_object* v_x_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lake_getLeanSrcDir___redArg___lam__0(v_x_860_);
lean_dec_ref(v_x_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg(lean_object* v_inst_863_, lean_object* v_inst_864_){
_start:
{
lean_object* v_map_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_map_865_ = lean_ctor_get(v_inst_864_, 0);
lean_inc_n(v_map_865_, 2);
lean_dec_ref(v_inst_864_);
v___f_866_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_867_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_868_ = lean_apply_4(v_map_865_, lean_box(0), lean_box(0), v___f_867_, v_inst_863_);
v___x_869_ = lean_apply_4(v_map_865_, lean_box(0), lean_box(0), v___f_866_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object* v_m_870_, lean_object* v_inst_871_, lean_object* v_inst_872_){
_start:
{
lean_object* v_map_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_map_873_ = lean_ctor_get(v_inst_872_, 0);
lean_inc_n(v_map_873_, 2);
lean_dec_ref(v_inst_872_);
v___f_874_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_875_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_876_ = lean_apply_4(v_map_873_, lean_box(0), lean_box(0), v___f_875_, v_inst_871_);
v___x_877_ = lean_apply_4(v_map_873_, lean_box(0), lean_box(0), v___f_874_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0(lean_object* v_x_878_){
_start:
{
lean_object* v_leanLibDir_879_; 
v_leanLibDir_879_ = lean_ctor_get(v_x_878_, 3);
lean_inc_ref(v_leanLibDir_879_);
return v_leanLibDir_879_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0___boxed(lean_object* v_x_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lake_getLeanLibDir___redArg___lam__0(v_x_880_);
lean_dec_ref(v_x_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg(lean_object* v_inst_883_, lean_object* v_inst_884_){
_start:
{
lean_object* v_map_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_map_885_ = lean_ctor_get(v_inst_884_, 0);
lean_inc_n(v_map_885_, 2);
lean_dec_ref(v_inst_884_);
v___f_886_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_887_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_888_ = lean_apply_4(v_map_885_, lean_box(0), lean_box(0), v___f_887_, v_inst_883_);
v___x_889_ = lean_apply_4(v_map_885_, lean_box(0), lean_box(0), v___f_886_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object* v_m_890_, lean_object* v_inst_891_, lean_object* v_inst_892_){
_start:
{
lean_object* v_map_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_map_893_ = lean_ctor_get(v_inst_892_, 0);
lean_inc_n(v_map_893_, 2);
lean_dec_ref(v_inst_892_);
v___f_894_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_895_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_896_ = lean_apply_4(v_map_893_, lean_box(0), lean_box(0), v___f_895_, v_inst_891_);
v___x_897_ = lean_apply_4(v_map_893_, lean_box(0), lean_box(0), v___f_894_, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0(lean_object* v_x_898_){
_start:
{
lean_object* v_includeDir_899_; 
v_includeDir_899_ = lean_ctor_get(v_x_898_, 4);
lean_inc_ref(v_includeDir_899_);
return v_includeDir_899_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0___boxed(lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lake_getLeanIncludeDir___redArg___lam__0(v_x_900_);
lean_dec_ref(v_x_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg(lean_object* v_inst_903_, lean_object* v_inst_904_){
_start:
{
lean_object* v_map_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_map_905_ = lean_ctor_get(v_inst_904_, 0);
lean_inc_n(v_map_905_, 2);
lean_dec_ref(v_inst_904_);
v___f_906_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_907_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_908_ = lean_apply_4(v_map_905_, lean_box(0), lean_box(0), v___f_907_, v_inst_903_);
v___x_909_ = lean_apply_4(v_map_905_, lean_box(0), lean_box(0), v___f_906_, v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object* v_m_910_, lean_object* v_inst_911_, lean_object* v_inst_912_){
_start:
{
lean_object* v_map_913_; lean_object* v___f_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_map_913_ = lean_ctor_get(v_inst_912_, 0);
lean_inc_n(v_map_913_, 2);
lean_dec_ref(v_inst_912_);
v___f_914_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_915_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_916_ = lean_apply_4(v_map_913_, lean_box(0), lean_box(0), v___f_915_, v_inst_911_);
v___x_917_ = lean_apply_4(v_map_913_, lean_box(0), lean_box(0), v___f_914_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0(lean_object* v_x_918_){
_start:
{
lean_object* v_systemLibDir_919_; 
v_systemLibDir_919_ = lean_ctor_get(v_x_918_, 5);
lean_inc_ref(v_systemLibDir_919_);
return v_systemLibDir_919_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed(lean_object* v_x_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lake_getLeanSystemLibDir___redArg___lam__0(v_x_920_);
lean_dec_ref(v_x_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg(lean_object* v_inst_923_, lean_object* v_inst_924_){
_start:
{
lean_object* v_map_925_; lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_map_925_ = lean_ctor_get(v_inst_924_, 0);
lean_inc_n(v_map_925_, 2);
lean_dec_ref(v_inst_924_);
v___f_926_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_927_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_928_ = lean_apply_4(v_map_925_, lean_box(0), lean_box(0), v___f_927_, v_inst_923_);
v___x_929_ = lean_apply_4(v_map_925_, lean_box(0), lean_box(0), v___f_926_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_inst_932_){
_start:
{
lean_object* v_map_933_; lean_object* v___f_934_; lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_map_933_ = lean_ctor_get(v_inst_932_, 0);
lean_inc_n(v_map_933_, 2);
lean_dec_ref(v_inst_932_);
v___f_934_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_935_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_936_ = lean_apply_4(v_map_933_, lean_box(0), lean_box(0), v___f_935_, v_inst_931_);
v___x_937_ = lean_apply_4(v_map_933_, lean_box(0), lean_box(0), v___f_934_, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0(lean_object* v_x_938_){
_start:
{
lean_object* v_lean_939_; 
v_lean_939_ = lean_ctor_get(v_x_938_, 7);
lean_inc_ref(v_lean_939_);
return v_lean_939_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0___boxed(lean_object* v_x_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lake_getLean___redArg___lam__0(v_x_940_);
lean_dec_ref(v_x_940_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg(lean_object* v_inst_943_, lean_object* v_inst_944_){
_start:
{
lean_object* v_map_945_; lean_object* v___f_946_; lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_map_945_ = lean_ctor_get(v_inst_944_, 0);
lean_inc_n(v_map_945_, 2);
lean_dec_ref(v_inst_944_);
v___f_946_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_947_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_948_ = lean_apply_4(v_map_945_, lean_box(0), lean_box(0), v___f_947_, v_inst_943_);
v___x_949_ = lean_apply_4(v_map_945_, lean_box(0), lean_box(0), v___f_946_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object* v_m_950_, lean_object* v_inst_951_, lean_object* v_inst_952_){
_start:
{
lean_object* v_map_953_; lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_map_953_ = lean_ctor_get(v_inst_952_, 0);
lean_inc_n(v_map_953_, 2);
lean_dec_ref(v_inst_952_);
v___f_954_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_955_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_956_ = lean_apply_4(v_map_953_, lean_box(0), lean_box(0), v___f_955_, v_inst_951_);
v___x_957_ = lean_apply_4(v_map_953_, lean_box(0), lean_box(0), v___f_954_, v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0(lean_object* v_x_958_){
_start:
{
lean_object* v_leanir_959_; 
v_leanir_959_ = lean_ctor_get(v_x_958_, 8);
lean_inc_ref(v_leanir_959_);
return v_leanir_959_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0___boxed(lean_object* v_x_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lake_getLeanir___redArg___lam__0(v_x_960_);
lean_dec_ref(v_x_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg(lean_object* v_inst_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v_map_965_; lean_object* v___f_966_; lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_map_965_ = lean_ctor_get(v_inst_964_, 0);
lean_inc_n(v_map_965_, 2);
lean_dec_ref(v_inst_964_);
v___f_966_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_967_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_968_ = lean_apply_4(v_map_965_, lean_box(0), lean_box(0), v___f_967_, v_inst_963_);
v___x_969_ = lean_apply_4(v_map_965_, lean_box(0), lean_box(0), v___f_966_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir(lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_inst_972_){
_start:
{
lean_object* v_map_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_map_973_ = lean_ctor_get(v_inst_972_, 0);
lean_inc_n(v_map_973_, 2);
lean_dec_ref(v_inst_972_);
v___f_974_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_975_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_976_ = lean_apply_4(v_map_973_, lean_box(0), lean_box(0), v___f_975_, v_inst_971_);
v___x_977_ = lean_apply_4(v_map_973_, lean_box(0), lean_box(0), v___f_974_, v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0(lean_object* v_x_978_){
_start:
{
lean_object* v_leanc_979_; 
v_leanc_979_ = lean_ctor_get(v_x_978_, 9);
lean_inc_ref(v_leanc_979_);
return v_leanc_979_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0___boxed(lean_object* v_x_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lake_getLeanc___redArg___lam__0(v_x_980_);
lean_dec_ref(v_x_980_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg(lean_object* v_inst_983_, lean_object* v_inst_984_){
_start:
{
lean_object* v_map_985_; lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_map_985_ = lean_ctor_get(v_inst_984_, 0);
lean_inc_n(v_map_985_, 2);
lean_dec_ref(v_inst_984_);
v___f_986_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_987_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_988_ = lean_apply_4(v_map_985_, lean_box(0), lean_box(0), v___f_987_, v_inst_983_);
v___x_989_ = lean_apply_4(v_map_985_, lean_box(0), lean_box(0), v___f_986_, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object* v_m_990_, lean_object* v_inst_991_, lean_object* v_inst_992_){
_start:
{
lean_object* v_map_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_map_993_ = lean_ctor_get(v_inst_992_, 0);
lean_inc_n(v_map_993_, 2);
lean_dec_ref(v_inst_992_);
v___f_994_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_995_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_996_ = lean_apply_4(v_map_993_, lean_box(0), lean_box(0), v___f_995_, v_inst_991_);
v___x_997_ = lean_apply_4(v_map_993_, lean_box(0), lean_box(0), v___f_994_, v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0(lean_object* v_x_998_){
_start:
{
lean_object* v_leantar_999_; 
v_leantar_999_ = lean_ctor_get(v_x_998_, 10);
lean_inc_ref(v_leantar_999_);
return v_leantar_999_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0___boxed(lean_object* v_x_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lake_getLeantar___redArg___lam__0(v_x_1000_);
lean_dec_ref(v_x_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg(lean_object* v_inst_1003_, lean_object* v_inst_1004_){
_start:
{
lean_object* v_map_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_map_1005_ = lean_ctor_get(v_inst_1004_, 0);
lean_inc_n(v_map_1005_, 2);
lean_dec_ref(v_inst_1004_);
v___f_1006_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1007_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1008_ = lean_apply_4(v_map_1005_, lean_box(0), lean_box(0), v___f_1007_, v_inst_1003_);
v___x_1009_ = lean_apply_4(v_map_1005_, lean_box(0), lean_box(0), v___f_1006_, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar(lean_object* v_m_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_){
_start:
{
lean_object* v_map_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_map_1013_ = lean_ctor_get(v_inst_1012_, 0);
lean_inc_n(v_map_1013_, 2);
lean_dec_ref(v_inst_1012_);
v___f_1014_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1015_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1016_ = lean_apply_4(v_map_1013_, lean_box(0), lean_box(0), v___f_1015_, v_inst_1011_);
v___x_1017_ = lean_apply_4(v_map_1013_, lean_box(0), lean_box(0), v___f_1014_, v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg___lam__0(lean_object* v_x_1018_){
_start:
{
lean_object* v_sharedDynlib_1019_; 
v_sharedDynlib_1019_ = lean_ctor_get(v_x_1018_, 12);
lean_inc_ref(v_sharedDynlib_1019_);
return v_sharedDynlib_1019_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg___lam__0___boxed(lean_object* v_x_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lake_getLeanSharedDynlib___redArg___lam__0(v_x_1020_);
lean_dec_ref(v_x_1020_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg(lean_object* v_inst_1023_, lean_object* v_inst_1024_){
_start:
{
lean_object* v_map_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_map_1025_ = lean_ctor_get(v_inst_1024_, 0);
lean_inc_n(v_map_1025_, 2);
lean_dec_ref(v_inst_1024_);
v___f_1026_ = ((lean_object*)(l_Lake_getLeanSharedDynlib___redArg___closed__0));
v___f_1027_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1028_ = lean_apply_4(v_map_1025_, lean_box(0), lean_box(0), v___f_1027_, v_inst_1023_);
v___x_1029_ = lean_apply_4(v_map_1025_, lean_box(0), lean_box(0), v___f_1026_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib(lean_object* v_m_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v_map_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_map_1033_ = lean_ctor_get(v_inst_1032_, 0);
lean_inc_n(v_map_1033_, 2);
lean_dec_ref(v_inst_1032_);
v___f_1034_ = ((lean_object*)(l_Lake_getLeanSharedDynlib___redArg___closed__0));
v___f_1035_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1036_ = lean_apply_4(v_map_1033_, lean_box(0), lean_box(0), v___f_1035_, v_inst_1031_);
v___x_1037_ = lean_apply_4(v_map_1033_, lean_box(0), lean_box(0), v___f_1034_, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg___lam__0(lean_object* v_x_1038_){
_start:
{
lean_object* v_sharedDynlibs_1039_; 
v_sharedDynlibs_1039_ = lean_ctor_get(v_x_1038_, 11);
lean_inc_ref(v_sharedDynlibs_1039_);
return v_sharedDynlibs_1039_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg___lam__0___boxed(lean_object* v_x_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lake_getLeanSharedDynlibs___redArg___lam__0(v_x_1040_);
lean_dec_ref(v_x_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_){
_start:
{
lean_object* v_map_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_map_1045_ = lean_ctor_get(v_inst_1044_, 0);
lean_inc_n(v_map_1045_, 2);
lean_dec_ref(v_inst_1044_);
v___f_1046_ = ((lean_object*)(l_Lake_getLeanSharedDynlibs___redArg___closed__0));
v___f_1047_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1048_ = lean_apply_4(v_map_1045_, lean_box(0), lean_box(0), v___f_1047_, v_inst_1043_);
v___x_1049_ = lean_apply_4(v_map_1045_, lean_box(0), lean_box(0), v___f_1046_, v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs(lean_object* v_m_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v_map_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v_map_1053_ = lean_ctor_get(v_inst_1052_, 0);
lean_inc_n(v_map_1053_, 2);
lean_dec_ref(v_inst_1052_);
v___f_1054_ = ((lean_object*)(l_Lake_getLeanSharedDynlibs___redArg___closed__0));
v___f_1055_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1056_ = lean_apply_4(v_map_1053_, lean_box(0), lean_box(0), v___f_1055_, v_inst_1051_);
v___x_1057_ = lean_apply_4(v_map_1053_, lean_box(0), lean_box(0), v___f_1054_, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0(lean_object* v_x_1058_){
_start:
{
lean_object* v_sharedDynlib_1059_; lean_object* v_path_1060_; 
v_sharedDynlib_1059_ = lean_ctor_get(v_x_1058_, 12);
v_path_1060_ = lean_ctor_get(v_sharedDynlib_1059_, 0);
lean_inc_ref(v_path_1060_);
return v_path_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0___boxed(lean_object* v_x_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lake_getLeanSharedLib___redArg___lam__0(v_x_1061_);
lean_dec_ref(v_x_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg(lean_object* v_inst_1064_, lean_object* v_inst_1065_){
_start:
{
lean_object* v_map_1066_; lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_map_1066_ = lean_ctor_get(v_inst_1065_, 0);
lean_inc_n(v_map_1066_, 2);
lean_dec_ref(v_inst_1065_);
v___f_1067_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1068_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1069_ = lean_apply_4(v_map_1066_, lean_box(0), lean_box(0), v___f_1068_, v_inst_1064_);
v___x_1070_ = lean_apply_4(v_map_1066_, lean_box(0), lean_box(0), v___f_1067_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object* v_m_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_){
_start:
{
lean_object* v_map_1074_; lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_map_1074_ = lean_ctor_get(v_inst_1073_, 0);
lean_inc_n(v_map_1074_, 2);
lean_dec_ref(v_inst_1073_);
v___f_1075_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1076_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1077_ = lean_apply_4(v_map_1074_, lean_box(0), lean_box(0), v___f_1076_, v_inst_1072_);
v___x_1078_ = lean_apply_4(v_map_1074_, lean_box(0), lean_box(0), v___f_1075_, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0(lean_object* v_x_1079_){
_start:
{
lean_object* v_ar_1080_; 
v_ar_1080_ = lean_ctor_get(v_x_1079_, 13);
lean_inc_ref(v_ar_1080_);
return v_ar_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0___boxed(lean_object* v_x_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lake_getLeanAr___redArg___lam__0(v_x_1081_);
lean_dec_ref(v_x_1081_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg(lean_object* v_inst_1084_, lean_object* v_inst_1085_){
_start:
{
lean_object* v_map_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_map_1086_ = lean_ctor_get(v_inst_1085_, 0);
lean_inc_n(v_map_1086_, 2);
lean_dec_ref(v_inst_1085_);
v___f_1087_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1088_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1089_ = lean_apply_4(v_map_1086_, lean_box(0), lean_box(0), v___f_1088_, v_inst_1084_);
v___x_1090_ = lean_apply_4(v_map_1086_, lean_box(0), lean_box(0), v___f_1087_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object* v_m_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_){
_start:
{
lean_object* v_map_1094_; lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_map_1094_ = lean_ctor_get(v_inst_1093_, 0);
lean_inc_n(v_map_1094_, 2);
lean_dec_ref(v_inst_1093_);
v___f_1095_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1096_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1097_ = lean_apply_4(v_map_1094_, lean_box(0), lean_box(0), v___f_1096_, v_inst_1092_);
v___x_1098_ = lean_apply_4(v_map_1094_, lean_box(0), lean_box(0), v___f_1095_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0(lean_object* v_x_1099_){
_start:
{
lean_object* v_cc_1100_; 
v_cc_1100_ = lean_ctor_get(v_x_1099_, 14);
lean_inc_ref(v_cc_1100_);
return v_cc_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0___boxed(lean_object* v_x_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lake_getLeanCc___redArg___lam__0(v_x_1101_);
lean_dec_ref(v_x_1101_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg(lean_object* v_inst_1104_, lean_object* v_inst_1105_){
_start:
{
lean_object* v_map_1106_; lean_object* v___f_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_map_1106_ = lean_ctor_get(v_inst_1105_, 0);
lean_inc_n(v_map_1106_, 2);
lean_dec_ref(v_inst_1105_);
v___f_1107_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1108_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1109_ = lean_apply_4(v_map_1106_, lean_box(0), lean_box(0), v___f_1108_, v_inst_1104_);
v___x_1110_ = lean_apply_4(v_map_1106_, lean_box(0), lean_box(0), v___f_1107_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object* v_m_1111_, lean_object* v_inst_1112_, lean_object* v_inst_1113_){
_start:
{
lean_object* v_map_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_map_1114_ = lean_ctor_get(v_inst_1113_, 0);
lean_inc_n(v_map_1114_, 2);
lean_dec_ref(v_inst_1113_);
v___f_1115_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1116_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1117_ = lean_apply_4(v_map_1114_, lean_box(0), lean_box(0), v___f_1116_, v_inst_1112_);
v___x_1118_ = lean_apply_4(v_map_1114_, lean_box(0), lean_box(0), v___f_1115_, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___redArg(lean_object* v_inst_1120_, lean_object* v_inst_1121_){
_start:
{
lean_object* v_map_1122_; lean_object* v___f_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_map_1122_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc_n(v_map_1122_, 2);
lean_dec_ref(v_inst_1121_);
v___f_1123_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1124_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1125_ = lean_apply_4(v_map_1122_, lean_box(0), lean_box(0), v___f_1124_, v_inst_1120_);
v___x_1126_ = lean_apply_4(v_map_1122_, lean_box(0), lean_box(0), v___f_1123_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object* v_m_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_){
_start:
{
lean_object* v_map_1130_; lean_object* v___f_1131_; lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_map_1130_ = lean_ctor_get(v_inst_1129_, 0);
lean_inc_n(v_map_1130_, 2);
lean_dec_ref(v_inst_1129_);
v___f_1131_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1132_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1133_ = lean_apply_4(v_map_1130_, lean_box(0), lean_box(0), v___f_1132_, v_inst_1128_);
v___x_1134_ = lean_apply_4(v_map_1130_, lean_box(0), lean_box(0), v___f_1131_, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0(lean_object* v_x_1135_){
_start:
{
lean_object* v_ccLinkSharedFlags_1136_; 
v_ccLinkSharedFlags_1136_ = lean_ctor_get(v_x_1135_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1136_);
return v_ccLinkSharedFlags_1136_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed(lean_object* v_x_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lake_getLeanLinkSharedFlags___redArg___lam__0(v_x_1137_);
lean_dec_ref(v_x_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg(lean_object* v_inst_1140_, lean_object* v_inst_1141_){
_start:
{
lean_object* v_map_1142_; lean_object* v___f_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_map_1142_ = lean_ctor_get(v_inst_1141_, 0);
lean_inc_n(v_map_1142_, 2);
lean_dec_ref(v_inst_1141_);
v___f_1143_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1144_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1145_ = lean_apply_4(v_map_1142_, lean_box(0), lean_box(0), v___f_1144_, v_inst_1140_);
v___x_1146_ = lean_apply_4(v_map_1142_, lean_box(0), lean_box(0), v___f_1143_, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags(lean_object* v_m_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_){
_start:
{
lean_object* v_map_1150_; lean_object* v___f_1151_; lean_object* v___f_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_map_1150_ = lean_ctor_get(v_inst_1149_, 0);
lean_inc_n(v_map_1150_, 2);
lean_dec_ref(v_inst_1149_);
v___f_1151_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1152_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1153_ = lean_apply_4(v_map_1150_, lean_box(0), lean_box(0), v___f_1152_, v_inst_1148_);
v___x_1154_ = lean_apply_4(v_map_1150_, lean_box(0), lean_box(0), v___f_1151_, v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0(lean_object* v_x_1155_){
_start:
{
lean_object* v_lake_1156_; 
v_lake_1156_ = lean_ctor_get(v_x_1155_, 0);
lean_inc_ref(v_lake_1156_);
return v_lake_1156_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0___boxed(lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lake_getLakeInstall___redArg___lam__0(v_x_1157_);
lean_dec_ref(v_x_1157_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg(lean_object* v_inst_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v_map_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
v_map_1162_ = lean_ctor_get(v_inst_1161_, 0);
lean_inc(v_map_1162_);
lean_dec_ref(v_inst_1161_);
v___f_1163_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1164_ = lean_apply_4(v_map_1162_, lean_box(0), lean_box(0), v___f_1163_, v_inst_1160_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object* v_m_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v_map_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; 
v_map_1168_ = lean_ctor_get(v_inst_1167_, 0);
lean_inc(v_map_1168_);
lean_dec_ref(v_inst_1167_);
v___f_1169_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1170_ = lean_apply_4(v_map_1168_, lean_box(0), lean_box(0), v___f_1169_, v_inst_1166_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0(lean_object* v_x_1171_){
_start:
{
lean_object* v_home_1172_; 
v_home_1172_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_home_1172_);
return v_home_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0___boxed(lean_object* v_x_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lake_getLakeHome___redArg___lam__0(v_x_1173_);
lean_dec_ref(v_x_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg(lean_object* v_inst_1176_, lean_object* v_inst_1177_){
_start:
{
lean_object* v_map_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_map_1178_ = lean_ctor_get(v_inst_1177_, 0);
lean_inc_n(v_map_1178_, 2);
lean_dec_ref(v_inst_1177_);
v___f_1179_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1180_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1181_ = lean_apply_4(v_map_1178_, lean_box(0), lean_box(0), v___f_1180_, v_inst_1176_);
v___x_1182_ = lean_apply_4(v_map_1178_, lean_box(0), lean_box(0), v___f_1179_, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_){
_start:
{
lean_object* v_map_1186_; lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_map_1186_ = lean_ctor_get(v_inst_1185_, 0);
lean_inc_n(v_map_1186_, 2);
lean_dec_ref(v_inst_1185_);
v___f_1187_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1188_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1189_ = lean_apply_4(v_map_1186_, lean_box(0), lean_box(0), v___f_1188_, v_inst_1184_);
v___x_1190_ = lean_apply_4(v_map_1186_, lean_box(0), lean_box(0), v___f_1187_, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0(lean_object* v_x_1191_){
_start:
{
lean_object* v_srcDir_1192_; 
v_srcDir_1192_ = lean_ctor_get(v_x_1191_, 1);
lean_inc_ref(v_srcDir_1192_);
return v_srcDir_1192_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0___boxed(lean_object* v_x_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lake_getLakeSrcDir___redArg___lam__0(v_x_1193_);
lean_dec_ref(v_x_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg(lean_object* v_inst_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v_map_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_map_1198_ = lean_ctor_get(v_inst_1197_, 0);
lean_inc_n(v_map_1198_, 2);
lean_dec_ref(v_inst_1197_);
v___f_1199_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1200_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1201_ = lean_apply_4(v_map_1198_, lean_box(0), lean_box(0), v___f_1200_, v_inst_1196_);
v___x_1202_ = lean_apply_4(v_map_1198_, lean_box(0), lean_box(0), v___f_1199_, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object* v_m_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v_map_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_map_1206_ = lean_ctor_get(v_inst_1205_, 0);
lean_inc_n(v_map_1206_, 2);
lean_dec_ref(v_inst_1205_);
v___f_1207_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1208_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1209_ = lean_apply_4(v_map_1206_, lean_box(0), lean_box(0), v___f_1208_, v_inst_1204_);
v___x_1210_ = lean_apply_4(v_map_1206_, lean_box(0), lean_box(0), v___f_1207_, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0(lean_object* v_x_1211_){
_start:
{
lean_object* v_libDir_1212_; 
v_libDir_1212_ = lean_ctor_get(v_x_1211_, 3);
lean_inc_ref(v_libDir_1212_);
return v_libDir_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0___boxed(lean_object* v_x_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lake_getLakeLibDir___redArg___lam__0(v_x_1213_);
lean_dec_ref(v_x_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
lean_object* v_map_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_map_1218_ = lean_ctor_get(v_inst_1217_, 0);
lean_inc_n(v_map_1218_, 2);
lean_dec_ref(v_inst_1217_);
v___f_1219_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1220_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1221_ = lean_apply_4(v_map_1218_, lean_box(0), lean_box(0), v___f_1220_, v_inst_1216_);
v___x_1222_ = lean_apply_4(v_map_1218_, lean_box(0), lean_box(0), v___f_1219_, v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object* v_m_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_){
_start:
{
lean_object* v_map_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_map_1226_ = lean_ctor_get(v_inst_1225_, 0);
lean_inc_n(v_map_1226_, 2);
lean_dec_ref(v_inst_1225_);
v___f_1227_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1228_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1229_ = lean_apply_4(v_map_1226_, lean_box(0), lean_box(0), v___f_1228_, v_inst_1224_);
v___x_1230_ = lean_apply_4(v_map_1226_, lean_box(0), lean_box(0), v___f_1227_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0(lean_object* v_x_1231_){
_start:
{
lean_object* v_lake_1232_; 
v_lake_1232_ = lean_ctor_get(v_x_1231_, 5);
lean_inc_ref(v_lake_1232_);
return v_lake_1232_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0___boxed(lean_object* v_x_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lake_getLake___redArg___lam__0(v_x_1233_);
lean_dec_ref(v_x_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg(lean_object* v_inst_1236_, lean_object* v_inst_1237_){
_start:
{
lean_object* v_map_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_map_1238_ = lean_ctor_get(v_inst_1237_, 0);
lean_inc_n(v_map_1238_, 2);
lean_dec_ref(v_inst_1237_);
v___f_1239_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1240_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1241_ = lean_apply_4(v_map_1238_, lean_box(0), lean_box(0), v___f_1240_, v_inst_1236_);
v___x_1242_ = lean_apply_4(v_map_1238_, lean_box(0), lean_box(0), v___f_1239_, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object* v_m_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_){
_start:
{
lean_object* v_map_1246_; lean_object* v___f_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_map_1246_ = lean_ctor_get(v_inst_1245_, 0);
lean_inc_n(v_map_1246_, 2);
lean_dec_ref(v_inst_1245_);
v___f_1247_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1248_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1249_ = lean_apply_4(v_map_1246_, lean_box(0), lean_box(0), v___f_1248_, v_inst_1244_);
v___x_1250_ = lean_apply_4(v_map_1246_, lean_box(0), lean_box(0), v___f_1247_, v___x_1249_);
return v___x_1250_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Monad(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Monad(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Monad(builtin);
}
#ifdef __cplusplus
}
#endif

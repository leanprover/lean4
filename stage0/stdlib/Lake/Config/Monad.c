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
lean_dec_ref(v_fst_171_);
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
lean_object* v_packages_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_config_518_; lean_object* v_restoreAllArtifacts_x3f_519_; 
v_packages_515_ = lean_ctor_get(v_x_512_, 4);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_array_fget_borrowed(v_packages_515_, v___x_516_);
v_config_518_ = lean_ctor_get(v___x_517_, 6);
v_restoreAllArtifacts_x3f_519_ = lean_ctor_get(v_config_518_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_519_) == 0)
{
uint8_t v___x_520_; 
v___x_520_ = 0;
return v___x_520_;
}
else
{
lean_object* v_val_521_; uint8_t v___x_522_; 
v_val_521_ = lean_ctor_get(v_restoreAllArtifacts_x3f_519_, 0);
v___x_522_ = lean_unbox(v_val_521_);
return v___x_522_;
}
}
else
{
lean_object* v_val_523_; uint8_t v___x_524_; 
v_val_523_ = lean_ctor_get(v_restoreAllArtifacts_x3f_514_, 0);
v___x_524_ = lean_unbox(v_val_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed(lean_object* v_self_525_, lean_object* v_x_526_){
_start:
{
uint8_t v_res_527_; lean_object* v_r_528_; 
v_res_527_ = l_Lake_Package_restoreAllArtifacts___redArg___lam__0(v_self_525_, v_x_526_);
lean_dec_ref(v_x_526_);
lean_dec_ref(v_self_525_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg(lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_self_531_){
_start:
{
lean_object* v_map_532_; lean_object* v___f_533_; lean_object* v___x_534_; 
v_map_532_ = lean_ctor_get(v_inst_529_, 0);
lean_inc(v_map_532_);
lean_dec_ref(v_inst_529_);
v___f_533_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_533_, 0, v_self_531_);
v___x_534_ = lean_apply_4(v_map_532_, lean_box(0), lean_box(0), v___f_533_, v_inst_530_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts(lean_object* v_m_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_self_538_){
_start:
{
lean_object* v_map_539_; lean_object* v___f_540_; lean_object* v___x_541_; 
v_map_539_ = lean_ctor_get(v_inst_536_, 0);
lean_inc(v_map_539_);
lean_dec_ref(v_inst_536_);
v___f_540_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_540_, 0, v_self_538_);
v___x_541_ = lean_apply_4(v_map_539_, lean_box(0), lean_box(0), v___f_540_, v_inst_537_);
return v___x_541_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(lean_object* v_self_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_config_544_; lean_object* v_enableArtifactCache_x3f_545_; 
v_config_544_ = lean_ctor_get(v_self_542_, 6);
v_enableArtifactCache_x3f_545_ = lean_ctor_get(v_config_544_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_545_) == 0)
{
lean_object* v_lakeEnv_546_; lean_object* v_enableArtifactCache_x3f_547_; 
v_lakeEnv_546_ = lean_ctor_get(v_x_543_, 0);
v_enableArtifactCache_x3f_547_ = lean_ctor_get(v_lakeEnv_546_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_547_) == 0)
{
lean_object* v_packages_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_config_551_; lean_object* v_enableArtifactCache_x3f_552_; 
v_packages_548_ = lean_ctor_get(v_x_543_, 4);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_array_fget_borrowed(v_packages_548_, v___x_549_);
v_config_551_ = lean_ctor_get(v___x_550_, 6);
v_enableArtifactCache_x3f_552_ = lean_ctor_get(v_config_551_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_552_) == 0)
{
uint8_t v___x_553_; 
v___x_553_ = 1;
return v___x_553_;
}
else
{
lean_object* v_val_554_; uint8_t v___x_555_; 
v_val_554_ = lean_ctor_get(v_enableArtifactCache_x3f_552_, 0);
v___x_555_ = lean_unbox(v_val_554_);
return v___x_555_;
}
}
else
{
lean_object* v_val_556_; uint8_t v___x_557_; 
v_val_556_ = lean_ctor_get(v_enableArtifactCache_x3f_547_, 0);
v___x_557_ = lean_unbox(v_val_556_);
return v___x_557_;
}
}
else
{
lean_object* v_val_558_; uint8_t v___x_559_; 
v_val_558_ = lean_ctor_get(v_enableArtifactCache_x3f_545_, 0);
v___x_559_ = lean_unbox(v_val_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed(lean_object* v_self_560_, lean_object* v_x_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(v_self_560_, v_x_561_);
lean_dec_ref(v_x_561_);
lean_dec_ref(v_self_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg(lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_self_566_){
_start:
{
lean_object* v_map_567_; lean_object* v___f_568_; lean_object* v___x_569_; 
v_map_567_ = lean_ctor_get(v_inst_564_, 0);
lean_inc(v_map_567_);
lean_dec_ref(v_inst_564_);
v___f_568_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_568_, 0, v_self_566_);
v___x_569_ = lean_apply_4(v_map_567_, lean_box(0), lean_box(0), v___f_568_, v_inst_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable(lean_object* v_m_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_self_573_){
_start:
{
lean_object* v_map_574_; lean_object* v___f_575_; lean_object* v___x_576_; 
v_map_574_ = lean_ctor_get(v_inst_571_, 0);
lean_inc(v_map_574_);
lean_dec_ref(v_inst_571_);
v___f_575_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_575_, 0, v_self_573_);
v___x_576_ = lean_apply_4(v_map_574_, lean_box(0), lean_box(0), v___f_575_, v_inst_572_);
return v___x_576_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(lean_object* v_self_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_config_579_; lean_object* v_enableArtifactCache_x3f_580_; 
v_config_579_ = lean_ctor_get(v_self_577_, 6);
v_enableArtifactCache_x3f_580_ = lean_ctor_get(v_config_579_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_580_) == 0)
{
lean_object* v_lakeEnv_581_; lean_object* v_enableArtifactCache_x3f_582_; 
v_lakeEnv_581_ = lean_ctor_get(v_x_578_, 0);
v_enableArtifactCache_x3f_582_ = lean_ctor_get(v_lakeEnv_581_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_582_) == 0)
{
lean_object* v_packages_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_config_586_; lean_object* v_enableArtifactCache_x3f_587_; 
v_packages_583_ = lean_ctor_get(v_x_578_, 4);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_array_fget_borrowed(v_packages_583_, v___x_584_);
v_config_586_ = lean_ctor_get(v___x_585_, 6);
v_enableArtifactCache_x3f_587_ = lean_ctor_get(v_config_586_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_587_) == 0)
{
uint8_t v___x_588_; 
v___x_588_ = 0;
return v___x_588_;
}
else
{
lean_object* v_val_589_; uint8_t v___x_590_; 
v_val_589_ = lean_ctor_get(v_enableArtifactCache_x3f_587_, 0);
v___x_590_ = lean_unbox(v_val_589_);
return v___x_590_;
}
}
else
{
lean_object* v_val_591_; uint8_t v___x_592_; 
v_val_591_ = lean_ctor_get(v_enableArtifactCache_x3f_582_, 0);
v___x_592_ = lean_unbox(v_val_591_);
return v___x_592_;
}
}
else
{
lean_object* v_val_593_; uint8_t v___x_594_; 
v_val_593_ = lean_ctor_get(v_enableArtifactCache_x3f_580_, 0);
v___x_594_ = lean_unbox(v_val_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed(lean_object* v_self_595_, lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(v_self_595_, v_x_596_);
lean_dec_ref(v_x_596_);
lean_dec_ref(v_self_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg(lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_self_601_){
_start:
{
lean_object* v_map_602_; lean_object* v___f_603_; lean_object* v___x_604_; 
v_map_602_ = lean_ctor_get(v_inst_599_, 0);
lean_inc(v_map_602_);
lean_dec_ref(v_inst_599_);
v___f_603_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_603_, 0, v_self_601_);
v___x_604_ = lean_apply_4(v_map_602_, lean_box(0), lean_box(0), v___f_603_, v_inst_600_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable(lean_object* v_m_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_self_608_){
_start:
{
lean_object* v_map_609_; lean_object* v___f_610_; lean_object* v___x_611_; 
v_map_609_ = lean_ctor_get(v_inst_606_, 0);
lean_inc(v_map_609_);
lean_dec_ref(v_inst_606_);
v___f_610_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_610_, 0, v_self_608_);
v___x_611_ = lean_apply_4(v_map_609_, lean_box(0), lean_box(0), v___f_610_, v_inst_607_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___redArg(lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_self_614_){
_start:
{
lean_object* v_map_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v_map_615_ = lean_ctor_get(v_inst_612_, 0);
lean_inc(v_map_615_);
lean_dec_ref(v_inst_612_);
v___f_616_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_616_, 0, v_self_614_);
v___x_617_ = lean_apply_4(v_map_615_, lean_box(0), lean_box(0), v___f_616_, v_inst_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled(lean_object* v_m_618_, lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_self_621_){
_start:
{
lean_object* v_map_622_; lean_object* v___f_623_; lean_object* v___x_624_; 
v_map_622_ = lean_ctor_get(v_inst_619_, 0);
lean_inc(v_map_622_);
lean_dec_ref(v_inst_619_);
v___f_623_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_623_, 0, v_self_621_);
v___x_624_ = lean_apply_4(v_map_622_, lean_box(0), lean_box(0), v___f_623_, v_inst_620_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg(lean_object* v_inst_625_){
_start:
{
lean_inc(v_inst_625_);
return v_inst_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg___boxed(lean_object* v_inst_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lake_getLakeEnv___redArg(v_inst_626_);
lean_dec(v_inst_626_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv(lean_object* v_m_628_, lean_object* v_inst_629_){
_start:
{
lean_inc(v_inst_629_);
return v_inst_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___boxed(lean_object* v_m_630_, lean_object* v_inst_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lake_getLakeEnv(v_m_630_, v_inst_631_);
lean_dec(v_inst_631_);
return v_res_632_;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoCache___redArg___lam__0(lean_object* v_x_633_){
_start:
{
uint8_t v_noCache_634_; 
v_noCache_634_ = lean_ctor_get_uint8(v_x_633_, sizeof(void*)*19);
return v_noCache_634_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg___lam__0___boxed(lean_object* v_x_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Lake_getNoCache___redArg___lam__0(v_x_635_);
lean_dec_ref(v_x_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg(lean_object* v_inst_639_, lean_object* v_inst_640_){
_start:
{
lean_object* v_map_641_; lean_object* v___f_642_; lean_object* v___x_643_; 
v_map_641_ = lean_ctor_get(v_inst_640_, 0);
lean_inc(v_map_641_);
lean_dec_ref(v_inst_640_);
v___f_642_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_643_ = lean_apply_4(v_map_641_, lean_box(0), lean_box(0), v___f_642_, v_inst_639_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache(lean_object* v_m_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_inst_647_){
_start:
{
lean_object* v_map_648_; lean_object* v___f_649_; lean_object* v___x_650_; 
v_map_648_ = lean_ctor_get(v_inst_646_, 0);
lean_inc(v_map_648_);
lean_dec_ref(v_inst_646_);
v___f_649_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_650_ = lean_apply_4(v_map_648_, lean_box(0), lean_box(0), v___f_649_, v_inst_645_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___boxed(lean_object* v_m_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_inst_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lake_getNoCache(v_m_651_, v_inst_652_, v_inst_653_, v_inst_654_);
lean_dec(v_inst_654_);
return v_res_655_;
}
}
LEAN_EXPORT uint8_t l_Lake_getTryCache___redArg___lam__0(lean_object* v_x_656_){
_start:
{
uint8_t v_noCache_657_; 
v_noCache_657_ = lean_ctor_get_uint8(v_x_656_, sizeof(void*)*19);
if (v_noCache_657_ == 0)
{
uint8_t v___x_658_; 
v___x_658_ = 1;
return v___x_658_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg___lam__0___boxed(lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Lake_getTryCache___redArg___lam__0(v_x_660_);
lean_dec_ref(v_x_660_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg(lean_object* v_inst_664_, lean_object* v_inst_665_){
_start:
{
lean_object* v_map_666_; lean_object* v___f_667_; lean_object* v___x_668_; 
v_map_666_ = lean_ctor_get(v_inst_665_, 0);
lean_inc(v_map_666_);
lean_dec_ref(v_inst_665_);
v___f_667_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_668_ = lean_apply_4(v_map_666_, lean_box(0), lean_box(0), v___f_667_, v_inst_664_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object* v_m_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_){
_start:
{
lean_object* v_map_673_; lean_object* v___f_674_; lean_object* v___x_675_; 
v_map_673_ = lean_ctor_get(v_inst_671_, 0);
lean_inc(v_map_673_);
lean_dec_ref(v_inst_671_);
v___f_674_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_675_ = lean_apply_4(v_map_673_, lean_box(0), lean_box(0), v___f_674_, v_inst_670_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___boxed(lean_object* v_m_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lake_getTryCache(v_m_676_, v_inst_677_, v_inst_678_, v_inst_679_);
lean_dec(v_inst_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0(lean_object* v_x_681_){
_start:
{
lean_object* v_pkgUrlMap_682_; 
v_pkgUrlMap_682_ = lean_ctor_get(v_x_681_, 5);
lean_inc(v_pkgUrlMap_682_);
return v_pkgUrlMap_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0___boxed(lean_object* v_x_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lake_getPkgUrlMap___redArg___lam__0(v_x_683_);
lean_dec_ref(v_x_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg(lean_object* v_inst_686_, lean_object* v_inst_687_){
_start:
{
lean_object* v_map_688_; lean_object* v___f_689_; lean_object* v___x_690_; 
v_map_688_ = lean_ctor_get(v_inst_687_, 0);
lean_inc(v_map_688_);
lean_dec_ref(v_inst_687_);
v___f_689_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_690_ = lean_apply_4(v_map_688_, lean_box(0), lean_box(0), v___f_689_, v_inst_686_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object* v_m_691_, lean_object* v_inst_692_, lean_object* v_inst_693_){
_start:
{
lean_object* v_map_694_; lean_object* v___f_695_; lean_object* v___x_696_; 
v_map_694_ = lean_ctor_get(v_inst_693_, 0);
lean_inc(v_map_694_);
lean_dec_ref(v_inst_693_);
v___f_695_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_696_ = lean_apply_4(v_map_694_, lean_box(0), lean_box(0), v___f_695_, v_inst_692_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0(lean_object* v_x_697_){
_start:
{
lean_object* v_toolchain_698_; 
v_toolchain_698_ = lean_ctor_get(v_x_697_, 18);
lean_inc_ref(v_toolchain_698_);
return v_toolchain_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0___boxed(lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lake_getElanToolchain___redArg___lam__0(v_x_699_);
lean_dec_ref(v_x_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg(lean_object* v_inst_702_, lean_object* v_inst_703_){
_start:
{
lean_object* v_map_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
v_map_704_ = lean_ctor_get(v_inst_703_, 0);
lean_inc(v_map_704_);
lean_dec_ref(v_inst_703_);
v___f_705_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_706_ = lean_apply_4(v_map_704_, lean_box(0), lean_box(0), v___f_705_, v_inst_702_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object* v_m_707_, lean_object* v_inst_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v_map_710_; lean_object* v___f_711_; lean_object* v___x_712_; 
v_map_710_ = lean_ctor_get(v_inst_709_, 0);
lean_inc(v_map_710_);
lean_dec_ref(v_inst_709_);
v___f_711_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_712_ = lean_apply_4(v_map_710_, lean_box(0), lean_box(0), v___f_711_, v_inst_708_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___redArg(lean_object* v_inst_714_, lean_object* v_inst_715_){
_start:
{
lean_object* v_map_716_; lean_object* v___f_717_; lean_object* v___x_718_; 
v_map_716_ = lean_ctor_get(v_inst_715_, 0);
lean_inc(v_map_716_);
lean_dec_ref(v_inst_715_);
v___f_717_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_718_ = lean_apply_4(v_map_716_, lean_box(0), lean_box(0), v___f_717_, v_inst_714_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object* v_m_719_, lean_object* v_inst_720_, lean_object* v_inst_721_){
_start:
{
lean_object* v_map_722_; lean_object* v___f_723_; lean_object* v___x_724_; 
v_map_722_ = lean_ctor_get(v_inst_721_, 0);
lean_inc(v_map_722_);
lean_dec_ref(v_inst_721_);
v___f_723_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_724_ = lean_apply_4(v_map_722_, lean_box(0), lean_box(0), v___f_723_, v_inst_720_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___redArg(lean_object* v_inst_726_, lean_object* v_inst_727_){
_start:
{
lean_object* v_map_728_; lean_object* v___f_729_; lean_object* v___x_730_; 
v_map_728_ = lean_ctor_get(v_inst_727_, 0);
lean_inc(v_map_728_);
lean_dec_ref(v_inst_727_);
v___f_729_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_730_ = lean_apply_4(v_map_728_, lean_box(0), lean_box(0), v___f_729_, v_inst_726_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object* v_m_731_, lean_object* v_inst_732_, lean_object* v_inst_733_){
_start:
{
lean_object* v_map_734_; lean_object* v___f_735_; lean_object* v___x_736_; 
v_map_734_ = lean_ctor_get(v_inst_733_, 0);
lean_inc(v_map_734_);
lean_dec_ref(v_inst_733_);
v___f_735_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_736_ = lean_apply_4(v_map_734_, lean_box(0), lean_box(0), v___f_735_, v_inst_732_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___redArg(lean_object* v_inst_738_, lean_object* v_inst_739_){
_start:
{
lean_object* v_map_740_; lean_object* v___f_741_; lean_object* v___x_742_; 
v_map_740_ = lean_ctor_get(v_inst_739_, 0);
lean_inc(v_map_740_);
lean_dec_ref(v_inst_739_);
v___f_741_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_742_ = lean_apply_4(v_map_740_, lean_box(0), lean_box(0), v___f_741_, v_inst_738_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object* v_m_743_, lean_object* v_inst_744_, lean_object* v_inst_745_){
_start:
{
lean_object* v_map_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
v_map_746_ = lean_ctor_get(v_inst_745_, 0);
lean_inc(v_map_746_);
lean_dec_ref(v_inst_745_);
v___f_747_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_748_ = lean_apply_4(v_map_746_, lean_box(0), lean_box(0), v___f_747_, v_inst_744_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0(lean_object* v_x_749_){
_start:
{
lean_object* v_elan_x3f_750_; 
v_elan_x3f_750_ = lean_ctor_get(v_x_749_, 2);
lean_inc(v_elan_x3f_750_);
return v_elan_x3f_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0___boxed(lean_object* v_x_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lake_getElanInstall_x3f___redArg___lam__0(v_x_751_);
lean_dec_ref(v_x_751_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg(lean_object* v_inst_754_, lean_object* v_inst_755_){
_start:
{
lean_object* v_map_756_; lean_object* v___f_757_; lean_object* v___x_758_; 
v_map_756_ = lean_ctor_get(v_inst_755_, 0);
lean_inc(v_map_756_);
lean_dec_ref(v_inst_755_);
v___f_757_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_758_ = lean_apply_4(v_map_756_, lean_box(0), lean_box(0), v___f_757_, v_inst_754_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object* v_m_759_, lean_object* v_inst_760_, lean_object* v_inst_761_){
_start:
{
lean_object* v_map_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
v_map_762_ = lean_ctor_get(v_inst_761_, 0);
lean_inc(v_map_762_);
lean_dec_ref(v_inst_761_);
v___f_763_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_764_ = lean_apply_4(v_map_762_, lean_box(0), lean_box(0), v___f_763_, v_inst_760_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg___lam__0(lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_775_; 
v_val_767_ = lean_ctor_get(v_x_765_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_775_ == 0)
{
v___x_769_ = v_x_765_;
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_dec(v_x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_775_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_home_771_; lean_object* v___x_773_; 
v_home_771_ = lean_ctor_get(v_val_767_, 0);
lean_inc_ref(v_home_771_);
lean_dec(v_val_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_home_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_home_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg(lean_object* v_inst_777_, lean_object* v_inst_778_){
_start:
{
lean_object* v_map_779_; lean_object* v___f_780_; lean_object* v___f_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_map_779_ = lean_ctor_get(v_inst_778_, 0);
lean_inc_n(v_map_779_, 2);
lean_dec_ref(v_inst_778_);
v___f_780_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_781_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_782_ = lean_apply_4(v_map_779_, lean_box(0), lean_box(0), v___f_781_, v_inst_777_);
v___x_783_ = lean_apply_4(v_map_779_, lean_box(0), lean_box(0), v___f_780_, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object* v_m_784_, lean_object* v_inst_785_, lean_object* v_inst_786_){
_start:
{
lean_object* v_map_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_map_787_ = lean_ctor_get(v_inst_786_, 0);
lean_inc_n(v_map_787_, 2);
lean_dec_ref(v_inst_786_);
v___f_788_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_789_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_790_ = lean_apply_4(v_map_787_, lean_box(0), lean_box(0), v___f_789_, v_inst_785_);
v___x_791_ = lean_apply_4(v_map_787_, lean_box(0), lean_box(0), v___f_788_, v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg___lam__0(lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v___x_793_; 
v___x_793_ = lean_box(0);
return v___x_793_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_val_794_ = lean_ctor_get(v_x_792_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_802_ == 0)
{
v___x_796_ = v_x_792_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v_x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_elan_798_; lean_object* v___x_800_; 
v_elan_798_ = lean_ctor_get(v_val_794_, 1);
lean_inc_ref(v_elan_798_);
lean_dec(v_val_794_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v_elan_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_elan_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg(lean_object* v_inst_804_, lean_object* v_inst_805_){
_start:
{
lean_object* v_map_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_map_806_ = lean_ctor_get(v_inst_805_, 0);
lean_inc_n(v_map_806_, 2);
lean_dec_ref(v_inst_805_);
v___f_807_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_808_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_809_ = lean_apply_4(v_map_806_, lean_box(0), lean_box(0), v___f_808_, v_inst_804_);
v___x_810_ = lean_apply_4(v_map_806_, lean_box(0), lean_box(0), v___f_807_, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object* v_m_811_, lean_object* v_inst_812_, lean_object* v_inst_813_){
_start:
{
lean_object* v_map_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_map_814_ = lean_ctor_get(v_inst_813_, 0);
lean_inc_n(v_map_814_, 2);
lean_dec_ref(v_inst_813_);
v___f_815_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_816_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_817_ = lean_apply_4(v_map_814_, lean_box(0), lean_box(0), v___f_816_, v_inst_812_);
v___x_818_ = lean_apply_4(v_map_814_, lean_box(0), lean_box(0), v___f_815_, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0(lean_object* v_x_819_){
_start:
{
lean_object* v_lean_820_; 
v_lean_820_ = lean_ctor_get(v_x_819_, 1);
lean_inc_ref(v_lean_820_);
return v_lean_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0___boxed(lean_object* v_x_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lake_getLeanInstall___redArg___lam__0(v_x_821_);
lean_dec_ref(v_x_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg(lean_object* v_inst_824_, lean_object* v_inst_825_){
_start:
{
lean_object* v_map_826_; lean_object* v___f_827_; lean_object* v___x_828_; 
v_map_826_ = lean_ctor_get(v_inst_825_, 0);
lean_inc(v_map_826_);
lean_dec_ref(v_inst_825_);
v___f_827_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_828_ = lean_apply_4(v_map_826_, lean_box(0), lean_box(0), v___f_827_, v_inst_824_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object* v_m_829_, lean_object* v_inst_830_, lean_object* v_inst_831_){
_start:
{
lean_object* v_map_832_; lean_object* v___f_833_; lean_object* v___x_834_; 
v_map_832_ = lean_ctor_get(v_inst_831_, 0);
lean_inc(v_map_832_);
lean_dec_ref(v_inst_831_);
v___f_833_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_834_ = lean_apply_4(v_map_832_, lean_box(0), lean_box(0), v___f_833_, v_inst_830_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0(lean_object* v_x_835_){
_start:
{
lean_object* v_sysroot_836_; 
v_sysroot_836_ = lean_ctor_get(v_x_835_, 0);
lean_inc_ref(v_sysroot_836_);
return v_sysroot_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0___boxed(lean_object* v_x_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lake_getLeanSysroot___redArg___lam__0(v_x_837_);
lean_dec_ref(v_x_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg(lean_object* v_inst_840_, lean_object* v_inst_841_){
_start:
{
lean_object* v_map_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_map_842_ = lean_ctor_get(v_inst_841_, 0);
lean_inc_n(v_map_842_, 2);
lean_dec_ref(v_inst_841_);
v___f_843_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_844_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_845_ = lean_apply_4(v_map_842_, lean_box(0), lean_box(0), v___f_844_, v_inst_840_);
v___x_846_ = lean_apply_4(v_map_842_, lean_box(0), lean_box(0), v___f_843_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object* v_m_847_, lean_object* v_inst_848_, lean_object* v_inst_849_){
_start:
{
lean_object* v_map_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_map_850_ = lean_ctor_get(v_inst_849_, 0);
lean_inc_n(v_map_850_, 2);
lean_dec_ref(v_inst_849_);
v___f_851_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_852_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_853_ = lean_apply_4(v_map_850_, lean_box(0), lean_box(0), v___f_852_, v_inst_848_);
v___x_854_ = lean_apply_4(v_map_850_, lean_box(0), lean_box(0), v___f_851_, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0(lean_object* v_x_855_){
_start:
{
lean_object* v_srcDir_856_; 
v_srcDir_856_ = lean_ctor_get(v_x_855_, 2);
lean_inc_ref(v_srcDir_856_);
return v_srcDir_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0___boxed(lean_object* v_x_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lake_getLeanSrcDir___redArg___lam__0(v_x_857_);
lean_dec_ref(v_x_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg(lean_object* v_inst_860_, lean_object* v_inst_861_){
_start:
{
lean_object* v_map_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_map_862_ = lean_ctor_get(v_inst_861_, 0);
lean_inc_n(v_map_862_, 2);
lean_dec_ref(v_inst_861_);
v___f_863_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_864_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_865_ = lean_apply_4(v_map_862_, lean_box(0), lean_box(0), v___f_864_, v_inst_860_);
v___x_866_ = lean_apply_4(v_map_862_, lean_box(0), lean_box(0), v___f_863_, v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object* v_m_867_, lean_object* v_inst_868_, lean_object* v_inst_869_){
_start:
{
lean_object* v_map_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_map_870_ = lean_ctor_get(v_inst_869_, 0);
lean_inc_n(v_map_870_, 2);
lean_dec_ref(v_inst_869_);
v___f_871_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_872_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_873_ = lean_apply_4(v_map_870_, lean_box(0), lean_box(0), v___f_872_, v_inst_868_);
v___x_874_ = lean_apply_4(v_map_870_, lean_box(0), lean_box(0), v___f_871_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0(lean_object* v_x_875_){
_start:
{
lean_object* v_leanLibDir_876_; 
v_leanLibDir_876_ = lean_ctor_get(v_x_875_, 3);
lean_inc_ref(v_leanLibDir_876_);
return v_leanLibDir_876_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0___boxed(lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lake_getLeanLibDir___redArg___lam__0(v_x_877_);
lean_dec_ref(v_x_877_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg(lean_object* v_inst_880_, lean_object* v_inst_881_){
_start:
{
lean_object* v_map_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_map_882_ = lean_ctor_get(v_inst_881_, 0);
lean_inc_n(v_map_882_, 2);
lean_dec_ref(v_inst_881_);
v___f_883_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_884_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_885_ = lean_apply_4(v_map_882_, lean_box(0), lean_box(0), v___f_884_, v_inst_880_);
v___x_886_ = lean_apply_4(v_map_882_, lean_box(0), lean_box(0), v___f_883_, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object* v_m_887_, lean_object* v_inst_888_, lean_object* v_inst_889_){
_start:
{
lean_object* v_map_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_map_890_ = lean_ctor_get(v_inst_889_, 0);
lean_inc_n(v_map_890_, 2);
lean_dec_ref(v_inst_889_);
v___f_891_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_892_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_893_ = lean_apply_4(v_map_890_, lean_box(0), lean_box(0), v___f_892_, v_inst_888_);
v___x_894_ = lean_apply_4(v_map_890_, lean_box(0), lean_box(0), v___f_891_, v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0(lean_object* v_x_895_){
_start:
{
lean_object* v_includeDir_896_; 
v_includeDir_896_ = lean_ctor_get(v_x_895_, 4);
lean_inc_ref(v_includeDir_896_);
return v_includeDir_896_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0___boxed(lean_object* v_x_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lake_getLeanIncludeDir___redArg___lam__0(v_x_897_);
lean_dec_ref(v_x_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg(lean_object* v_inst_900_, lean_object* v_inst_901_){
_start:
{
lean_object* v_map_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_map_902_ = lean_ctor_get(v_inst_901_, 0);
lean_inc_n(v_map_902_, 2);
lean_dec_ref(v_inst_901_);
v___f_903_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_904_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_905_ = lean_apply_4(v_map_902_, lean_box(0), lean_box(0), v___f_904_, v_inst_900_);
v___x_906_ = lean_apply_4(v_map_902_, lean_box(0), lean_box(0), v___f_903_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object* v_m_907_, lean_object* v_inst_908_, lean_object* v_inst_909_){
_start:
{
lean_object* v_map_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_map_910_ = lean_ctor_get(v_inst_909_, 0);
lean_inc_n(v_map_910_, 2);
lean_dec_ref(v_inst_909_);
v___f_911_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_912_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_913_ = lean_apply_4(v_map_910_, lean_box(0), lean_box(0), v___f_912_, v_inst_908_);
v___x_914_ = lean_apply_4(v_map_910_, lean_box(0), lean_box(0), v___f_911_, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0(lean_object* v_x_915_){
_start:
{
lean_object* v_systemLibDir_916_; 
v_systemLibDir_916_ = lean_ctor_get(v_x_915_, 5);
lean_inc_ref(v_systemLibDir_916_);
return v_systemLibDir_916_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed(lean_object* v_x_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lake_getLeanSystemLibDir___redArg___lam__0(v_x_917_);
lean_dec_ref(v_x_917_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg(lean_object* v_inst_920_, lean_object* v_inst_921_){
_start:
{
lean_object* v_map_922_; lean_object* v___f_923_; lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_map_922_ = lean_ctor_get(v_inst_921_, 0);
lean_inc_n(v_map_922_, 2);
lean_dec_ref(v_inst_921_);
v___f_923_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_924_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_925_ = lean_apply_4(v_map_922_, lean_box(0), lean_box(0), v___f_924_, v_inst_920_);
v___x_926_ = lean_apply_4(v_map_922_, lean_box(0), lean_box(0), v___f_923_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object* v_m_927_, lean_object* v_inst_928_, lean_object* v_inst_929_){
_start:
{
lean_object* v_map_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_map_930_ = lean_ctor_get(v_inst_929_, 0);
lean_inc_n(v_map_930_, 2);
lean_dec_ref(v_inst_929_);
v___f_931_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_932_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_933_ = lean_apply_4(v_map_930_, lean_box(0), lean_box(0), v___f_932_, v_inst_928_);
v___x_934_ = lean_apply_4(v_map_930_, lean_box(0), lean_box(0), v___f_931_, v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0(lean_object* v_x_935_){
_start:
{
lean_object* v_lean_936_; 
v_lean_936_ = lean_ctor_get(v_x_935_, 7);
lean_inc_ref(v_lean_936_);
return v_lean_936_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0___boxed(lean_object* v_x_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lake_getLean___redArg___lam__0(v_x_937_);
lean_dec_ref(v_x_937_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg(lean_object* v_inst_940_, lean_object* v_inst_941_){
_start:
{
lean_object* v_map_942_; lean_object* v___f_943_; lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_map_942_ = lean_ctor_get(v_inst_941_, 0);
lean_inc_n(v_map_942_, 2);
lean_dec_ref(v_inst_941_);
v___f_943_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_944_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_945_ = lean_apply_4(v_map_942_, lean_box(0), lean_box(0), v___f_944_, v_inst_940_);
v___x_946_ = lean_apply_4(v_map_942_, lean_box(0), lean_box(0), v___f_943_, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object* v_m_947_, lean_object* v_inst_948_, lean_object* v_inst_949_){
_start:
{
lean_object* v_map_950_; lean_object* v___f_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_map_950_ = lean_ctor_get(v_inst_949_, 0);
lean_inc_n(v_map_950_, 2);
lean_dec_ref(v_inst_949_);
v___f_951_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_952_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_953_ = lean_apply_4(v_map_950_, lean_box(0), lean_box(0), v___f_952_, v_inst_948_);
v___x_954_ = lean_apply_4(v_map_950_, lean_box(0), lean_box(0), v___f_951_, v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0(lean_object* v_x_955_){
_start:
{
lean_object* v_leanir_956_; 
v_leanir_956_ = lean_ctor_get(v_x_955_, 8);
lean_inc_ref(v_leanir_956_);
return v_leanir_956_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0___boxed(lean_object* v_x_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lake_getLeanir___redArg___lam__0(v_x_957_);
lean_dec_ref(v_x_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg(lean_object* v_inst_960_, lean_object* v_inst_961_){
_start:
{
lean_object* v_map_962_; lean_object* v___f_963_; lean_object* v___f_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_map_962_ = lean_ctor_get(v_inst_961_, 0);
lean_inc_n(v_map_962_, 2);
lean_dec_ref(v_inst_961_);
v___f_963_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_964_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_965_ = lean_apply_4(v_map_962_, lean_box(0), lean_box(0), v___f_964_, v_inst_960_);
v___x_966_ = lean_apply_4(v_map_962_, lean_box(0), lean_box(0), v___f_963_, v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir(lean_object* v_m_967_, lean_object* v_inst_968_, lean_object* v_inst_969_){
_start:
{
lean_object* v_map_970_; lean_object* v___f_971_; lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_map_970_ = lean_ctor_get(v_inst_969_, 0);
lean_inc_n(v_map_970_, 2);
lean_dec_ref(v_inst_969_);
v___f_971_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_972_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_973_ = lean_apply_4(v_map_970_, lean_box(0), lean_box(0), v___f_972_, v_inst_968_);
v___x_974_ = lean_apply_4(v_map_970_, lean_box(0), lean_box(0), v___f_971_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0(lean_object* v_x_975_){
_start:
{
lean_object* v_leanc_976_; 
v_leanc_976_ = lean_ctor_get(v_x_975_, 9);
lean_inc_ref(v_leanc_976_);
return v_leanc_976_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0___boxed(lean_object* v_x_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lake_getLeanc___redArg___lam__0(v_x_977_);
lean_dec_ref(v_x_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg(lean_object* v_inst_980_, lean_object* v_inst_981_){
_start:
{
lean_object* v_map_982_; lean_object* v___f_983_; lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_map_982_ = lean_ctor_get(v_inst_981_, 0);
lean_inc_n(v_map_982_, 2);
lean_dec_ref(v_inst_981_);
v___f_983_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_984_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_985_ = lean_apply_4(v_map_982_, lean_box(0), lean_box(0), v___f_984_, v_inst_980_);
v___x_986_ = lean_apply_4(v_map_982_, lean_box(0), lean_box(0), v___f_983_, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object* v_m_987_, lean_object* v_inst_988_, lean_object* v_inst_989_){
_start:
{
lean_object* v_map_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_map_990_ = lean_ctor_get(v_inst_989_, 0);
lean_inc_n(v_map_990_, 2);
lean_dec_ref(v_inst_989_);
v___f_991_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_992_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_993_ = lean_apply_4(v_map_990_, lean_box(0), lean_box(0), v___f_992_, v_inst_988_);
v___x_994_ = lean_apply_4(v_map_990_, lean_box(0), lean_box(0), v___f_991_, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0(lean_object* v_x_995_){
_start:
{
lean_object* v_leantar_996_; 
v_leantar_996_ = lean_ctor_get(v_x_995_, 10);
lean_inc_ref(v_leantar_996_);
return v_leantar_996_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0___boxed(lean_object* v_x_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lake_getLeantar___redArg___lam__0(v_x_997_);
lean_dec_ref(v_x_997_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg(lean_object* v_inst_1000_, lean_object* v_inst_1001_){
_start:
{
lean_object* v_map_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_map_1002_ = lean_ctor_get(v_inst_1001_, 0);
lean_inc_n(v_map_1002_, 2);
lean_dec_ref(v_inst_1001_);
v___f_1003_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1004_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1005_ = lean_apply_4(v_map_1002_, lean_box(0), lean_box(0), v___f_1004_, v_inst_1000_);
v___x_1006_ = lean_apply_4(v_map_1002_, lean_box(0), lean_box(0), v___f_1003_, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar(lean_object* v_m_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_){
_start:
{
lean_object* v_map_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_map_1010_ = lean_ctor_get(v_inst_1009_, 0);
lean_inc_n(v_map_1010_, 2);
lean_dec_ref(v_inst_1009_);
v___f_1011_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1012_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1013_ = lean_apply_4(v_map_1010_, lean_box(0), lean_box(0), v___f_1012_, v_inst_1008_);
v___x_1014_ = lean_apply_4(v_map_1010_, lean_box(0), lean_box(0), v___f_1011_, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0(lean_object* v_x_1015_){
_start:
{
lean_object* v_sharedLib_1016_; 
v_sharedLib_1016_ = lean_ctor_get(v_x_1015_, 11);
lean_inc_ref(v_sharedLib_1016_);
return v_sharedLib_1016_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0___boxed(lean_object* v_x_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lake_getLeanSharedLib___redArg___lam__0(v_x_1017_);
lean_dec_ref(v_x_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg(lean_object* v_inst_1020_, lean_object* v_inst_1021_){
_start:
{
lean_object* v_map_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_map_1022_ = lean_ctor_get(v_inst_1021_, 0);
lean_inc_n(v_map_1022_, 2);
lean_dec_ref(v_inst_1021_);
v___f_1023_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1024_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1025_ = lean_apply_4(v_map_1022_, lean_box(0), lean_box(0), v___f_1024_, v_inst_1020_);
v___x_1026_ = lean_apply_4(v_map_1022_, lean_box(0), lean_box(0), v___f_1023_, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object* v_m_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_){
_start:
{
lean_object* v_map_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_map_1030_ = lean_ctor_get(v_inst_1029_, 0);
lean_inc_n(v_map_1030_, 2);
lean_dec_ref(v_inst_1029_);
v___f_1031_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1032_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1033_ = lean_apply_4(v_map_1030_, lean_box(0), lean_box(0), v___f_1032_, v_inst_1028_);
v___x_1034_ = lean_apply_4(v_map_1030_, lean_box(0), lean_box(0), v___f_1031_, v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0(lean_object* v_x_1035_){
_start:
{
lean_object* v_ar_1036_; 
v_ar_1036_ = lean_ctor_get(v_x_1035_, 13);
lean_inc_ref(v_ar_1036_);
return v_ar_1036_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0___boxed(lean_object* v_x_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lake_getLeanAr___redArg___lam__0(v_x_1037_);
lean_dec_ref(v_x_1037_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg(lean_object* v_inst_1040_, lean_object* v_inst_1041_){
_start:
{
lean_object* v_map_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_map_1042_ = lean_ctor_get(v_inst_1041_, 0);
lean_inc_n(v_map_1042_, 2);
lean_dec_ref(v_inst_1041_);
v___f_1043_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1044_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1045_ = lean_apply_4(v_map_1042_, lean_box(0), lean_box(0), v___f_1044_, v_inst_1040_);
v___x_1046_ = lean_apply_4(v_map_1042_, lean_box(0), lean_box(0), v___f_1043_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object* v_m_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_){
_start:
{
lean_object* v_map_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_map_1050_ = lean_ctor_get(v_inst_1049_, 0);
lean_inc_n(v_map_1050_, 2);
lean_dec_ref(v_inst_1049_);
v___f_1051_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1052_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1053_ = lean_apply_4(v_map_1050_, lean_box(0), lean_box(0), v___f_1052_, v_inst_1048_);
v___x_1054_ = lean_apply_4(v_map_1050_, lean_box(0), lean_box(0), v___f_1051_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0(lean_object* v_x_1055_){
_start:
{
lean_object* v_cc_1056_; 
v_cc_1056_ = lean_ctor_get(v_x_1055_, 14);
lean_inc_ref(v_cc_1056_);
return v_cc_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0___boxed(lean_object* v_x_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lake_getLeanCc___redArg___lam__0(v_x_1057_);
lean_dec_ref(v_x_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg(lean_object* v_inst_1060_, lean_object* v_inst_1061_){
_start:
{
lean_object* v_map_1062_; lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_map_1062_ = lean_ctor_get(v_inst_1061_, 0);
lean_inc_n(v_map_1062_, 2);
lean_dec_ref(v_inst_1061_);
v___f_1063_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1064_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1065_ = lean_apply_4(v_map_1062_, lean_box(0), lean_box(0), v___f_1064_, v_inst_1060_);
v___x_1066_ = lean_apply_4(v_map_1062_, lean_box(0), lean_box(0), v___f_1063_, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object* v_m_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_){
_start:
{
lean_object* v_map_1070_; lean_object* v___f_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_map_1070_ = lean_ctor_get(v_inst_1069_, 0);
lean_inc_n(v_map_1070_, 2);
lean_dec_ref(v_inst_1069_);
v___f_1071_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1072_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1073_ = lean_apply_4(v_map_1070_, lean_box(0), lean_box(0), v___f_1072_, v_inst_1068_);
v___x_1074_ = lean_apply_4(v_map_1070_, lean_box(0), lean_box(0), v___f_1071_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___redArg(lean_object* v_inst_1076_, lean_object* v_inst_1077_){
_start:
{
lean_object* v_map_1078_; lean_object* v___f_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_map_1078_ = lean_ctor_get(v_inst_1077_, 0);
lean_inc_n(v_map_1078_, 2);
lean_dec_ref(v_inst_1077_);
v___f_1079_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1080_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1081_ = lean_apply_4(v_map_1078_, lean_box(0), lean_box(0), v___f_1080_, v_inst_1076_);
v___x_1082_ = lean_apply_4(v_map_1078_, lean_box(0), lean_box(0), v___f_1079_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object* v_m_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_){
_start:
{
lean_object* v_map_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_map_1086_ = lean_ctor_get(v_inst_1085_, 0);
lean_inc_n(v_map_1086_, 2);
lean_dec_ref(v_inst_1085_);
v___f_1087_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1088_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1089_ = lean_apply_4(v_map_1086_, lean_box(0), lean_box(0), v___f_1088_, v_inst_1084_);
v___x_1090_ = lean_apply_4(v_map_1086_, lean_box(0), lean_box(0), v___f_1087_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0(lean_object* v_x_1091_){
_start:
{
lean_object* v_ccLinkSharedFlags_1092_; 
v_ccLinkSharedFlags_1092_ = lean_ctor_get(v_x_1091_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1092_);
return v_ccLinkSharedFlags_1092_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed(lean_object* v_x_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lake_getLeanLinkSharedFlags___redArg___lam__0(v_x_1093_);
lean_dec_ref(v_x_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg(lean_object* v_inst_1096_, lean_object* v_inst_1097_){
_start:
{
lean_object* v_map_1098_; lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_map_1098_ = lean_ctor_get(v_inst_1097_, 0);
lean_inc_n(v_map_1098_, 2);
lean_dec_ref(v_inst_1097_);
v___f_1099_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1100_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1101_ = lean_apply_4(v_map_1098_, lean_box(0), lean_box(0), v___f_1100_, v_inst_1096_);
v___x_1102_ = lean_apply_4(v_map_1098_, lean_box(0), lean_box(0), v___f_1099_, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags(lean_object* v_m_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_){
_start:
{
lean_object* v_map_1106_; lean_object* v___f_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_map_1106_ = lean_ctor_get(v_inst_1105_, 0);
lean_inc_n(v_map_1106_, 2);
lean_dec_ref(v_inst_1105_);
v___f_1107_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1108_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1109_ = lean_apply_4(v_map_1106_, lean_box(0), lean_box(0), v___f_1108_, v_inst_1104_);
v___x_1110_ = lean_apply_4(v_map_1106_, lean_box(0), lean_box(0), v___f_1107_, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0(lean_object* v_x_1111_){
_start:
{
lean_object* v_lake_1112_; 
v_lake_1112_ = lean_ctor_get(v_x_1111_, 0);
lean_inc_ref(v_lake_1112_);
return v_lake_1112_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0___boxed(lean_object* v_x_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lake_getLakeInstall___redArg___lam__0(v_x_1113_);
lean_dec_ref(v_x_1113_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg(lean_object* v_inst_1116_, lean_object* v_inst_1117_){
_start:
{
lean_object* v_map_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; 
v_map_1118_ = lean_ctor_get(v_inst_1117_, 0);
lean_inc(v_map_1118_);
lean_dec_ref(v_inst_1117_);
v___f_1119_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1120_ = lean_apply_4(v_map_1118_, lean_box(0), lean_box(0), v___f_1119_, v_inst_1116_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object* v_m_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_){
_start:
{
lean_object* v_map_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; 
v_map_1124_ = lean_ctor_get(v_inst_1123_, 0);
lean_inc(v_map_1124_);
lean_dec_ref(v_inst_1123_);
v___f_1125_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1126_ = lean_apply_4(v_map_1124_, lean_box(0), lean_box(0), v___f_1125_, v_inst_1122_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0(lean_object* v_x_1127_){
_start:
{
lean_object* v_home_1128_; 
v_home_1128_ = lean_ctor_get(v_x_1127_, 0);
lean_inc_ref(v_home_1128_);
return v_home_1128_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0___boxed(lean_object* v_x_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lake_getLakeHome___redArg___lam__0(v_x_1129_);
lean_dec_ref(v_x_1129_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg(lean_object* v_inst_1132_, lean_object* v_inst_1133_){
_start:
{
lean_object* v_map_1134_; lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_map_1134_ = lean_ctor_get(v_inst_1133_, 0);
lean_inc_n(v_map_1134_, 2);
lean_dec_ref(v_inst_1133_);
v___f_1135_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1136_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1137_ = lean_apply_4(v_map_1134_, lean_box(0), lean_box(0), v___f_1136_, v_inst_1132_);
v___x_1138_ = lean_apply_4(v_map_1134_, lean_box(0), lean_box(0), v___f_1135_, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object* v_m_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_){
_start:
{
lean_object* v_map_1142_; lean_object* v___f_1143_; lean_object* v___f_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_map_1142_ = lean_ctor_get(v_inst_1141_, 0);
lean_inc_n(v_map_1142_, 2);
lean_dec_ref(v_inst_1141_);
v___f_1143_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1144_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1145_ = lean_apply_4(v_map_1142_, lean_box(0), lean_box(0), v___f_1144_, v_inst_1140_);
v___x_1146_ = lean_apply_4(v_map_1142_, lean_box(0), lean_box(0), v___f_1143_, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0(lean_object* v_x_1147_){
_start:
{
lean_object* v_srcDir_1148_; 
v_srcDir_1148_ = lean_ctor_get(v_x_1147_, 1);
lean_inc_ref(v_srcDir_1148_);
return v_srcDir_1148_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0___boxed(lean_object* v_x_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lake_getLakeSrcDir___redArg___lam__0(v_x_1149_);
lean_dec_ref(v_x_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg(lean_object* v_inst_1152_, lean_object* v_inst_1153_){
_start:
{
lean_object* v_map_1154_; lean_object* v___f_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_map_1154_ = lean_ctor_get(v_inst_1153_, 0);
lean_inc_n(v_map_1154_, 2);
lean_dec_ref(v_inst_1153_);
v___f_1155_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1156_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1157_ = lean_apply_4(v_map_1154_, lean_box(0), lean_box(0), v___f_1156_, v_inst_1152_);
v___x_1158_ = lean_apply_4(v_map_1154_, lean_box(0), lean_box(0), v___f_1155_, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object* v_m_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v_map_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_map_1162_ = lean_ctor_get(v_inst_1161_, 0);
lean_inc_n(v_map_1162_, 2);
lean_dec_ref(v_inst_1161_);
v___f_1163_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1164_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1165_ = lean_apply_4(v_map_1162_, lean_box(0), lean_box(0), v___f_1164_, v_inst_1160_);
v___x_1166_ = lean_apply_4(v_map_1162_, lean_box(0), lean_box(0), v___f_1163_, v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0(lean_object* v_x_1167_){
_start:
{
lean_object* v_libDir_1168_; 
v_libDir_1168_ = lean_ctor_get(v_x_1167_, 3);
lean_inc_ref(v_libDir_1168_);
return v_libDir_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0___boxed(lean_object* v_x_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lake_getLakeLibDir___redArg___lam__0(v_x_1169_);
lean_dec_ref(v_x_1169_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg(lean_object* v_inst_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v_map_1174_; lean_object* v___f_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_map_1174_ = lean_ctor_get(v_inst_1173_, 0);
lean_inc_n(v_map_1174_, 2);
lean_dec_ref(v_inst_1173_);
v___f_1175_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1176_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1177_ = lean_apply_4(v_map_1174_, lean_box(0), lean_box(0), v___f_1176_, v_inst_1172_);
v___x_1178_ = lean_apply_4(v_map_1174_, lean_box(0), lean_box(0), v___f_1175_, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object* v_m_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v_map_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_map_1182_ = lean_ctor_get(v_inst_1181_, 0);
lean_inc_n(v_map_1182_, 2);
lean_dec_ref(v_inst_1181_);
v___f_1183_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1184_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1185_ = lean_apply_4(v_map_1182_, lean_box(0), lean_box(0), v___f_1184_, v_inst_1180_);
v___x_1186_ = lean_apply_4(v_map_1182_, lean_box(0), lean_box(0), v___f_1183_, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0(lean_object* v_x_1187_){
_start:
{
lean_object* v_lake_1188_; 
v_lake_1188_ = lean_ctor_get(v_x_1187_, 5);
lean_inc_ref(v_lake_1188_);
return v_lake_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0___boxed(lean_object* v_x_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lake_getLake___redArg___lam__0(v_x_1189_);
lean_dec_ref(v_x_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg(lean_object* v_inst_1192_, lean_object* v_inst_1193_){
_start:
{
lean_object* v_map_1194_; lean_object* v___f_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_map_1194_ = lean_ctor_get(v_inst_1193_, 0);
lean_inc_n(v_map_1194_, 2);
lean_dec_ref(v_inst_1193_);
v___f_1195_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1196_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1197_ = lean_apply_4(v_map_1194_, lean_box(0), lean_box(0), v___f_1196_, v_inst_1192_);
v___x_1198_ = lean_apply_4(v_map_1194_, lean_box(0), lean_box(0), v___f_1195_, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object* v_m_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_){
_start:
{
lean_object* v_map_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_map_1202_ = lean_ctor_get(v_inst_1201_, 0);
lean_inc_n(v_map_1202_, 2);
lean_dec_ref(v_inst_1201_);
v___f_1203_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1204_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1205_ = lean_apply_4(v_map_1202_, lean_box(0), lean_box(0), v___f_1204_, v_inst_1200_);
v___x_1206_ = lean_apply_4(v_map_1202_, lean_box(0), lean_box(0), v___f_1203_, v___x_1205_);
return v___x_1206_;
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

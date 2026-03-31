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
v_lakeEnv_68_ = lean_ctor_get(v_x_67_, 1);
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
lean_object* v_root_82_; 
v_root_82_ = lean_ctor_get(v_x_81_, 0);
lean_inc_ref(v_root_82_);
return v_root_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg___lam__0___boxed(lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lake_getRootPackage___redArg___lam__0(v_x_83_);
lean_dec_ref(v_x_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___redArg(lean_object* v_inst_86_, lean_object* v_inst_87_){
_start:
{
lean_object* v_map_88_; lean_object* v___f_89_; lean_object* v___x_90_; 
v_map_88_ = lean_ctor_get(v_inst_87_, 0);
lean_inc(v_map_88_);
lean_dec_ref(v_inst_87_);
v___f_89_ = ((lean_object*)(l_Lake_getRootPackage___redArg___closed__0));
v___x_90_ = lean_apply_4(v_map_88_, lean_box(0), lean_box(0), v___f_89_, v_inst_86_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage(lean_object* v_m_91_, lean_object* v_inst_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v_map_94_; lean_object* v___f_95_; lean_object* v___x_96_; 
v_map_94_ = lean_ctor_get(v_inst_93_, 0);
lean_inc(v_map_94_);
lean_dec_ref(v_inst_93_);
v___f_95_ = ((lean_object*)(l_Lake_getRootPackage___redArg___closed__0));
v___x_96_ = lean_apply_4(v_map_94_, lean_box(0), lean_box(0), v___f_95_, v_inst_92_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f___redArg___lam__0(lean_object* v_keyName_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_packageMap_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_packageMap_100_ = lean_ctor_get(v_x_99_, 6);
lean_inc(v_packageMap_100_);
lean_dec_ref(v_x_99_);
v___x_101_ = ((lean_object*)(l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0));
v___x_102_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_101_, v_packageMap_100_, v_keyName_98_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f___redArg(lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_keyName_105_){
_start:
{
lean_object* v_map_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v_map_106_ = lean_ctor_get(v_inst_104_, 0);
lean_inc(v_map_106_);
lean_dec_ref(v_inst_104_);
v___f_107_ = lean_alloc_closure((void*)(l_Lake_findPackageByKey_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_107_, 0, v_keyName_105_);
v___x_108_ = lean_apply_4(v_map_106_, lean_box(0), lean_box(0), v___f_107_, v_inst_103_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByKey_x3f(lean_object* v_m_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_keyName_112_){
_start:
{
lean_object* v_map_113_; lean_object* v___f_114_; lean_object* v___x_115_; 
v_map_113_ = lean_ctor_get(v_inst_111_, 0);
lean_inc(v_map_113_);
lean_dec_ref(v_inst_111_);
v___f_114_ = lean_alloc_closure((void*)(l_Lake_findPackageByKey_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_114_, 0, v_keyName_112_);
v___x_115_ = lean_apply_4(v_map_113_, lean_box(0), lean_box(0), v___f_114_, v_inst_110_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__0(lean_object* v_name_116_, lean_object* v___x_117_, lean_object* v___x_118_, lean_object* v_a_119_, lean_object* v_x_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_baseName_122_; uint8_t v___x_123_; 
v_baseName_122_ = lean_ctor_get(v_a_119_, 1);
v___x_123_ = lean_name_eq(v_baseName_122_, v_name_116_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref(v_a_119_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_117_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref(v___x_117_);
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v_a_119_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_118_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__0___boxed(lean_object* v_name_129_, lean_object* v___x_130_, lean_object* v___x_131_, lean_object* v_a_132_, lean_object* v_x_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lake_findPackageByName_x3f___redArg___lam__0(v_name_129_, v___x_130_, v___x_131_, v_a_132_, v_x_133_, v___y_134_);
lean_dec_ref(v___y_134_);
lean_dec(v_name_129_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg___lam__1(lean_object* v_name_158_, lean_object* v_x_159_){
_start:
{
lean_object* v_packages_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___f_165_; size_t v_sz_166_; size_t v___x_167_; lean_object* v___x_168_; lean_object* v_fst_169_; 
v_packages_160_ = lean_ctor_get(v_x_159_, 5);
lean_inc_ref(v_packages_160_);
lean_dec_ref(v_x_159_);
v___x_161_ = ((lean_object*)(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9));
v___x_162_ = lean_box(0);
v___x_163_ = lean_box(0);
v___x_164_ = ((lean_object*)(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10));
v___f_165_ = lean_alloc_closure((void*)(l_Lake_findPackageByName_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_165_, 0, v_name_158_);
lean_closure_set(v___f_165_, 1, v___x_164_);
lean_closure_set(v___f_165_, 2, v___x_163_);
v_sz_166_ = lean_array_size(v_packages_160_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_161_, v_packages_160_, v___f_165_, v_sz_166_, v___x_167_, v___x_164_);
v_fst_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_fst_169_);
lean_dec(v___x_168_);
if (lean_obj_tag(v_fst_169_) == 0)
{
return v___x_162_;
}
else
{
lean_object* v_val_170_; 
v_val_170_ = lean_ctor_get(v_fst_169_, 0);
lean_inc(v_val_170_);
lean_dec_ref(v_fst_169_);
return v_val_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_name_173_){
_start:
{
lean_object* v_map_174_; lean_object* v___f_175_; lean_object* v___x_176_; 
v_map_174_ = lean_ctor_get(v_inst_172_, 0);
lean_inc(v_map_174_);
lean_dec_ref(v_inst_172_);
v___f_175_ = lean_alloc_closure((void*)(l_Lake_findPackageByName_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_175_, 0, v_name_173_);
v___x_176_ = lean_apply_4(v_map_174_, lean_box(0), lean_box(0), v___f_175_, v_inst_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackageByName_x3f(lean_object* v_m_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_name_180_){
_start:
{
lean_object* v_map_181_; lean_object* v___f_182_; lean_object* v___x_183_; 
v_map_181_ = lean_ctor_get(v_inst_179_, 0);
lean_inc(v_map_181_);
lean_dec_ref(v_inst_179_);
v___f_182_ = lean_alloc_closure((void*)(l_Lake_findPackageByName_x3f___redArg___lam__1), 2, 1);
lean_closure_set(v___f_182_, 0, v_name_180_);
v___x_183_ = lean_apply_4(v_map_181_, lean_box(0), lean_box(0), v___f_182_, v_inst_178_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___redArg___lam__0(lean_object* v_name_184_, lean_object* v_x_185_){
_start:
{
lean_object* v_packageMap_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_packageMap_186_ = lean_ctor_get(v_x_185_, 6);
lean_inc(v_packageMap_186_);
lean_dec_ref(v_x_185_);
v___x_187_ = ((lean_object*)(l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0));
v___x_188_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v___x_187_, v_packageMap_186_, v_name_184_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___redArg(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_name_191_){
_start:
{
lean_object* v_map_192_; lean_object* v___f_193_; lean_object* v___x_194_; 
v_map_192_ = lean_ctor_get(v_inst_190_, 0);
lean_inc(v_map_192_);
lean_dec_ref(v_inst_190_);
v___f_193_ = lean_alloc_closure((void*)(l_Lake_findPackage_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_193_, 0, v_name_191_);
v___x_194_ = lean_apply_4(v_map_192_, lean_box(0), lean_box(0), v___f_193_, v_inst_189_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f(lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_name_198_){
_start:
{
lean_object* v_map_199_; lean_object* v___f_200_; lean_object* v___x_201_; 
v_map_199_ = lean_ctor_get(v_inst_197_, 0);
lean_inc(v_map_199_);
lean_dec_ref(v_inst_197_);
v___f_200_ = lean_alloc_closure((void*)(l_Lake_findPackage_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_200_, 0, v_name_198_);
v___x_201_ = lean_apply_4(v_map_199_, lean_box(0), lean_box(0), v___f_200_, v_inst_196_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg___lam__0(lean_object* v_name_202_, lean_object* v_x_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lake_Workspace_findModule_x3f(v_name_202_, v_x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg___lam__0___boxed(lean_object* v_name_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lake_findModule_x3f___redArg___lam__0(v_name_205_, v_x_206_);
lean_dec_ref(v_x_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___redArg(lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_name_210_){
_start:
{
lean_object* v_map_211_; lean_object* v___f_212_; lean_object* v___x_213_; 
v_map_211_ = lean_ctor_get(v_inst_209_, 0);
lean_inc(v_map_211_);
lean_dec_ref(v_inst_209_);
v___f_212_ = lean_alloc_closure((void*)(l_Lake_findModule_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_212_, 0, v_name_210_);
v___x_213_ = lean_apply_4(v_map_211_, lean_box(0), lean_box(0), v___f_212_, v_inst_208_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f(lean_object* v_m_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_name_217_){
_start:
{
lean_object* v_map_218_; lean_object* v___f_219_; lean_object* v___x_220_; 
v_map_218_ = lean_ctor_get(v_inst_216_, 0);
lean_inc(v_map_218_);
lean_dec_ref(v_inst_216_);
v___f_219_ = lean_alloc_closure((void*)(l_Lake_findModule_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_219_, 0, v_name_217_);
v___x_220_ = lean_apply_4(v_map_218_, lean_box(0), lean_box(0), v___f_219_, v_inst_215_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules___redArg___lam__0(lean_object* v_name_221_, lean_object* v_x_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lake_Workspace_findModules(v_name_221_, v_x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules___redArg___lam__0___boxed(lean_object* v_name_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lake_findModules___redArg___lam__0(v_name_224_, v_x_225_);
lean_dec_ref(v_x_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules___redArg(lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_name_229_){
_start:
{
lean_object* v_map_230_; lean_object* v___f_231_; lean_object* v___x_232_; 
v_map_230_ = lean_ctor_get(v_inst_228_, 0);
lean_inc(v_map_230_);
lean_dec_ref(v_inst_228_);
v___f_231_ = lean_alloc_closure((void*)(l_Lake_findModules___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_231_, 0, v_name_229_);
v___x_232_ = lean_apply_4(v_map_230_, lean_box(0), lean_box(0), v___f_231_, v_inst_227_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModules(lean_object* v_m_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_name_236_){
_start:
{
lean_object* v_map_237_; lean_object* v___f_238_; lean_object* v___x_239_; 
v_map_237_ = lean_ctor_get(v_inst_235_, 0);
lean_inc(v_map_237_);
lean_dec_ref(v_inst_235_);
v___f_238_ = lean_alloc_closure((void*)(l_Lake_findModules___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_238_, 0, v_name_236_);
v___x_239_ = lean_apply_4(v_map_237_, lean_box(0), lean_box(0), v___f_238_, v_inst_234_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg___lam__0(lean_object* v_path_240_, lean_object* v_x_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_240_, v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed(lean_object* v_path_243_, lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_findModuleBySrc_x3f___redArg___lam__0(v_path_243_, v_x_244_);
lean_dec_ref(v_x_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f___redArg(lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_path_248_){
_start:
{
lean_object* v_map_249_; lean_object* v___f_250_; lean_object* v___x_251_; 
v_map_249_ = lean_ctor_get(v_inst_247_, 0);
lean_inc(v_map_249_);
lean_dec_ref(v_inst_247_);
v___f_250_ = lean_alloc_closure((void*)(l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_250_, 0, v_path_248_);
v___x_251_ = lean_apply_4(v_map_249_, lean_box(0), lean_box(0), v___f_250_, v_inst_246_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_findModuleBySrc_x3f(lean_object* v_m_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_path_255_){
_start:
{
lean_object* v_map_256_; lean_object* v___f_257_; lean_object* v___x_258_; 
v_map_256_ = lean_ctor_get(v_inst_254_, 0);
lean_inc(v_map_256_);
lean_dec_ref(v_inst_254_);
v___f_257_ = lean_alloc_closure((void*)(l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_257_, 0, v_path_255_);
v___x_258_ = lean_apply_4(v_map_256_, lean_box(0), lean_box(0), v___f_257_, v_inst_253_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg___lam__0(lean_object* v_name_259_, lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lake_Workspace_findLeanExe_x3f(v_name_259_, v_x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg___lam__0___boxed(lean_object* v_name_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lake_findLeanExe_x3f___redArg___lam__0(v_name_262_, v_x_263_);
lean_dec_ref(v_x_263_);
lean_dec(v_name_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___redArg(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_name_267_){
_start:
{
lean_object* v_map_268_; lean_object* v___f_269_; lean_object* v___x_270_; 
v_map_268_ = lean_ctor_get(v_inst_266_, 0);
lean_inc(v_map_268_);
lean_dec_ref(v_inst_266_);
v___f_269_ = lean_alloc_closure((void*)(l_Lake_findLeanExe_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_269_, 0, v_name_267_);
v___x_270_ = lean_apply_4(v_map_268_, lean_box(0), lean_box(0), v___f_269_, v_inst_265_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f(lean_object* v_m_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_name_274_){
_start:
{
lean_object* v_map_275_; lean_object* v___f_276_; lean_object* v___x_277_; 
v_map_275_ = lean_ctor_get(v_inst_273_, 0);
lean_inc(v_map_275_);
lean_dec_ref(v_inst_273_);
v___f_276_ = lean_alloc_closure((void*)(l_Lake_findLeanExe_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_276_, 0, v_name_274_);
v___x_277_ = lean_apply_4(v_map_275_, lean_box(0), lean_box(0), v___f_276_, v_inst_272_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg___lam__0(lean_object* v_name_278_, lean_object* v_x_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lake_Workspace_findLeanLib_x3f(v_name_278_, v_x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg___lam__0___boxed(lean_object* v_name_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lake_findLeanLib_x3f___redArg___lam__0(v_name_281_, v_x_282_);
lean_dec_ref(v_x_282_);
lean_dec(v_name_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___redArg(lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_name_286_){
_start:
{
lean_object* v_map_287_; lean_object* v___f_288_; lean_object* v___x_289_; 
v_map_287_ = lean_ctor_get(v_inst_285_, 0);
lean_inc(v_map_287_);
lean_dec_ref(v_inst_285_);
v___f_288_ = lean_alloc_closure((void*)(l_Lake_findLeanLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_288_, 0, v_name_286_);
v___x_289_ = lean_apply_4(v_map_287_, lean_box(0), lean_box(0), v___f_288_, v_inst_284_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f(lean_object* v_m_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_name_293_){
_start:
{
lean_object* v_map_294_; lean_object* v___f_295_; lean_object* v___x_296_; 
v_map_294_ = lean_ctor_get(v_inst_292_, 0);
lean_inc(v_map_294_);
lean_dec_ref(v_inst_292_);
v___f_295_ = lean_alloc_closure((void*)(l_Lake_findLeanLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_295_, 0, v_name_293_);
v___x_296_ = lean_apply_4(v_map_294_, lean_box(0), lean_box(0), v___f_295_, v_inst_291_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg___lam__0(lean_object* v_name_297_, lean_object* v_x_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lake_Workspace_findExternLib_x3f(v_name_297_, v_x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg___lam__0___boxed(lean_object* v_name_300_, lean_object* v_x_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lake_findExternLib_x3f___redArg___lam__0(v_name_300_, v_x_301_);
lean_dec_ref(v_x_301_);
lean_dec(v_name_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___redArg(lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_name_305_){
_start:
{
lean_object* v_map_306_; lean_object* v___f_307_; lean_object* v___x_308_; 
v_map_306_ = lean_ctor_get(v_inst_304_, 0);
lean_inc(v_map_306_);
lean_dec_ref(v_inst_304_);
v___f_307_ = lean_alloc_closure((void*)(l_Lake_findExternLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_307_, 0, v_name_305_);
v___x_308_ = lean_apply_4(v_map_306_, lean_box(0), lean_box(0), v___f_307_, v_inst_303_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f(lean_object* v_m_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_name_312_){
_start:
{
lean_object* v_map_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v_map_313_ = lean_ctor_get(v_inst_311_, 0);
lean_inc(v_map_313_);
lean_dec_ref(v_inst_311_);
v___f_314_ = lean_alloc_closure((void*)(l_Lake_findExternLib_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_314_, 0, v_name_312_);
v___x_315_ = lean_apply_4(v_map_313_, lean_box(0), lean_box(0), v___f_314_, v_inst_310_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg___lam__0(lean_object* v_x_316_){
_start:
{
lean_object* v_root_317_; lean_object* v_config_318_; lean_object* v_toLeanConfig_319_; lean_object* v_leanOptions_320_; lean_object* v_moreServerOptions_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_root_317_ = lean_ctor_get(v_x_316_, 0);
v_config_318_ = lean_ctor_get(v_root_317_, 6);
v_toLeanConfig_319_ = lean_ctor_get(v_config_318_, 1);
v_leanOptions_320_ = lean_ctor_get(v_toLeanConfig_319_, 0);
v_moreServerOptions_321_ = lean_ctor_get(v_toLeanConfig_319_, 4);
v___x_322_ = l_Lean_LeanOptions_ofArray(v_leanOptions_320_);
v___x_323_ = l_Lean_LeanOptions_appendArray(v___x_322_, v_moreServerOptions_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg___lam__0___boxed(lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lake_getServerOptions___redArg___lam__0(v_x_324_);
lean_dec_ref(v_x_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions___redArg(lean_object* v_inst_327_, lean_object* v_inst_328_){
_start:
{
lean_object* v_map_329_; lean_object* v___f_330_; lean_object* v___x_331_; 
v_map_329_ = lean_ctor_get(v_inst_328_, 0);
lean_inc(v_map_329_);
lean_dec_ref(v_inst_328_);
v___f_330_ = ((lean_object*)(l_Lake_getServerOptions___redArg___closed__0));
v___x_331_ = lean_apply_4(v_map_329_, lean_box(0), lean_box(0), v___f_330_, v_inst_327_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_getServerOptions(lean_object* v_m_332_, lean_object* v_inst_333_, lean_object* v_inst_334_){
_start:
{
lean_object* v_map_335_; lean_object* v___f_336_; lean_object* v___x_337_; 
v_map_335_ = lean_ctor_get(v_inst_334_, 0);
lean_inc(v_map_335_);
lean_dec_ref(v_inst_334_);
v___f_336_ = ((lean_object*)(l_Lake_getServerOptions___redArg___closed__0));
v___x_337_ = lean_apply_4(v_map_335_, lean_box(0), lean_box(0), v___f_336_, v_inst_333_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg___lam__0(lean_object* v_x_338_){
_start:
{
lean_object* v_root_339_; lean_object* v_config_340_; lean_object* v_toLeanConfig_341_; lean_object* v_leanOptions_342_; lean_object* v___x_343_; 
v_root_339_ = lean_ctor_get(v_x_338_, 0);
v_config_340_ = lean_ctor_get(v_root_339_, 6);
v_toLeanConfig_341_ = lean_ctor_get(v_config_340_, 1);
v_leanOptions_342_ = lean_ctor_get(v_toLeanConfig_341_, 0);
v___x_343_ = l_Lean_LeanOptions_ofArray(v_leanOptions_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg___lam__0___boxed(lean_object* v_x_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lake_getLeanOptions___redArg___lam__0(v_x_344_);
lean_dec_ref(v_x_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions___redArg(lean_object* v_inst_347_, lean_object* v_inst_348_){
_start:
{
lean_object* v_map_349_; lean_object* v___f_350_; lean_object* v___x_351_; 
v_map_349_ = lean_ctor_get(v_inst_348_, 0);
lean_inc(v_map_349_);
lean_dec_ref(v_inst_348_);
v___f_350_ = ((lean_object*)(l_Lake_getLeanOptions___redArg___closed__0));
v___x_351_ = lean_apply_4(v_map_349_, lean_box(0), lean_box(0), v___f_350_, v_inst_347_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanOptions(lean_object* v_m_352_, lean_object* v_inst_353_, lean_object* v_inst_354_){
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
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg___lam__0(lean_object* v_x_358_){
_start:
{
lean_object* v_root_359_; lean_object* v_config_360_; lean_object* v_toLeanConfig_361_; lean_object* v_moreLeanArgs_362_; 
v_root_359_ = lean_ctor_get(v_x_358_, 0);
v_config_360_ = lean_ctor_get(v_root_359_, 6);
v_toLeanConfig_361_ = lean_ctor_get(v_config_360_, 1);
v_moreLeanArgs_362_ = lean_ctor_get(v_toLeanConfig_361_, 1);
lean_inc_ref(v_moreLeanArgs_362_);
return v_moreLeanArgs_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg___lam__0___boxed(lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lake_getLeanArgs___redArg___lam__0(v_x_363_);
lean_dec_ref(v_x_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanArgs___redArg(lean_object* v_inst_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v_map_368_; lean_object* v___f_369_; lean_object* v___x_370_; 
v_map_368_ = lean_ctor_get(v_inst_367_, 0);
lean_inc(v_map_368_);
lean_dec_ref(v_inst_367_);
v___f_369_ = ((lean_object*)(l_Lake_getLeanArgs___redArg___closed__0));
v___x_370_ = lean_apply_4(v_map_368_, lean_box(0), lean_box(0), v___f_369_, v_inst_366_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanArgs(lean_object* v_m_371_, lean_object* v_inst_372_, lean_object* v_inst_373_){
_start:
{
lean_object* v_map_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v_map_374_ = lean_ctor_get(v_inst_373_, 0);
lean_inc(v_map_374_);
lean_dec_ref(v_inst_373_);
v___f_375_ = ((lean_object*)(l_Lake_getLeanArgs___redArg___closed__0));
v___x_376_ = lean_apply_4(v_map_374_, lean_box(0), lean_box(0), v___f_375_, v_inst_372_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanPath___redArg(lean_object* v_inst_378_, lean_object* v_inst_379_){
_start:
{
lean_object* v_map_380_; lean_object* v___f_381_; lean_object* v___x_382_; 
v_map_380_ = lean_ctor_get(v_inst_379_, 0);
lean_inc(v_map_380_);
lean_dec_ref(v_inst_379_);
v___f_381_ = ((lean_object*)(l_Lake_getLeanPath___redArg___closed__0));
v___x_382_ = lean_apply_4(v_map_380_, lean_box(0), lean_box(0), v___f_381_, v_inst_378_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanPath(lean_object* v_m_383_, lean_object* v_inst_384_, lean_object* v_inst_385_){
_start:
{
lean_object* v_map_386_; lean_object* v___f_387_; lean_object* v___x_388_; 
v_map_386_ = lean_ctor_get(v_inst_385_, 0);
lean_inc(v_map_386_);
lean_dec_ref(v_inst_385_);
v___f_387_ = ((lean_object*)(l_Lake_getLeanPath___redArg___closed__0));
v___x_388_ = lean_apply_4(v_map_386_, lean_box(0), lean_box(0), v___f_387_, v_inst_384_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath___redArg(lean_object* v_inst_390_, lean_object* v_inst_391_){
_start:
{
lean_object* v_map_392_; lean_object* v___f_393_; lean_object* v___x_394_; 
v_map_392_ = lean_ctor_get(v_inst_391_, 0);
lean_inc(v_map_392_);
lean_dec_ref(v_inst_391_);
v___f_393_ = ((lean_object*)(l_Lake_getLeanSrcPath___redArg___closed__0));
v___x_394_ = lean_apply_4(v_map_392_, lean_box(0), lean_box(0), v___f_393_, v_inst_390_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath(lean_object* v_m_395_, lean_object* v_inst_396_, lean_object* v_inst_397_){
_start:
{
lean_object* v_map_398_; lean_object* v___f_399_; lean_object* v___x_400_; 
v_map_398_ = lean_ctor_get(v_inst_397_, 0);
lean_inc(v_map_398_);
lean_dec_ref(v_inst_397_);
v___f_399_ = ((lean_object*)(l_Lake_getLeanSrcPath___redArg___closed__0));
v___x_400_ = lean_apply_4(v_map_398_, lean_box(0), lean_box(0), v___f_399_, v_inst_396_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath___redArg(lean_object* v_inst_402_, lean_object* v_inst_403_){
_start:
{
lean_object* v_map_404_; lean_object* v___f_405_; lean_object* v___x_406_; 
v_map_404_ = lean_ctor_get(v_inst_403_, 0);
lean_inc(v_map_404_);
lean_dec_ref(v_inst_403_);
v___f_405_ = ((lean_object*)(l_Lake_getSharedLibPath___redArg___closed__0));
v___x_406_ = lean_apply_4(v_map_404_, lean_box(0), lean_box(0), v___f_405_, v_inst_402_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath(lean_object* v_m_407_, lean_object* v_inst_408_, lean_object* v_inst_409_){
_start:
{
lean_object* v_map_410_; lean_object* v___f_411_; lean_object* v___x_412_; 
v_map_410_ = lean_ctor_get(v_inst_409_, 0);
lean_inc(v_map_410_);
lean_dec_ref(v_inst_409_);
v___f_411_ = ((lean_object*)(l_Lake_getSharedLibPath___redArg___closed__0));
v___x_412_ = lean_apply_4(v_map_410_, lean_box(0), lean_box(0), v___f_411_, v_inst_408_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath___redArg(lean_object* v_inst_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v_map_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v_map_416_ = lean_ctor_get(v_inst_415_, 0);
lean_inc(v_map_416_);
lean_dec_ref(v_inst_415_);
v___f_417_ = ((lean_object*)(l_Lake_getAugmentedLeanPath___redArg___closed__0));
v___x_418_ = lean_apply_4(v_map_416_, lean_box(0), lean_box(0), v___f_417_, v_inst_414_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath(lean_object* v_m_419_, lean_object* v_inst_420_, lean_object* v_inst_421_){
_start:
{
lean_object* v_map_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
v_map_422_ = lean_ctor_get(v_inst_421_, 0);
lean_inc(v_map_422_);
lean_dec_ref(v_inst_421_);
v___f_423_ = ((lean_object*)(l_Lake_getAugmentedLeanPath___redArg___closed__0));
v___x_424_ = lean_apply_4(v_map_422_, lean_box(0), lean_box(0), v___f_423_, v_inst_420_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath___redArg(lean_object* v_inst_426_, lean_object* v_inst_427_){
_start:
{
lean_object* v_map_428_; lean_object* v___f_429_; lean_object* v___x_430_; 
v_map_428_ = lean_ctor_get(v_inst_427_, 0);
lean_inc(v_map_428_);
lean_dec_ref(v_inst_427_);
v___f_429_ = ((lean_object*)(l_Lake_getAugmentedLeanSrcPath___redArg___closed__0));
v___x_430_ = lean_apply_4(v_map_428_, lean_box(0), lean_box(0), v___f_429_, v_inst_426_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath(lean_object* v_m_431_, lean_object* v_inst_432_, lean_object* v_inst_433_){
_start:
{
lean_object* v_map_434_; lean_object* v___f_435_; lean_object* v___x_436_; 
v_map_434_ = lean_ctor_get(v_inst_433_, 0);
lean_inc(v_map_434_);
lean_dec_ref(v_inst_433_);
v___f_435_ = ((lean_object*)(l_Lake_getAugmentedLeanSrcPath___redArg___closed__0));
v___x_436_ = lean_apply_4(v_map_434_, lean_box(0), lean_box(0), v___f_435_, v_inst_432_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath___redArg(lean_object* v_inst_438_, lean_object* v_inst_439_){
_start:
{
lean_object* v_map_440_; lean_object* v___f_441_; lean_object* v___x_442_; 
v_map_440_ = lean_ctor_get(v_inst_439_, 0);
lean_inc(v_map_440_);
lean_dec_ref(v_inst_439_);
v___f_441_ = ((lean_object*)(l_Lake_getAugmentedSharedLibPath___redArg___closed__0));
v___x_442_ = lean_apply_4(v_map_440_, lean_box(0), lean_box(0), v___f_441_, v_inst_438_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath(lean_object* v_m_443_, lean_object* v_inst_444_, lean_object* v_inst_445_){
_start:
{
lean_object* v_map_446_; lean_object* v___f_447_; lean_object* v___x_448_; 
v_map_446_ = lean_ctor_get(v_inst_445_, 0);
lean_inc(v_map_446_);
lean_dec_ref(v_inst_445_);
v___f_447_ = ((lean_object*)(l_Lake_getAugmentedSharedLibPath___redArg___closed__0));
v___x_448_ = lean_apply_4(v_map_446_, lean_box(0), lean_box(0), v___f_447_, v_inst_444_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv___redArg(lean_object* v_inst_450_, lean_object* v_inst_451_){
_start:
{
lean_object* v_map_452_; lean_object* v___f_453_; lean_object* v___x_454_; 
v_map_452_ = lean_ctor_get(v_inst_451_, 0);
lean_inc(v_map_452_);
lean_dec_ref(v_inst_451_);
v___f_453_ = ((lean_object*)(l_Lake_getAugmentedEnv___redArg___closed__0));
v___x_454_ = lean_apply_4(v_map_452_, lean_box(0), lean_box(0), v___f_453_, v_inst_450_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv(lean_object* v_m_455_, lean_object* v_inst_456_, lean_object* v_inst_457_){
_start:
{
lean_object* v_map_458_; lean_object* v___f_459_; lean_object* v___x_460_; 
v_map_458_ = lean_ctor_get(v_inst_457_, 0);
lean_inc(v_map_458_);
lean_dec_ref(v_inst_457_);
v___f_459_ = ((lean_object*)(l_Lake_getAugmentedEnv___redArg___closed__0));
v___x_460_ = lean_apply_4(v_map_458_, lean_box(0), lean_box(0), v___f_459_, v_inst_456_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg___lam__0(lean_object* v_x_461_){
_start:
{
lean_object* v_lakeCache_462_; 
v_lakeCache_462_ = lean_ctor_get(v_x_461_, 3);
lean_inc_ref(v_lakeCache_462_);
return v_lakeCache_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg___lam__0___boxed(lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lake_getLakeCache___redArg___lam__0(v_x_463_);
lean_dec_ref(v_x_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache___redArg(lean_object* v_inst_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v_map_468_; lean_object* v___f_469_; lean_object* v___x_470_; 
v_map_468_ = lean_ctor_get(v_inst_467_, 0);
lean_inc(v_map_468_);
lean_dec_ref(v_inst_467_);
v___f_469_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___x_470_ = lean_apply_4(v_map_468_, lean_box(0), lean_box(0), v___f_469_, v_inst_466_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeCache(lean_object* v_m_471_, lean_object* v_inst_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v_map_474_; lean_object* v___f_475_; lean_object* v___x_476_; 
v_map_474_ = lean_ctor_get(v_inst_473_, 0);
lean_inc(v_map_474_);
lean_dec_ref(v_inst_473_);
v___f_475_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___x_476_ = lean_apply_4(v_map_474_, lean_box(0), lean_box(0), v___f_475_, v_inst_472_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f___redArg___lam__1(lean_object* v_descr_477_, lean_object* v_inst_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_alloc_closure((void*)(l_Lake_Cache_getArtifact_x3f___boxed), 3, 2);
lean_closure_set(v___x_480_, 0, v_x_479_);
lean_closure_set(v___x_480_, 1, v_descr_477_);
v___x_481_ = lean_apply_2(v_inst_478_, lean_box(0), v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f___redArg(lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_descr_486_){
_start:
{
lean_object* v_map_487_; lean_object* v___f_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_map_487_ = lean_ctor_get(v_inst_483_, 0);
lean_inc(v_map_487_);
lean_dec_ref(v_inst_483_);
v___f_488_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___f_489_ = lean_alloc_closure((void*)(l_Lake_getArtifact_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_489_, 0, v_descr_486_);
lean_closure_set(v___f_489_, 1, v_inst_485_);
v___x_490_ = lean_apply_4(v_map_487_, lean_box(0), lean_box(0), v___f_488_, v_inst_482_);
v___x_491_ = lean_apply_4(v_inst_484_, lean_box(0), lean_box(0), v___x_490_, v___f_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_getArtifact_x3f(lean_object* v_m_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_descr_497_){
_start:
{
lean_object* v_map_498_; lean_object* v___f_499_; lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_map_498_ = lean_ctor_get(v_inst_494_, 0);
lean_inc(v_map_498_);
lean_dec_ref(v_inst_494_);
v___f_499_ = ((lean_object*)(l_Lake_getLakeCache___redArg___closed__0));
v___f_500_ = lean_alloc_closure((void*)(l_Lake_getArtifact_x3f___redArg___lam__1), 3, 2);
lean_closure_set(v___f_500_, 0, v_descr_497_);
lean_closure_set(v___f_500_, 1, v_inst_496_);
v___x_501_ = lean_apply_4(v_map_498_, lean_box(0), lean_box(0), v___f_499_, v_inst_493_);
v___x_502_ = lean_apply_4(v_inst_495_, lean_box(0), lean_box(0), v___x_501_, v___f_500_);
return v___x_502_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_restoreAllArtifacts___redArg___lam__0(lean_object* v_self_503_, lean_object* v_x_504_){
_start:
{
lean_object* v_config_505_; lean_object* v_restoreAllArtifacts_x3f_506_; 
v_config_505_ = lean_ctor_get(v_self_503_, 6);
v_restoreAllArtifacts_x3f_506_ = lean_ctor_get(v_config_505_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_506_) == 0)
{
lean_object* v_root_507_; lean_object* v_config_508_; lean_object* v_restoreAllArtifacts_x3f_509_; 
v_root_507_ = lean_ctor_get(v_x_504_, 0);
v_config_508_ = lean_ctor_get(v_root_507_, 6);
v_restoreAllArtifacts_x3f_509_ = lean_ctor_get(v_config_508_, 25);
if (lean_obj_tag(v_restoreAllArtifacts_x3f_509_) == 0)
{
uint8_t v___x_510_; 
v___x_510_ = 0;
return v___x_510_;
}
else
{
lean_object* v_val_511_; uint8_t v___x_512_; 
v_val_511_ = lean_ctor_get(v_restoreAllArtifacts_x3f_509_, 0);
v___x_512_ = lean_unbox(v_val_511_);
return v___x_512_;
}
}
else
{
lean_object* v_val_513_; uint8_t v___x_514_; 
v_val_513_ = lean_ctor_get(v_restoreAllArtifacts_x3f_506_, 0);
v___x_514_ = lean_unbox(v_val_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed(lean_object* v_self_515_, lean_object* v_x_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_Lake_Package_restoreAllArtifacts___redArg___lam__0(v_self_515_, v_x_516_);
lean_dec_ref(v_x_516_);
lean_dec_ref(v_self_515_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg(lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_self_521_){
_start:
{
lean_object* v_map_522_; lean_object* v___f_523_; lean_object* v___x_524_; 
v_map_522_ = lean_ctor_get(v_inst_519_, 0);
lean_inc(v_map_522_);
lean_dec_ref(v_inst_519_);
v___f_523_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_523_, 0, v_self_521_);
v___x_524_ = lean_apply_4(v_map_522_, lean_box(0), lean_box(0), v___f_523_, v_inst_520_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts(lean_object* v_m_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_self_528_){
_start:
{
lean_object* v_map_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
v_map_529_ = lean_ctor_get(v_inst_526_, 0);
lean_inc(v_map_529_);
lean_dec_ref(v_inst_526_);
v___f_530_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_530_, 0, v_self_528_);
v___x_531_ = lean_apply_4(v_map_529_, lean_box(0), lean_box(0), v___f_530_, v_inst_527_);
return v___x_531_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(lean_object* v_self_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_config_534_; lean_object* v_enableArtifactCache_x3f_535_; 
v_config_534_ = lean_ctor_get(v_self_532_, 6);
v_enableArtifactCache_x3f_535_ = lean_ctor_get(v_config_534_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_535_) == 0)
{
lean_object* v_lakeEnv_536_; lean_object* v_enableArtifactCache_x3f_537_; 
v_lakeEnv_536_ = lean_ctor_get(v_x_533_, 1);
v_enableArtifactCache_x3f_537_ = lean_ctor_get(v_lakeEnv_536_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_537_) == 0)
{
lean_object* v_root_538_; lean_object* v_config_539_; lean_object* v_enableArtifactCache_x3f_540_; 
v_root_538_ = lean_ctor_get(v_x_533_, 0);
v_config_539_ = lean_ctor_get(v_root_538_, 6);
v_enableArtifactCache_x3f_540_ = lean_ctor_get(v_config_539_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_540_) == 0)
{
uint8_t v___x_541_; 
v___x_541_ = 1;
return v___x_541_;
}
else
{
lean_object* v_val_542_; uint8_t v___x_543_; 
v_val_542_ = lean_ctor_get(v_enableArtifactCache_x3f_540_, 0);
v___x_543_ = lean_unbox(v_val_542_);
return v___x_543_;
}
}
else
{
lean_object* v_val_544_; uint8_t v___x_545_; 
v_val_544_ = lean_ctor_get(v_enableArtifactCache_x3f_537_, 0);
v___x_545_ = lean_unbox(v_val_544_);
return v___x_545_;
}
}
else
{
lean_object* v_val_546_; uint8_t v___x_547_; 
v_val_546_ = lean_ctor_get(v_enableArtifactCache_x3f_535_, 0);
v___x_547_ = lean_unbox(v_val_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed(lean_object* v_self_548_, lean_object* v_x_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(v_self_548_, v_x_549_);
lean_dec_ref(v_x_549_);
lean_dec_ref(v_self_548_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg(lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_self_554_){
_start:
{
lean_object* v_map_555_; lean_object* v___f_556_; lean_object* v___x_557_; 
v_map_555_ = lean_ctor_get(v_inst_552_, 0);
lean_inc(v_map_555_);
lean_dec_ref(v_inst_552_);
v___f_556_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_556_, 0, v_self_554_);
v___x_557_ = lean_apply_4(v_map_555_, lean_box(0), lean_box(0), v___f_556_, v_inst_553_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable(lean_object* v_m_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_self_561_){
_start:
{
lean_object* v_map_562_; lean_object* v___f_563_; lean_object* v___x_564_; 
v_map_562_ = lean_ctor_get(v_inst_559_, 0);
lean_inc(v_map_562_);
lean_dec_ref(v_inst_559_);
v___f_563_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_563_, 0, v_self_561_);
v___x_564_ = lean_apply_4(v_map_562_, lean_box(0), lean_box(0), v___f_563_, v_inst_560_);
return v___x_564_;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(lean_object* v_self_565_, lean_object* v_x_566_){
_start:
{
lean_object* v_config_567_; lean_object* v_enableArtifactCache_x3f_568_; 
v_config_567_ = lean_ctor_get(v_self_565_, 6);
v_enableArtifactCache_x3f_568_ = lean_ctor_get(v_config_567_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_568_) == 0)
{
lean_object* v_lakeEnv_569_; lean_object* v_enableArtifactCache_x3f_570_; 
v_lakeEnv_569_ = lean_ctor_get(v_x_566_, 1);
v_enableArtifactCache_x3f_570_ = lean_ctor_get(v_lakeEnv_569_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_570_) == 0)
{
lean_object* v_root_571_; lean_object* v_config_572_; lean_object* v_enableArtifactCache_x3f_573_; 
v_root_571_ = lean_ctor_get(v_x_566_, 0);
v_config_572_ = lean_ctor_get(v_root_571_, 6);
v_enableArtifactCache_x3f_573_ = lean_ctor_get(v_config_572_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_573_) == 0)
{
uint8_t v___x_574_; 
v___x_574_ = 0;
return v___x_574_;
}
else
{
lean_object* v_val_575_; uint8_t v___x_576_; 
v_val_575_ = lean_ctor_get(v_enableArtifactCache_x3f_573_, 0);
v___x_576_ = lean_unbox(v_val_575_);
return v___x_576_;
}
}
else
{
lean_object* v_val_577_; uint8_t v___x_578_; 
v_val_577_ = lean_ctor_get(v_enableArtifactCache_x3f_570_, 0);
v___x_578_ = lean_unbox(v_val_577_);
return v___x_578_;
}
}
else
{
lean_object* v_val_579_; uint8_t v___x_580_; 
v_val_579_ = lean_ctor_get(v_enableArtifactCache_x3f_568_, 0);
v___x_580_ = lean_unbox(v_val_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed(lean_object* v_self_581_, lean_object* v_x_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(v_self_581_, v_x_582_);
lean_dec_ref(v_x_582_);
lean_dec_ref(v_self_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg(lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_self_587_){
_start:
{
lean_object* v_map_588_; lean_object* v___f_589_; lean_object* v___x_590_; 
v_map_588_ = lean_ctor_get(v_inst_585_, 0);
lean_inc(v_map_588_);
lean_dec_ref(v_inst_585_);
v___f_589_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_589_, 0, v_self_587_);
v___x_590_ = lean_apply_4(v_map_588_, lean_box(0), lean_box(0), v___f_589_, v_inst_586_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable(lean_object* v_m_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_self_594_){
_start:
{
lean_object* v_map_595_; lean_object* v___f_596_; lean_object* v___x_597_; 
v_map_595_ = lean_ctor_get(v_inst_592_, 0);
lean_inc(v_map_595_);
lean_dec_ref(v_inst_592_);
v___f_596_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_596_, 0, v_self_594_);
v___x_597_ = lean_apply_4(v_map_595_, lean_box(0), lean_box(0), v___f_596_, v_inst_593_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___redArg(lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v_self_600_){
_start:
{
lean_object* v_map_601_; lean_object* v___f_602_; lean_object* v___x_603_; 
v_map_601_ = lean_ctor_get(v_inst_598_, 0);
lean_inc(v_map_601_);
lean_dec_ref(v_inst_598_);
v___f_602_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_602_, 0, v_self_600_);
v___x_603_ = lean_apply_4(v_map_601_, lean_box(0), lean_box(0), v___f_602_, v_inst_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled(lean_object* v_m_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_self_607_){
_start:
{
lean_object* v_map_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
v_map_608_ = lean_ctor_get(v_inst_605_, 0);
lean_inc(v_map_608_);
lean_dec_ref(v_inst_605_);
v___f_609_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_609_, 0, v_self_607_);
v___x_610_ = lean_apply_4(v_map_608_, lean_box(0), lean_box(0), v___f_609_, v_inst_606_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg(lean_object* v_inst_611_){
_start:
{
lean_inc(v_inst_611_);
return v_inst_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg___boxed(lean_object* v_inst_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lake_getLakeEnv___redArg(v_inst_612_);
lean_dec(v_inst_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv(lean_object* v_m_614_, lean_object* v_inst_615_){
_start:
{
lean_inc(v_inst_615_);
return v_inst_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___boxed(lean_object* v_m_616_, lean_object* v_inst_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lake_getLakeEnv(v_m_616_, v_inst_617_);
lean_dec(v_inst_617_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoCache___redArg___lam__0(lean_object* v_x_619_){
_start:
{
uint8_t v_noCache_620_; 
v_noCache_620_ = lean_ctor_get_uint8(v_x_619_, sizeof(void*)*19);
return v_noCache_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg___lam__0___boxed(lean_object* v_x_621_){
_start:
{
uint8_t v_res_622_; lean_object* v_r_623_; 
v_res_622_ = l_Lake_getNoCache___redArg___lam__0(v_x_621_);
lean_dec_ref(v_x_621_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg(lean_object* v_inst_625_, lean_object* v_inst_626_){
_start:
{
lean_object* v_map_627_; lean_object* v___f_628_; lean_object* v___x_629_; 
v_map_627_ = lean_ctor_get(v_inst_626_, 0);
lean_inc(v_map_627_);
lean_dec_ref(v_inst_626_);
v___f_628_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_629_ = lean_apply_4(v_map_627_, lean_box(0), lean_box(0), v___f_628_, v_inst_625_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache(lean_object* v_m_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_){
_start:
{
lean_object* v_map_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
v_map_634_ = lean_ctor_get(v_inst_632_, 0);
lean_inc(v_map_634_);
lean_dec_ref(v_inst_632_);
v___f_635_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_636_ = lean_apply_4(v_map_634_, lean_box(0), lean_box(0), v___f_635_, v_inst_631_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___boxed(lean_object* v_m_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_inst_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lake_getNoCache(v_m_637_, v_inst_638_, v_inst_639_, v_inst_640_);
lean_dec(v_inst_640_);
return v_res_641_;
}
}
LEAN_EXPORT uint8_t l_Lake_getTryCache___redArg___lam__0(lean_object* v_x_642_){
_start:
{
uint8_t v_noCache_643_; 
v_noCache_643_ = lean_ctor_get_uint8(v_x_642_, sizeof(void*)*19);
if (v_noCache_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = 1;
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = 0;
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg___lam__0___boxed(lean_object* v_x_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Lake_getTryCache___redArg___lam__0(v_x_646_);
lean_dec_ref(v_x_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg(lean_object* v_inst_650_, lean_object* v_inst_651_){
_start:
{
lean_object* v_map_652_; lean_object* v___f_653_; lean_object* v___x_654_; 
v_map_652_ = lean_ctor_get(v_inst_651_, 0);
lean_inc(v_map_652_);
lean_dec_ref(v_inst_651_);
v___f_653_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_654_ = lean_apply_4(v_map_652_, lean_box(0), lean_box(0), v___f_653_, v_inst_650_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object* v_m_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v_map_659_; lean_object* v___f_660_; lean_object* v___x_661_; 
v_map_659_ = lean_ctor_get(v_inst_657_, 0);
lean_inc(v_map_659_);
lean_dec_ref(v_inst_657_);
v___f_660_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_661_ = lean_apply_4(v_map_659_, lean_box(0), lean_box(0), v___f_660_, v_inst_656_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___boxed(lean_object* v_m_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lake_getTryCache(v_m_662_, v_inst_663_, v_inst_664_, v_inst_665_);
lean_dec(v_inst_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0(lean_object* v_x_667_){
_start:
{
lean_object* v_pkgUrlMap_668_; 
v_pkgUrlMap_668_ = lean_ctor_get(v_x_667_, 5);
lean_inc(v_pkgUrlMap_668_);
return v_pkgUrlMap_668_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0___boxed(lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lake_getPkgUrlMap___redArg___lam__0(v_x_669_);
lean_dec_ref(v_x_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg(lean_object* v_inst_672_, lean_object* v_inst_673_){
_start:
{
lean_object* v_map_674_; lean_object* v___f_675_; lean_object* v___x_676_; 
v_map_674_ = lean_ctor_get(v_inst_673_, 0);
lean_inc(v_map_674_);
lean_dec_ref(v_inst_673_);
v___f_675_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_676_ = lean_apply_4(v_map_674_, lean_box(0), lean_box(0), v___f_675_, v_inst_672_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object* v_m_677_, lean_object* v_inst_678_, lean_object* v_inst_679_){
_start:
{
lean_object* v_map_680_; lean_object* v___f_681_; lean_object* v___x_682_; 
v_map_680_ = lean_ctor_get(v_inst_679_, 0);
lean_inc(v_map_680_);
lean_dec_ref(v_inst_679_);
v___f_681_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_682_ = lean_apply_4(v_map_680_, lean_box(0), lean_box(0), v___f_681_, v_inst_678_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0(lean_object* v_x_683_){
_start:
{
lean_object* v_toolchain_684_; 
v_toolchain_684_ = lean_ctor_get(v_x_683_, 18);
lean_inc_ref(v_toolchain_684_);
return v_toolchain_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0___boxed(lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lake_getElanToolchain___redArg___lam__0(v_x_685_);
lean_dec_ref(v_x_685_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg(lean_object* v_inst_688_, lean_object* v_inst_689_){
_start:
{
lean_object* v_map_690_; lean_object* v___f_691_; lean_object* v___x_692_; 
v_map_690_ = lean_ctor_get(v_inst_689_, 0);
lean_inc(v_map_690_);
lean_dec_ref(v_inst_689_);
v___f_691_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_692_ = lean_apply_4(v_map_690_, lean_box(0), lean_box(0), v___f_691_, v_inst_688_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object* v_m_693_, lean_object* v_inst_694_, lean_object* v_inst_695_){
_start:
{
lean_object* v_map_696_; lean_object* v___f_697_; lean_object* v___x_698_; 
v_map_696_ = lean_ctor_get(v_inst_695_, 0);
lean_inc(v_map_696_);
lean_dec_ref(v_inst_695_);
v___f_697_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_698_ = lean_apply_4(v_map_696_, lean_box(0), lean_box(0), v___f_697_, v_inst_694_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___redArg(lean_object* v_inst_700_, lean_object* v_inst_701_){
_start:
{
lean_object* v_map_702_; lean_object* v___f_703_; lean_object* v___x_704_; 
v_map_702_ = lean_ctor_get(v_inst_701_, 0);
lean_inc(v_map_702_);
lean_dec_ref(v_inst_701_);
v___f_703_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_704_ = lean_apply_4(v_map_702_, lean_box(0), lean_box(0), v___f_703_, v_inst_700_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object* v_m_705_, lean_object* v_inst_706_, lean_object* v_inst_707_){
_start:
{
lean_object* v_map_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v_map_708_ = lean_ctor_get(v_inst_707_, 0);
lean_inc(v_map_708_);
lean_dec_ref(v_inst_707_);
v___f_709_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_710_ = lean_apply_4(v_map_708_, lean_box(0), lean_box(0), v___f_709_, v_inst_706_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___redArg(lean_object* v_inst_712_, lean_object* v_inst_713_){
_start:
{
lean_object* v_map_714_; lean_object* v___f_715_; lean_object* v___x_716_; 
v_map_714_ = lean_ctor_get(v_inst_713_, 0);
lean_inc(v_map_714_);
lean_dec_ref(v_inst_713_);
v___f_715_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_716_ = lean_apply_4(v_map_714_, lean_box(0), lean_box(0), v___f_715_, v_inst_712_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object* v_m_717_, lean_object* v_inst_718_, lean_object* v_inst_719_){
_start:
{
lean_object* v_map_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
v_map_720_ = lean_ctor_get(v_inst_719_, 0);
lean_inc(v_map_720_);
lean_dec_ref(v_inst_719_);
v___f_721_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_722_ = lean_apply_4(v_map_720_, lean_box(0), lean_box(0), v___f_721_, v_inst_718_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___redArg(lean_object* v_inst_724_, lean_object* v_inst_725_){
_start:
{
lean_object* v_map_726_; lean_object* v___f_727_; lean_object* v___x_728_; 
v_map_726_ = lean_ctor_get(v_inst_725_, 0);
lean_inc(v_map_726_);
lean_dec_ref(v_inst_725_);
v___f_727_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_728_ = lean_apply_4(v_map_726_, lean_box(0), lean_box(0), v___f_727_, v_inst_724_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object* v_m_729_, lean_object* v_inst_730_, lean_object* v_inst_731_){
_start:
{
lean_object* v_map_732_; lean_object* v___f_733_; lean_object* v___x_734_; 
v_map_732_ = lean_ctor_get(v_inst_731_, 0);
lean_inc(v_map_732_);
lean_dec_ref(v_inst_731_);
v___f_733_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_734_ = lean_apply_4(v_map_732_, lean_box(0), lean_box(0), v___f_733_, v_inst_730_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0(lean_object* v_x_735_){
_start:
{
lean_object* v_elan_x3f_736_; 
v_elan_x3f_736_ = lean_ctor_get(v_x_735_, 2);
lean_inc(v_elan_x3f_736_);
return v_elan_x3f_736_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0___boxed(lean_object* v_x_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lake_getElanInstall_x3f___redArg___lam__0(v_x_737_);
lean_dec_ref(v_x_737_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg(lean_object* v_inst_740_, lean_object* v_inst_741_){
_start:
{
lean_object* v_map_742_; lean_object* v___f_743_; lean_object* v___x_744_; 
v_map_742_ = lean_ctor_get(v_inst_741_, 0);
lean_inc(v_map_742_);
lean_dec_ref(v_inst_741_);
v___f_743_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_744_ = lean_apply_4(v_map_742_, lean_box(0), lean_box(0), v___f_743_, v_inst_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object* v_m_745_, lean_object* v_inst_746_, lean_object* v_inst_747_){
_start:
{
lean_object* v_map_748_; lean_object* v___f_749_; lean_object* v___x_750_; 
v_map_748_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_map_748_);
lean_dec_ref(v_inst_747_);
v___f_749_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_750_ = lean_apply_4(v_map_748_, lean_box(0), lean_box(0), v___f_749_, v_inst_746_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg___lam__0(lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_object* v___x_752_; 
v___x_752_ = lean_box(0);
return v___x_752_;
}
else
{
lean_object* v_val_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_val_753_ = lean_ctor_get(v_x_751_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_761_ == 0)
{
v___x_755_ = v_x_751_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_val_753_);
lean_dec(v_x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_home_757_; lean_object* v___x_759_; 
v_home_757_ = lean_ctor_get(v_val_753_, 0);
lean_inc_ref(v_home_757_);
lean_dec(v_val_753_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_home_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_home_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg(lean_object* v_inst_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v_map_765_; lean_object* v___f_766_; lean_object* v___f_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_map_765_ = lean_ctor_get(v_inst_764_, 0);
lean_inc_n(v_map_765_, 2);
lean_dec_ref(v_inst_764_);
v___f_766_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_767_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_768_ = lean_apply_4(v_map_765_, lean_box(0), lean_box(0), v___f_767_, v_inst_763_);
v___x_769_ = lean_apply_4(v_map_765_, lean_box(0), lean_box(0), v___f_766_, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object* v_m_770_, lean_object* v_inst_771_, lean_object* v_inst_772_){
_start:
{
lean_object* v_map_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_map_773_ = lean_ctor_get(v_inst_772_, 0);
lean_inc_n(v_map_773_, 2);
lean_dec_ref(v_inst_772_);
v___f_774_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_775_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_776_ = lean_apply_4(v_map_773_, lean_box(0), lean_box(0), v___f_775_, v_inst_771_);
v___x_777_ = lean_apply_4(v_map_773_, lean_box(0), lean_box(0), v___f_774_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg___lam__0(lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v___x_779_; 
v___x_779_ = lean_box(0);
return v___x_779_;
}
else
{
lean_object* v_val_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_val_780_ = lean_ctor_get(v_x_778_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v_x_778_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_val_780_);
lean_dec(v_x_778_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_elan_784_; lean_object* v___x_786_; 
v_elan_784_ = lean_ctor_get(v_val_780_, 1);
lean_inc_ref(v_elan_784_);
lean_dec(v_val_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v_elan_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_elan_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg(lean_object* v_inst_790_, lean_object* v_inst_791_){
_start:
{
lean_object* v_map_792_; lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_map_792_ = lean_ctor_get(v_inst_791_, 0);
lean_inc_n(v_map_792_, 2);
lean_dec_ref(v_inst_791_);
v___f_793_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_794_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_795_ = lean_apply_4(v_map_792_, lean_box(0), lean_box(0), v___f_794_, v_inst_790_);
v___x_796_ = lean_apply_4(v_map_792_, lean_box(0), lean_box(0), v___f_793_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object* v_m_797_, lean_object* v_inst_798_, lean_object* v_inst_799_){
_start:
{
lean_object* v_map_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_map_800_ = lean_ctor_get(v_inst_799_, 0);
lean_inc_n(v_map_800_, 2);
lean_dec_ref(v_inst_799_);
v___f_801_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_802_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_803_ = lean_apply_4(v_map_800_, lean_box(0), lean_box(0), v___f_802_, v_inst_798_);
v___x_804_ = lean_apply_4(v_map_800_, lean_box(0), lean_box(0), v___f_801_, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0(lean_object* v_x_805_){
_start:
{
lean_object* v_lean_806_; 
v_lean_806_ = lean_ctor_get(v_x_805_, 1);
lean_inc_ref(v_lean_806_);
return v_lean_806_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0___boxed(lean_object* v_x_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lake_getLeanInstall___redArg___lam__0(v_x_807_);
lean_dec_ref(v_x_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg(lean_object* v_inst_810_, lean_object* v_inst_811_){
_start:
{
lean_object* v_map_812_; lean_object* v___f_813_; lean_object* v___x_814_; 
v_map_812_ = lean_ctor_get(v_inst_811_, 0);
lean_inc(v_map_812_);
lean_dec_ref(v_inst_811_);
v___f_813_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_814_ = lean_apply_4(v_map_812_, lean_box(0), lean_box(0), v___f_813_, v_inst_810_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v_map_818_; lean_object* v___f_819_; lean_object* v___x_820_; 
v_map_818_ = lean_ctor_get(v_inst_817_, 0);
lean_inc(v_map_818_);
lean_dec_ref(v_inst_817_);
v___f_819_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_820_ = lean_apply_4(v_map_818_, lean_box(0), lean_box(0), v___f_819_, v_inst_816_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0(lean_object* v_x_821_){
_start:
{
lean_object* v_sysroot_822_; 
v_sysroot_822_ = lean_ctor_get(v_x_821_, 0);
lean_inc_ref(v_sysroot_822_);
return v_sysroot_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0___boxed(lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lake_getLeanSysroot___redArg___lam__0(v_x_823_);
lean_dec_ref(v_x_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg(lean_object* v_inst_826_, lean_object* v_inst_827_){
_start:
{
lean_object* v_map_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_map_828_ = lean_ctor_get(v_inst_827_, 0);
lean_inc_n(v_map_828_, 2);
lean_dec_ref(v_inst_827_);
v___f_829_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_830_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_831_ = lean_apply_4(v_map_828_, lean_box(0), lean_box(0), v___f_830_, v_inst_826_);
v___x_832_ = lean_apply_4(v_map_828_, lean_box(0), lean_box(0), v___f_829_, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object* v_m_833_, lean_object* v_inst_834_, lean_object* v_inst_835_){
_start:
{
lean_object* v_map_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_map_836_ = lean_ctor_get(v_inst_835_, 0);
lean_inc_n(v_map_836_, 2);
lean_dec_ref(v_inst_835_);
v___f_837_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_838_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_839_ = lean_apply_4(v_map_836_, lean_box(0), lean_box(0), v___f_838_, v_inst_834_);
v___x_840_ = lean_apply_4(v_map_836_, lean_box(0), lean_box(0), v___f_837_, v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0(lean_object* v_x_841_){
_start:
{
lean_object* v_srcDir_842_; 
v_srcDir_842_ = lean_ctor_get(v_x_841_, 2);
lean_inc_ref(v_srcDir_842_);
return v_srcDir_842_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0___boxed(lean_object* v_x_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lake_getLeanSrcDir___redArg___lam__0(v_x_843_);
lean_dec_ref(v_x_843_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg(lean_object* v_inst_846_, lean_object* v_inst_847_){
_start:
{
lean_object* v_map_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_map_848_ = lean_ctor_get(v_inst_847_, 0);
lean_inc_n(v_map_848_, 2);
lean_dec_ref(v_inst_847_);
v___f_849_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_850_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_851_ = lean_apply_4(v_map_848_, lean_box(0), lean_box(0), v___f_850_, v_inst_846_);
v___x_852_ = lean_apply_4(v_map_848_, lean_box(0), lean_box(0), v___f_849_, v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object* v_m_853_, lean_object* v_inst_854_, lean_object* v_inst_855_){
_start:
{
lean_object* v_map_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_map_856_ = lean_ctor_get(v_inst_855_, 0);
lean_inc_n(v_map_856_, 2);
lean_dec_ref(v_inst_855_);
v___f_857_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_858_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_859_ = lean_apply_4(v_map_856_, lean_box(0), lean_box(0), v___f_858_, v_inst_854_);
v___x_860_ = lean_apply_4(v_map_856_, lean_box(0), lean_box(0), v___f_857_, v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0(lean_object* v_x_861_){
_start:
{
lean_object* v_leanLibDir_862_; 
v_leanLibDir_862_ = lean_ctor_get(v_x_861_, 3);
lean_inc_ref(v_leanLibDir_862_);
return v_leanLibDir_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0___boxed(lean_object* v_x_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lake_getLeanLibDir___redArg___lam__0(v_x_863_);
lean_dec_ref(v_x_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg(lean_object* v_inst_866_, lean_object* v_inst_867_){
_start:
{
lean_object* v_map_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_map_868_ = lean_ctor_get(v_inst_867_, 0);
lean_inc_n(v_map_868_, 2);
lean_dec_ref(v_inst_867_);
v___f_869_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_870_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_871_ = lean_apply_4(v_map_868_, lean_box(0), lean_box(0), v___f_870_, v_inst_866_);
v___x_872_ = lean_apply_4(v_map_868_, lean_box(0), lean_box(0), v___f_869_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object* v_m_873_, lean_object* v_inst_874_, lean_object* v_inst_875_){
_start:
{
lean_object* v_map_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_map_876_ = lean_ctor_get(v_inst_875_, 0);
lean_inc_n(v_map_876_, 2);
lean_dec_ref(v_inst_875_);
v___f_877_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_878_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_879_ = lean_apply_4(v_map_876_, lean_box(0), lean_box(0), v___f_878_, v_inst_874_);
v___x_880_ = lean_apply_4(v_map_876_, lean_box(0), lean_box(0), v___f_877_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0(lean_object* v_x_881_){
_start:
{
lean_object* v_includeDir_882_; 
v_includeDir_882_ = lean_ctor_get(v_x_881_, 4);
lean_inc_ref(v_includeDir_882_);
return v_includeDir_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0___boxed(lean_object* v_x_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lake_getLeanIncludeDir___redArg___lam__0(v_x_883_);
lean_dec_ref(v_x_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg(lean_object* v_inst_886_, lean_object* v_inst_887_){
_start:
{
lean_object* v_map_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_map_888_ = lean_ctor_get(v_inst_887_, 0);
lean_inc_n(v_map_888_, 2);
lean_dec_ref(v_inst_887_);
v___f_889_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_890_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_891_ = lean_apply_4(v_map_888_, lean_box(0), lean_box(0), v___f_890_, v_inst_886_);
v___x_892_ = lean_apply_4(v_map_888_, lean_box(0), lean_box(0), v___f_889_, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object* v_m_893_, lean_object* v_inst_894_, lean_object* v_inst_895_){
_start:
{
lean_object* v_map_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_map_896_ = lean_ctor_get(v_inst_895_, 0);
lean_inc_n(v_map_896_, 2);
lean_dec_ref(v_inst_895_);
v___f_897_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_898_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_899_ = lean_apply_4(v_map_896_, lean_box(0), lean_box(0), v___f_898_, v_inst_894_);
v___x_900_ = lean_apply_4(v_map_896_, lean_box(0), lean_box(0), v___f_897_, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0(lean_object* v_x_901_){
_start:
{
lean_object* v_systemLibDir_902_; 
v_systemLibDir_902_ = lean_ctor_get(v_x_901_, 5);
lean_inc_ref(v_systemLibDir_902_);
return v_systemLibDir_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed(lean_object* v_x_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lake_getLeanSystemLibDir___redArg___lam__0(v_x_903_);
lean_dec_ref(v_x_903_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg(lean_object* v_inst_906_, lean_object* v_inst_907_){
_start:
{
lean_object* v_map_908_; lean_object* v___f_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_map_908_ = lean_ctor_get(v_inst_907_, 0);
lean_inc_n(v_map_908_, 2);
lean_dec_ref(v_inst_907_);
v___f_909_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_910_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_911_ = lean_apply_4(v_map_908_, lean_box(0), lean_box(0), v___f_910_, v_inst_906_);
v___x_912_ = lean_apply_4(v_map_908_, lean_box(0), lean_box(0), v___f_909_, v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object* v_m_913_, lean_object* v_inst_914_, lean_object* v_inst_915_){
_start:
{
lean_object* v_map_916_; lean_object* v___f_917_; lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_map_916_ = lean_ctor_get(v_inst_915_, 0);
lean_inc_n(v_map_916_, 2);
lean_dec_ref(v_inst_915_);
v___f_917_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_918_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_919_ = lean_apply_4(v_map_916_, lean_box(0), lean_box(0), v___f_918_, v_inst_914_);
v___x_920_ = lean_apply_4(v_map_916_, lean_box(0), lean_box(0), v___f_917_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0(lean_object* v_x_921_){
_start:
{
lean_object* v_lean_922_; 
v_lean_922_ = lean_ctor_get(v_x_921_, 7);
lean_inc_ref(v_lean_922_);
return v_lean_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0___boxed(lean_object* v_x_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lake_getLean___redArg___lam__0(v_x_923_);
lean_dec_ref(v_x_923_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg(lean_object* v_inst_926_, lean_object* v_inst_927_){
_start:
{
lean_object* v_map_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_map_928_ = lean_ctor_get(v_inst_927_, 0);
lean_inc_n(v_map_928_, 2);
lean_dec_ref(v_inst_927_);
v___f_929_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_930_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_931_ = lean_apply_4(v_map_928_, lean_box(0), lean_box(0), v___f_930_, v_inst_926_);
v___x_932_ = lean_apply_4(v_map_928_, lean_box(0), lean_box(0), v___f_929_, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object* v_m_933_, lean_object* v_inst_934_, lean_object* v_inst_935_){
_start:
{
lean_object* v_map_936_; lean_object* v___f_937_; lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_map_936_ = lean_ctor_get(v_inst_935_, 0);
lean_inc_n(v_map_936_, 2);
lean_dec_ref(v_inst_935_);
v___f_937_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_938_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_939_ = lean_apply_4(v_map_936_, lean_box(0), lean_box(0), v___f_938_, v_inst_934_);
v___x_940_ = lean_apply_4(v_map_936_, lean_box(0), lean_box(0), v___f_937_, v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0(lean_object* v_x_941_){
_start:
{
lean_object* v_leanir_942_; 
v_leanir_942_ = lean_ctor_get(v_x_941_, 8);
lean_inc_ref(v_leanir_942_);
return v_leanir_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0___boxed(lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lake_getLeanir___redArg___lam__0(v_x_943_);
lean_dec_ref(v_x_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg(lean_object* v_inst_946_, lean_object* v_inst_947_){
_start:
{
lean_object* v_map_948_; lean_object* v___f_949_; lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_map_948_ = lean_ctor_get(v_inst_947_, 0);
lean_inc_n(v_map_948_, 2);
lean_dec_ref(v_inst_947_);
v___f_949_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_950_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_951_ = lean_apply_4(v_map_948_, lean_box(0), lean_box(0), v___f_950_, v_inst_946_);
v___x_952_ = lean_apply_4(v_map_948_, lean_box(0), lean_box(0), v___f_949_, v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir(lean_object* v_m_953_, lean_object* v_inst_954_, lean_object* v_inst_955_){
_start:
{
lean_object* v_map_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_map_956_ = lean_ctor_get(v_inst_955_, 0);
lean_inc_n(v_map_956_, 2);
lean_dec_ref(v_inst_955_);
v___f_957_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_958_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_959_ = lean_apply_4(v_map_956_, lean_box(0), lean_box(0), v___f_958_, v_inst_954_);
v___x_960_ = lean_apply_4(v_map_956_, lean_box(0), lean_box(0), v___f_957_, v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0(lean_object* v_x_961_){
_start:
{
lean_object* v_leanc_962_; 
v_leanc_962_ = lean_ctor_get(v_x_961_, 9);
lean_inc_ref(v_leanc_962_);
return v_leanc_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0___boxed(lean_object* v_x_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lake_getLeanc___redArg___lam__0(v_x_963_);
lean_dec_ref(v_x_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg(lean_object* v_inst_966_, lean_object* v_inst_967_){
_start:
{
lean_object* v_map_968_; lean_object* v___f_969_; lean_object* v___f_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_map_968_ = lean_ctor_get(v_inst_967_, 0);
lean_inc_n(v_map_968_, 2);
lean_dec_ref(v_inst_967_);
v___f_969_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_970_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_971_ = lean_apply_4(v_map_968_, lean_box(0), lean_box(0), v___f_970_, v_inst_966_);
v___x_972_ = lean_apply_4(v_map_968_, lean_box(0), lean_box(0), v___f_969_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object* v_m_973_, lean_object* v_inst_974_, lean_object* v_inst_975_){
_start:
{
lean_object* v_map_976_; lean_object* v___f_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_map_976_ = lean_ctor_get(v_inst_975_, 0);
lean_inc_n(v_map_976_, 2);
lean_dec_ref(v_inst_975_);
v___f_977_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_978_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_979_ = lean_apply_4(v_map_976_, lean_box(0), lean_box(0), v___f_978_, v_inst_974_);
v___x_980_ = lean_apply_4(v_map_976_, lean_box(0), lean_box(0), v___f_977_, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0(lean_object* v_x_981_){
_start:
{
lean_object* v_leantar_982_; 
v_leantar_982_ = lean_ctor_get(v_x_981_, 10);
lean_inc_ref(v_leantar_982_);
return v_leantar_982_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0___boxed(lean_object* v_x_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lake_getLeantar___redArg___lam__0(v_x_983_);
lean_dec_ref(v_x_983_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg(lean_object* v_inst_986_, lean_object* v_inst_987_){
_start:
{
lean_object* v_map_988_; lean_object* v___f_989_; lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_map_988_ = lean_ctor_get(v_inst_987_, 0);
lean_inc_n(v_map_988_, 2);
lean_dec_ref(v_inst_987_);
v___f_989_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_990_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_991_ = lean_apply_4(v_map_988_, lean_box(0), lean_box(0), v___f_990_, v_inst_986_);
v___x_992_ = lean_apply_4(v_map_988_, lean_box(0), lean_box(0), v___f_989_, v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar(lean_object* v_m_993_, lean_object* v_inst_994_, lean_object* v_inst_995_){
_start:
{
lean_object* v_map_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_map_996_ = lean_ctor_get(v_inst_995_, 0);
lean_inc_n(v_map_996_, 2);
lean_dec_ref(v_inst_995_);
v___f_997_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_998_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_999_ = lean_apply_4(v_map_996_, lean_box(0), lean_box(0), v___f_998_, v_inst_994_);
v___x_1000_ = lean_apply_4(v_map_996_, lean_box(0), lean_box(0), v___f_997_, v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0(lean_object* v_x_1001_){
_start:
{
lean_object* v_sharedLib_1002_; 
v_sharedLib_1002_ = lean_ctor_get(v_x_1001_, 11);
lean_inc_ref(v_sharedLib_1002_);
return v_sharedLib_1002_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0___boxed(lean_object* v_x_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lake_getLeanSharedLib___redArg___lam__0(v_x_1003_);
lean_dec_ref(v_x_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg(lean_object* v_inst_1006_, lean_object* v_inst_1007_){
_start:
{
lean_object* v_map_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_map_1008_ = lean_ctor_get(v_inst_1007_, 0);
lean_inc_n(v_map_1008_, 2);
lean_dec_ref(v_inst_1007_);
v___f_1009_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1010_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1011_ = lean_apply_4(v_map_1008_, lean_box(0), lean_box(0), v___f_1010_, v_inst_1006_);
v___x_1012_ = lean_apply_4(v_map_1008_, lean_box(0), lean_box(0), v___f_1009_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_){
_start:
{
lean_object* v_map_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_map_1016_ = lean_ctor_get(v_inst_1015_, 0);
lean_inc_n(v_map_1016_, 2);
lean_dec_ref(v_inst_1015_);
v___f_1017_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1018_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1019_ = lean_apply_4(v_map_1016_, lean_box(0), lean_box(0), v___f_1018_, v_inst_1014_);
v___x_1020_ = lean_apply_4(v_map_1016_, lean_box(0), lean_box(0), v___f_1017_, v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0(lean_object* v_x_1021_){
_start:
{
lean_object* v_ar_1022_; 
v_ar_1022_ = lean_ctor_get(v_x_1021_, 13);
lean_inc_ref(v_ar_1022_);
return v_ar_1022_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0___boxed(lean_object* v_x_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lake_getLeanAr___redArg___lam__0(v_x_1023_);
lean_dec_ref(v_x_1023_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_){
_start:
{
lean_object* v_map_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_map_1028_ = lean_ctor_get(v_inst_1027_, 0);
lean_inc_n(v_map_1028_, 2);
lean_dec_ref(v_inst_1027_);
v___f_1029_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1030_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1031_ = lean_apply_4(v_map_1028_, lean_box(0), lean_box(0), v___f_1030_, v_inst_1026_);
v___x_1032_ = lean_apply_4(v_map_1028_, lean_box(0), lean_box(0), v___f_1029_, v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object* v_m_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_){
_start:
{
lean_object* v_map_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_map_1036_ = lean_ctor_get(v_inst_1035_, 0);
lean_inc_n(v_map_1036_, 2);
lean_dec_ref(v_inst_1035_);
v___f_1037_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1038_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1039_ = lean_apply_4(v_map_1036_, lean_box(0), lean_box(0), v___f_1038_, v_inst_1034_);
v___x_1040_ = lean_apply_4(v_map_1036_, lean_box(0), lean_box(0), v___f_1037_, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0(lean_object* v_x_1041_){
_start:
{
lean_object* v_cc_1042_; 
v_cc_1042_ = lean_ctor_get(v_x_1041_, 14);
lean_inc_ref(v_cc_1042_);
return v_cc_1042_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0___boxed(lean_object* v_x_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lake_getLeanCc___redArg___lam__0(v_x_1043_);
lean_dec_ref(v_x_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg(lean_object* v_inst_1046_, lean_object* v_inst_1047_){
_start:
{
lean_object* v_map_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_map_1048_ = lean_ctor_get(v_inst_1047_, 0);
lean_inc_n(v_map_1048_, 2);
lean_dec_ref(v_inst_1047_);
v___f_1049_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1050_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1051_ = lean_apply_4(v_map_1048_, lean_box(0), lean_box(0), v___f_1050_, v_inst_1046_);
v___x_1052_ = lean_apply_4(v_map_1048_, lean_box(0), lean_box(0), v___f_1049_, v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object* v_m_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_){
_start:
{
lean_object* v_map_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_map_1056_ = lean_ctor_get(v_inst_1055_, 0);
lean_inc_n(v_map_1056_, 2);
lean_dec_ref(v_inst_1055_);
v___f_1057_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1058_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1059_ = lean_apply_4(v_map_1056_, lean_box(0), lean_box(0), v___f_1058_, v_inst_1054_);
v___x_1060_ = lean_apply_4(v_map_1056_, lean_box(0), lean_box(0), v___f_1057_, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___redArg(lean_object* v_inst_1062_, lean_object* v_inst_1063_){
_start:
{
lean_object* v_map_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_map_1064_ = lean_ctor_get(v_inst_1063_, 0);
lean_inc_n(v_map_1064_, 2);
lean_dec_ref(v_inst_1063_);
v___f_1065_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1066_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1067_ = lean_apply_4(v_map_1064_, lean_box(0), lean_box(0), v___f_1066_, v_inst_1062_);
v___x_1068_ = lean_apply_4(v_map_1064_, lean_box(0), lean_box(0), v___f_1065_, v___x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object* v_m_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_){
_start:
{
lean_object* v_map_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_map_1072_ = lean_ctor_get(v_inst_1071_, 0);
lean_inc_n(v_map_1072_, 2);
lean_dec_ref(v_inst_1071_);
v___f_1073_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1074_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1075_ = lean_apply_4(v_map_1072_, lean_box(0), lean_box(0), v___f_1074_, v_inst_1070_);
v___x_1076_ = lean_apply_4(v_map_1072_, lean_box(0), lean_box(0), v___f_1073_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0(lean_object* v_x_1077_){
_start:
{
lean_object* v_ccLinkSharedFlags_1078_; 
v_ccLinkSharedFlags_1078_ = lean_ctor_get(v_x_1077_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1078_);
return v_ccLinkSharedFlags_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed(lean_object* v_x_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lake_getLeanLinkSharedFlags___redArg___lam__0(v_x_1079_);
lean_dec_ref(v_x_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg(lean_object* v_inst_1082_, lean_object* v_inst_1083_){
_start:
{
lean_object* v_map_1084_; lean_object* v___f_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_map_1084_ = lean_ctor_get(v_inst_1083_, 0);
lean_inc_n(v_map_1084_, 2);
lean_dec_ref(v_inst_1083_);
v___f_1085_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1086_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1087_ = lean_apply_4(v_map_1084_, lean_box(0), lean_box(0), v___f_1086_, v_inst_1082_);
v___x_1088_ = lean_apply_4(v_map_1084_, lean_box(0), lean_box(0), v___f_1085_, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags(lean_object* v_m_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_){
_start:
{
lean_object* v_map_1092_; lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_map_1092_ = lean_ctor_get(v_inst_1091_, 0);
lean_inc_n(v_map_1092_, 2);
lean_dec_ref(v_inst_1091_);
v___f_1093_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1094_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1095_ = lean_apply_4(v_map_1092_, lean_box(0), lean_box(0), v___f_1094_, v_inst_1090_);
v___x_1096_ = lean_apply_4(v_map_1092_, lean_box(0), lean_box(0), v___f_1093_, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0(lean_object* v_x_1097_){
_start:
{
lean_object* v_lake_1098_; 
v_lake_1098_ = lean_ctor_get(v_x_1097_, 0);
lean_inc_ref(v_lake_1098_);
return v_lake_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0___boxed(lean_object* v_x_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lake_getLakeInstall___redArg___lam__0(v_x_1099_);
lean_dec_ref(v_x_1099_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg(lean_object* v_inst_1102_, lean_object* v_inst_1103_){
_start:
{
lean_object* v_map_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v_map_1104_ = lean_ctor_get(v_inst_1103_, 0);
lean_inc(v_map_1104_);
lean_dec_ref(v_inst_1103_);
v___f_1105_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1106_ = lean_apply_4(v_map_1104_, lean_box(0), lean_box(0), v___f_1105_, v_inst_1102_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object* v_m_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_){
_start:
{
lean_object* v_map_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
v_map_1110_ = lean_ctor_get(v_inst_1109_, 0);
lean_inc(v_map_1110_);
lean_dec_ref(v_inst_1109_);
v___f_1111_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1112_ = lean_apply_4(v_map_1110_, lean_box(0), lean_box(0), v___f_1111_, v_inst_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0(lean_object* v_x_1113_){
_start:
{
lean_object* v_home_1114_; 
v_home_1114_ = lean_ctor_get(v_x_1113_, 0);
lean_inc_ref(v_home_1114_);
return v_home_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0___boxed(lean_object* v_x_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lake_getLakeHome___redArg___lam__0(v_x_1115_);
lean_dec_ref(v_x_1115_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v_map_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_map_1120_ = lean_ctor_get(v_inst_1119_, 0);
lean_inc_n(v_map_1120_, 2);
lean_dec_ref(v_inst_1119_);
v___f_1121_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1122_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1123_ = lean_apply_4(v_map_1120_, lean_box(0), lean_box(0), v___f_1122_, v_inst_1118_);
v___x_1124_ = lean_apply_4(v_map_1120_, lean_box(0), lean_box(0), v___f_1121_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object* v_m_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_){
_start:
{
lean_object* v_map_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_map_1128_ = lean_ctor_get(v_inst_1127_, 0);
lean_inc_n(v_map_1128_, 2);
lean_dec_ref(v_inst_1127_);
v___f_1129_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1130_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1131_ = lean_apply_4(v_map_1128_, lean_box(0), lean_box(0), v___f_1130_, v_inst_1126_);
v___x_1132_ = lean_apply_4(v_map_1128_, lean_box(0), lean_box(0), v___f_1129_, v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0(lean_object* v_x_1133_){
_start:
{
lean_object* v_srcDir_1134_; 
v_srcDir_1134_ = lean_ctor_get(v_x_1133_, 1);
lean_inc_ref(v_srcDir_1134_);
return v_srcDir_1134_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0___boxed(lean_object* v_x_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lake_getLakeSrcDir___redArg___lam__0(v_x_1135_);
lean_dec_ref(v_x_1135_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg(lean_object* v_inst_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v_map_1140_; lean_object* v___f_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_map_1140_ = lean_ctor_get(v_inst_1139_, 0);
lean_inc_n(v_map_1140_, 2);
lean_dec_ref(v_inst_1139_);
v___f_1141_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1142_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1143_ = lean_apply_4(v_map_1140_, lean_box(0), lean_box(0), v___f_1142_, v_inst_1138_);
v___x_1144_ = lean_apply_4(v_map_1140_, lean_box(0), lean_box(0), v___f_1141_, v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object* v_m_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_){
_start:
{
lean_object* v_map_1148_; lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_map_1148_ = lean_ctor_get(v_inst_1147_, 0);
lean_inc_n(v_map_1148_, 2);
lean_dec_ref(v_inst_1147_);
v___f_1149_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1150_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1151_ = lean_apply_4(v_map_1148_, lean_box(0), lean_box(0), v___f_1150_, v_inst_1146_);
v___x_1152_ = lean_apply_4(v_map_1148_, lean_box(0), lean_box(0), v___f_1149_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0(lean_object* v_x_1153_){
_start:
{
lean_object* v_libDir_1154_; 
v_libDir_1154_ = lean_ctor_get(v_x_1153_, 3);
lean_inc_ref(v_libDir_1154_);
return v_libDir_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0___boxed(lean_object* v_x_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lake_getLakeLibDir___redArg___lam__0(v_x_1155_);
lean_dec_ref(v_x_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg(lean_object* v_inst_1158_, lean_object* v_inst_1159_){
_start:
{
lean_object* v_map_1160_; lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_map_1160_ = lean_ctor_get(v_inst_1159_, 0);
lean_inc_n(v_map_1160_, 2);
lean_dec_ref(v_inst_1159_);
v___f_1161_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1162_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1163_ = lean_apply_4(v_map_1160_, lean_box(0), lean_box(0), v___f_1162_, v_inst_1158_);
v___x_1164_ = lean_apply_4(v_map_1160_, lean_box(0), lean_box(0), v___f_1161_, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object* v_m_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v_map_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_map_1168_ = lean_ctor_get(v_inst_1167_, 0);
lean_inc_n(v_map_1168_, 2);
lean_dec_ref(v_inst_1167_);
v___f_1169_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1170_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1171_ = lean_apply_4(v_map_1168_, lean_box(0), lean_box(0), v___f_1170_, v_inst_1166_);
v___x_1172_ = lean_apply_4(v_map_1168_, lean_box(0), lean_box(0), v___f_1169_, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0(lean_object* v_x_1173_){
_start:
{
lean_object* v_lake_1174_; 
v_lake_1174_ = lean_ctor_get(v_x_1173_, 5);
lean_inc_ref(v_lake_1174_);
return v_lake_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0___boxed(lean_object* v_x_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lake_getLake___redArg___lam__0(v_x_1175_);
lean_dec_ref(v_x_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg(lean_object* v_inst_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v_map_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_map_1180_ = lean_ctor_get(v_inst_1179_, 0);
lean_inc_n(v_map_1180_, 2);
lean_dec_ref(v_inst_1179_);
v___f_1181_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1182_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1183_ = lean_apply_4(v_map_1180_, lean_box(0), lean_box(0), v___f_1182_, v_inst_1178_);
v___x_1184_ = lean_apply_4(v_map_1180_, lean_box(0), lean_box(0), v___f_1181_, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object* v_m_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_){
_start:
{
lean_object* v_map_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_map_1188_ = lean_ctor_get(v_inst_1187_, 0);
lean_inc_n(v_map_1188_, 2);
lean_dec_ref(v_inst_1187_);
v___f_1189_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1190_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1191_ = lean_apply_4(v_map_1188_, lean_box(0), lean_box(0), v___f_1190_, v_inst_1186_);
v___x_1192_ = lean_apply_4(v_map_1188_, lean_box(0), lean_box(0), v___f_1189_, v___x_1191_);
return v___x_1192_;
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

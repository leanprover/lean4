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
uint8_t v_noCache_661_; 
v_noCache_661_ = lean_ctor_get_uint8(v_x_660_, sizeof(void*)*20);
if (v_noCache_661_ == 0)
{
uint8_t v___x_662_; 
v___x_662_ = 1;
return v___x_662_;
}
else
{
uint8_t v___x_663_; 
v___x_663_ = 0;
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg___lam__0___boxed(lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Lake_getTryCache___redArg___lam__0(v_x_664_);
lean_dec_ref(v_x_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg(lean_object* v_inst_668_, lean_object* v_inst_669_){
_start:
{
lean_object* v_map_670_; lean_object* v___f_671_; lean_object* v___x_672_; 
v_map_670_ = lean_ctor_get(v_inst_669_, 0);
lean_inc(v_map_670_);
lean_dec_ref(v_inst_669_);
v___f_671_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_672_ = lean_apply_4(v_map_670_, lean_box(0), lean_box(0), v___f_671_, v_inst_668_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object* v_m_673_, lean_object* v_inst_674_, lean_object* v_inst_675_, lean_object* v_inst_676_){
_start:
{
lean_object* v_map_677_; lean_object* v___f_678_; lean_object* v___x_679_; 
v_map_677_ = lean_ctor_get(v_inst_675_, 0);
lean_inc(v_map_677_);
lean_dec_ref(v_inst_675_);
v___f_678_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_679_ = lean_apply_4(v_map_677_, lean_box(0), lean_box(0), v___f_678_, v_inst_674_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___boxed(lean_object* v_m_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lake_getTryCache(v_m_680_, v_inst_681_, v_inst_682_, v_inst_683_);
lean_dec(v_inst_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0(lean_object* v_x_685_){
_start:
{
lean_object* v_pkgUrlMap_686_; 
v_pkgUrlMap_686_ = lean_ctor_get(v_x_685_, 5);
lean_inc(v_pkgUrlMap_686_);
return v_pkgUrlMap_686_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0___boxed(lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lake_getPkgUrlMap___redArg___lam__0(v_x_687_);
lean_dec_ref(v_x_687_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg(lean_object* v_inst_690_, lean_object* v_inst_691_){
_start:
{
lean_object* v_map_692_; lean_object* v___f_693_; lean_object* v___x_694_; 
v_map_692_ = lean_ctor_get(v_inst_691_, 0);
lean_inc(v_map_692_);
lean_dec_ref(v_inst_691_);
v___f_693_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_694_ = lean_apply_4(v_map_692_, lean_box(0), lean_box(0), v___f_693_, v_inst_690_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object* v_m_695_, lean_object* v_inst_696_, lean_object* v_inst_697_){
_start:
{
lean_object* v_map_698_; lean_object* v___f_699_; lean_object* v___x_700_; 
v_map_698_ = lean_ctor_get(v_inst_697_, 0);
lean_inc(v_map_698_);
lean_dec_ref(v_inst_697_);
v___f_699_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_700_ = lean_apply_4(v_map_698_, lean_box(0), lean_box(0), v___f_699_, v_inst_696_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0(lean_object* v_x_701_){
_start:
{
lean_object* v_toolchain_702_; 
v_toolchain_702_ = lean_ctor_get(v_x_701_, 19);
lean_inc_ref(v_toolchain_702_);
return v_toolchain_702_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0___boxed(lean_object* v_x_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lake_getElanToolchain___redArg___lam__0(v_x_703_);
lean_dec_ref(v_x_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg(lean_object* v_inst_706_, lean_object* v_inst_707_){
_start:
{
lean_object* v_map_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v_map_708_ = lean_ctor_get(v_inst_707_, 0);
lean_inc(v_map_708_);
lean_dec_ref(v_inst_707_);
v___f_709_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_710_ = lean_apply_4(v_map_708_, lean_box(0), lean_box(0), v___f_709_, v_inst_706_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object* v_m_711_, lean_object* v_inst_712_, lean_object* v_inst_713_){
_start:
{
lean_object* v_map_714_; lean_object* v___f_715_; lean_object* v___x_716_; 
v_map_714_ = lean_ctor_get(v_inst_713_, 0);
lean_inc(v_map_714_);
lean_dec_ref(v_inst_713_);
v___f_715_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_716_ = lean_apply_4(v_map_714_, lean_box(0), lean_box(0), v___f_715_, v_inst_712_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___redArg(lean_object* v_inst_718_, lean_object* v_inst_719_){
_start:
{
lean_object* v_map_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
v_map_720_ = lean_ctor_get(v_inst_719_, 0);
lean_inc(v_map_720_);
lean_dec_ref(v_inst_719_);
v___f_721_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_722_ = lean_apply_4(v_map_720_, lean_box(0), lean_box(0), v___f_721_, v_inst_718_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object* v_m_723_, lean_object* v_inst_724_, lean_object* v_inst_725_){
_start:
{
lean_object* v_map_726_; lean_object* v___f_727_; lean_object* v___x_728_; 
v_map_726_ = lean_ctor_get(v_inst_725_, 0);
lean_inc(v_map_726_);
lean_dec_ref(v_inst_725_);
v___f_727_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_728_ = lean_apply_4(v_map_726_, lean_box(0), lean_box(0), v___f_727_, v_inst_724_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___redArg(lean_object* v_inst_730_, lean_object* v_inst_731_){
_start:
{
lean_object* v_map_732_; lean_object* v___f_733_; lean_object* v___x_734_; 
v_map_732_ = lean_ctor_get(v_inst_731_, 0);
lean_inc(v_map_732_);
lean_dec_ref(v_inst_731_);
v___f_733_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_734_ = lean_apply_4(v_map_732_, lean_box(0), lean_box(0), v___f_733_, v_inst_730_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object* v_m_735_, lean_object* v_inst_736_, lean_object* v_inst_737_){
_start:
{
lean_object* v_map_738_; lean_object* v___f_739_; lean_object* v___x_740_; 
v_map_738_ = lean_ctor_get(v_inst_737_, 0);
lean_inc(v_map_738_);
lean_dec_ref(v_inst_737_);
v___f_739_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_740_ = lean_apply_4(v_map_738_, lean_box(0), lean_box(0), v___f_739_, v_inst_736_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___redArg(lean_object* v_inst_742_, lean_object* v_inst_743_){
_start:
{
lean_object* v_map_744_; lean_object* v___f_745_; lean_object* v___x_746_; 
v_map_744_ = lean_ctor_get(v_inst_743_, 0);
lean_inc(v_map_744_);
lean_dec_ref(v_inst_743_);
v___f_745_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_746_ = lean_apply_4(v_map_744_, lean_box(0), lean_box(0), v___f_745_, v_inst_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object* v_m_747_, lean_object* v_inst_748_, lean_object* v_inst_749_){
_start:
{
lean_object* v_map_750_; lean_object* v___f_751_; lean_object* v___x_752_; 
v_map_750_ = lean_ctor_get(v_inst_749_, 0);
lean_inc(v_map_750_);
lean_dec_ref(v_inst_749_);
v___f_751_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_752_ = lean_apply_4(v_map_750_, lean_box(0), lean_box(0), v___f_751_, v_inst_748_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0(lean_object* v_x_753_){
_start:
{
lean_object* v_elan_x3f_754_; 
v_elan_x3f_754_ = lean_ctor_get(v_x_753_, 2);
lean_inc(v_elan_x3f_754_);
return v_elan_x3f_754_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0___boxed(lean_object* v_x_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lake_getElanInstall_x3f___redArg___lam__0(v_x_755_);
lean_dec_ref(v_x_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg(lean_object* v_inst_758_, lean_object* v_inst_759_){
_start:
{
lean_object* v_map_760_; lean_object* v___f_761_; lean_object* v___x_762_; 
v_map_760_ = lean_ctor_get(v_inst_759_, 0);
lean_inc(v_map_760_);
lean_dec_ref(v_inst_759_);
v___f_761_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_762_ = lean_apply_4(v_map_760_, lean_box(0), lean_box(0), v___f_761_, v_inst_758_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object* v_m_763_, lean_object* v_inst_764_, lean_object* v_inst_765_){
_start:
{
lean_object* v_map_766_; lean_object* v___f_767_; lean_object* v___x_768_; 
v_map_766_ = lean_ctor_get(v_inst_765_, 0);
lean_inc(v_map_766_);
lean_dec_ref(v_inst_765_);
v___f_767_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_768_ = lean_apply_4(v_map_766_, lean_box(0), lean_box(0), v___f_767_, v_inst_764_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg___lam__0(lean_object* v_x_769_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
lean_object* v___x_770_; 
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_779_; 
v_val_771_ = lean_ctor_get(v_x_769_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_779_ == 0)
{
v___x_773_ = v_x_769_;
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v_x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_home_775_; lean_object* v___x_777_; 
v_home_775_ = lean_ctor_get(v_val_771_, 0);
lean_inc_ref(v_home_775_);
lean_dec(v_val_771_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_home_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_home_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg(lean_object* v_inst_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v_map_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_map_783_ = lean_ctor_get(v_inst_782_, 0);
lean_inc_n(v_map_783_, 2);
lean_dec_ref(v_inst_782_);
v___f_784_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_785_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_786_ = lean_apply_4(v_map_783_, lean_box(0), lean_box(0), v___f_785_, v_inst_781_);
v___x_787_ = lean_apply_4(v_map_783_, lean_box(0), lean_box(0), v___f_784_, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object* v_m_788_, lean_object* v_inst_789_, lean_object* v_inst_790_){
_start:
{
lean_object* v_map_791_; lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_map_791_ = lean_ctor_get(v_inst_790_, 0);
lean_inc_n(v_map_791_, 2);
lean_dec_ref(v_inst_790_);
v___f_792_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_793_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_794_ = lean_apply_4(v_map_791_, lean_box(0), lean_box(0), v___f_793_, v_inst_789_);
v___x_795_ = lean_apply_4(v_map_791_, lean_box(0), lean_box(0), v___f_792_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg___lam__0(lean_object* v_x_796_){
_start:
{
if (lean_obj_tag(v_x_796_) == 0)
{
lean_object* v___x_797_; 
v___x_797_ = lean_box(0);
return v___x_797_;
}
else
{
lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_val_798_ = lean_ctor_get(v_x_796_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v_x_796_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_dec(v_x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_elan_802_; lean_object* v___x_804_; 
v_elan_802_ = lean_ctor_get(v_val_798_, 1);
lean_inc_ref(v_elan_802_);
lean_dec(v_val_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_elan_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_elan_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg(lean_object* v_inst_808_, lean_object* v_inst_809_){
_start:
{
lean_object* v_map_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_map_810_ = lean_ctor_get(v_inst_809_, 0);
lean_inc_n(v_map_810_, 2);
lean_dec_ref(v_inst_809_);
v___f_811_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_812_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_813_ = lean_apply_4(v_map_810_, lean_box(0), lean_box(0), v___f_812_, v_inst_808_);
v___x_814_ = lean_apply_4(v_map_810_, lean_box(0), lean_box(0), v___f_811_, v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v_map_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_map_818_ = lean_ctor_get(v_inst_817_, 0);
lean_inc_n(v_map_818_, 2);
lean_dec_ref(v_inst_817_);
v___f_819_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_820_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_821_ = lean_apply_4(v_map_818_, lean_box(0), lean_box(0), v___f_820_, v_inst_816_);
v___x_822_ = lean_apply_4(v_map_818_, lean_box(0), lean_box(0), v___f_819_, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0(lean_object* v_x_823_){
_start:
{
lean_object* v_lean_824_; 
v_lean_824_ = lean_ctor_get(v_x_823_, 1);
lean_inc_ref(v_lean_824_);
return v_lean_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0___boxed(lean_object* v_x_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lake_getLeanInstall___redArg___lam__0(v_x_825_);
lean_dec_ref(v_x_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg(lean_object* v_inst_828_, lean_object* v_inst_829_){
_start:
{
lean_object* v_map_830_; lean_object* v___f_831_; lean_object* v___x_832_; 
v_map_830_ = lean_ctor_get(v_inst_829_, 0);
lean_inc(v_map_830_);
lean_dec_ref(v_inst_829_);
v___f_831_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_832_ = lean_apply_4(v_map_830_, lean_box(0), lean_box(0), v___f_831_, v_inst_828_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object* v_m_833_, lean_object* v_inst_834_, lean_object* v_inst_835_){
_start:
{
lean_object* v_map_836_; lean_object* v___f_837_; lean_object* v___x_838_; 
v_map_836_ = lean_ctor_get(v_inst_835_, 0);
lean_inc(v_map_836_);
lean_dec_ref(v_inst_835_);
v___f_837_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_838_ = lean_apply_4(v_map_836_, lean_box(0), lean_box(0), v___f_837_, v_inst_834_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0(lean_object* v_x_839_){
_start:
{
lean_object* v_sysroot_840_; 
v_sysroot_840_ = lean_ctor_get(v_x_839_, 0);
lean_inc_ref(v_sysroot_840_);
return v_sysroot_840_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0___boxed(lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_getLeanSysroot___redArg___lam__0(v_x_841_);
lean_dec_ref(v_x_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg(lean_object* v_inst_844_, lean_object* v_inst_845_){
_start:
{
lean_object* v_map_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_map_846_ = lean_ctor_get(v_inst_845_, 0);
lean_inc_n(v_map_846_, 2);
lean_dec_ref(v_inst_845_);
v___f_847_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_848_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_849_ = lean_apply_4(v_map_846_, lean_box(0), lean_box(0), v___f_848_, v_inst_844_);
v___x_850_ = lean_apply_4(v_map_846_, lean_box(0), lean_box(0), v___f_847_, v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object* v_m_851_, lean_object* v_inst_852_, lean_object* v_inst_853_){
_start:
{
lean_object* v_map_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_map_854_ = lean_ctor_get(v_inst_853_, 0);
lean_inc_n(v_map_854_, 2);
lean_dec_ref(v_inst_853_);
v___f_855_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_856_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_857_ = lean_apply_4(v_map_854_, lean_box(0), lean_box(0), v___f_856_, v_inst_852_);
v___x_858_ = lean_apply_4(v_map_854_, lean_box(0), lean_box(0), v___f_855_, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0(lean_object* v_x_859_){
_start:
{
lean_object* v_srcDir_860_; 
v_srcDir_860_ = lean_ctor_get(v_x_859_, 2);
lean_inc_ref(v_srcDir_860_);
return v_srcDir_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0___boxed(lean_object* v_x_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lake_getLeanSrcDir___redArg___lam__0(v_x_861_);
lean_dec_ref(v_x_861_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg(lean_object* v_inst_864_, lean_object* v_inst_865_){
_start:
{
lean_object* v_map_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_map_866_ = lean_ctor_get(v_inst_865_, 0);
lean_inc_n(v_map_866_, 2);
lean_dec_ref(v_inst_865_);
v___f_867_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_868_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_869_ = lean_apply_4(v_map_866_, lean_box(0), lean_box(0), v___f_868_, v_inst_864_);
v___x_870_ = lean_apply_4(v_map_866_, lean_box(0), lean_box(0), v___f_867_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object* v_m_871_, lean_object* v_inst_872_, lean_object* v_inst_873_){
_start:
{
lean_object* v_map_874_; lean_object* v___f_875_; lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_map_874_ = lean_ctor_get(v_inst_873_, 0);
lean_inc_n(v_map_874_, 2);
lean_dec_ref(v_inst_873_);
v___f_875_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_876_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_877_ = lean_apply_4(v_map_874_, lean_box(0), lean_box(0), v___f_876_, v_inst_872_);
v___x_878_ = lean_apply_4(v_map_874_, lean_box(0), lean_box(0), v___f_875_, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0(lean_object* v_x_879_){
_start:
{
lean_object* v_leanLibDir_880_; 
v_leanLibDir_880_ = lean_ctor_get(v_x_879_, 3);
lean_inc_ref(v_leanLibDir_880_);
return v_leanLibDir_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0___boxed(lean_object* v_x_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lake_getLeanLibDir___redArg___lam__0(v_x_881_);
lean_dec_ref(v_x_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg(lean_object* v_inst_884_, lean_object* v_inst_885_){
_start:
{
lean_object* v_map_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_map_886_ = lean_ctor_get(v_inst_885_, 0);
lean_inc_n(v_map_886_, 2);
lean_dec_ref(v_inst_885_);
v___f_887_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_888_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_889_ = lean_apply_4(v_map_886_, lean_box(0), lean_box(0), v___f_888_, v_inst_884_);
v___x_890_ = lean_apply_4(v_map_886_, lean_box(0), lean_box(0), v___f_887_, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object* v_m_891_, lean_object* v_inst_892_, lean_object* v_inst_893_){
_start:
{
lean_object* v_map_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_map_894_ = lean_ctor_get(v_inst_893_, 0);
lean_inc_n(v_map_894_, 2);
lean_dec_ref(v_inst_893_);
v___f_895_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_896_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_897_ = lean_apply_4(v_map_894_, lean_box(0), lean_box(0), v___f_896_, v_inst_892_);
v___x_898_ = lean_apply_4(v_map_894_, lean_box(0), lean_box(0), v___f_895_, v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0(lean_object* v_x_899_){
_start:
{
lean_object* v_includeDir_900_; 
v_includeDir_900_ = lean_ctor_get(v_x_899_, 4);
lean_inc_ref(v_includeDir_900_);
return v_includeDir_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0___boxed(lean_object* v_x_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lake_getLeanIncludeDir___redArg___lam__0(v_x_901_);
lean_dec_ref(v_x_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg(lean_object* v_inst_904_, lean_object* v_inst_905_){
_start:
{
lean_object* v_map_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_map_906_ = lean_ctor_get(v_inst_905_, 0);
lean_inc_n(v_map_906_, 2);
lean_dec_ref(v_inst_905_);
v___f_907_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_908_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_909_ = lean_apply_4(v_map_906_, lean_box(0), lean_box(0), v___f_908_, v_inst_904_);
v___x_910_ = lean_apply_4(v_map_906_, lean_box(0), lean_box(0), v___f_907_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object* v_m_911_, lean_object* v_inst_912_, lean_object* v_inst_913_){
_start:
{
lean_object* v_map_914_; lean_object* v___f_915_; lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_map_914_ = lean_ctor_get(v_inst_913_, 0);
lean_inc_n(v_map_914_, 2);
lean_dec_ref(v_inst_913_);
v___f_915_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_916_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_917_ = lean_apply_4(v_map_914_, lean_box(0), lean_box(0), v___f_916_, v_inst_912_);
v___x_918_ = lean_apply_4(v_map_914_, lean_box(0), lean_box(0), v___f_915_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0(lean_object* v_x_919_){
_start:
{
lean_object* v_systemLibDir_920_; 
v_systemLibDir_920_ = lean_ctor_get(v_x_919_, 5);
lean_inc_ref(v_systemLibDir_920_);
return v_systemLibDir_920_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed(lean_object* v_x_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lake_getLeanSystemLibDir___redArg___lam__0(v_x_921_);
lean_dec_ref(v_x_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg(lean_object* v_inst_924_, lean_object* v_inst_925_){
_start:
{
lean_object* v_map_926_; lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_map_926_ = lean_ctor_get(v_inst_925_, 0);
lean_inc_n(v_map_926_, 2);
lean_dec_ref(v_inst_925_);
v___f_927_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_928_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_929_ = lean_apply_4(v_map_926_, lean_box(0), lean_box(0), v___f_928_, v_inst_924_);
v___x_930_ = lean_apply_4(v_map_926_, lean_box(0), lean_box(0), v___f_927_, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object* v_m_931_, lean_object* v_inst_932_, lean_object* v_inst_933_){
_start:
{
lean_object* v_map_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_map_934_ = lean_ctor_get(v_inst_933_, 0);
lean_inc_n(v_map_934_, 2);
lean_dec_ref(v_inst_933_);
v___f_935_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_936_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_937_ = lean_apply_4(v_map_934_, lean_box(0), lean_box(0), v___f_936_, v_inst_932_);
v___x_938_ = lean_apply_4(v_map_934_, lean_box(0), lean_box(0), v___f_935_, v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0(lean_object* v_x_939_){
_start:
{
lean_object* v_lean_940_; 
v_lean_940_ = lean_ctor_get(v_x_939_, 7);
lean_inc_ref(v_lean_940_);
return v_lean_940_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0___boxed(lean_object* v_x_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lake_getLean___redArg___lam__0(v_x_941_);
lean_dec_ref(v_x_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg(lean_object* v_inst_944_, lean_object* v_inst_945_){
_start:
{
lean_object* v_map_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_map_946_ = lean_ctor_get(v_inst_945_, 0);
lean_inc_n(v_map_946_, 2);
lean_dec_ref(v_inst_945_);
v___f_947_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_948_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_949_ = lean_apply_4(v_map_946_, lean_box(0), lean_box(0), v___f_948_, v_inst_944_);
v___x_950_ = lean_apply_4(v_map_946_, lean_box(0), lean_box(0), v___f_947_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object* v_m_951_, lean_object* v_inst_952_, lean_object* v_inst_953_){
_start:
{
lean_object* v_map_954_; lean_object* v___f_955_; lean_object* v___f_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_map_954_ = lean_ctor_get(v_inst_953_, 0);
lean_inc_n(v_map_954_, 2);
lean_dec_ref(v_inst_953_);
v___f_955_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_956_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_957_ = lean_apply_4(v_map_954_, lean_box(0), lean_box(0), v___f_956_, v_inst_952_);
v___x_958_ = lean_apply_4(v_map_954_, lean_box(0), lean_box(0), v___f_955_, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0(lean_object* v_x_959_){
_start:
{
lean_object* v_leanir_960_; 
v_leanir_960_ = lean_ctor_get(v_x_959_, 8);
lean_inc_ref(v_leanir_960_);
return v_leanir_960_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0___boxed(lean_object* v_x_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lake_getLeanir___redArg___lam__0(v_x_961_);
lean_dec_ref(v_x_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg(lean_object* v_inst_964_, lean_object* v_inst_965_){
_start:
{
lean_object* v_map_966_; lean_object* v___f_967_; lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_map_966_ = lean_ctor_get(v_inst_965_, 0);
lean_inc_n(v_map_966_, 2);
lean_dec_ref(v_inst_965_);
v___f_967_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_968_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_969_ = lean_apply_4(v_map_966_, lean_box(0), lean_box(0), v___f_968_, v_inst_964_);
v___x_970_ = lean_apply_4(v_map_966_, lean_box(0), lean_box(0), v___f_967_, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir(lean_object* v_m_971_, lean_object* v_inst_972_, lean_object* v_inst_973_){
_start:
{
lean_object* v_map_974_; lean_object* v___f_975_; lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_map_974_ = lean_ctor_get(v_inst_973_, 0);
lean_inc_n(v_map_974_, 2);
lean_dec_ref(v_inst_973_);
v___f_975_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_976_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_977_ = lean_apply_4(v_map_974_, lean_box(0), lean_box(0), v___f_976_, v_inst_972_);
v___x_978_ = lean_apply_4(v_map_974_, lean_box(0), lean_box(0), v___f_975_, v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0(lean_object* v_x_979_){
_start:
{
lean_object* v_leanc_980_; 
v_leanc_980_ = lean_ctor_get(v_x_979_, 9);
lean_inc_ref(v_leanc_980_);
return v_leanc_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0___boxed(lean_object* v_x_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lake_getLeanc___redArg___lam__0(v_x_981_);
lean_dec_ref(v_x_981_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg(lean_object* v_inst_984_, lean_object* v_inst_985_){
_start:
{
lean_object* v_map_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_map_986_ = lean_ctor_get(v_inst_985_, 0);
lean_inc_n(v_map_986_, 2);
lean_dec_ref(v_inst_985_);
v___f_987_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_988_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_989_ = lean_apply_4(v_map_986_, lean_box(0), lean_box(0), v___f_988_, v_inst_984_);
v___x_990_ = lean_apply_4(v_map_986_, lean_box(0), lean_box(0), v___f_987_, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object* v_m_991_, lean_object* v_inst_992_, lean_object* v_inst_993_){
_start:
{
lean_object* v_map_994_; lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_map_994_ = lean_ctor_get(v_inst_993_, 0);
lean_inc_n(v_map_994_, 2);
lean_dec_ref(v_inst_993_);
v___f_995_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_996_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_997_ = lean_apply_4(v_map_994_, lean_box(0), lean_box(0), v___f_996_, v_inst_992_);
v___x_998_ = lean_apply_4(v_map_994_, lean_box(0), lean_box(0), v___f_995_, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0(lean_object* v_x_999_){
_start:
{
lean_object* v_leantar_1000_; 
v_leantar_1000_ = lean_ctor_get(v_x_999_, 10);
lean_inc_ref(v_leantar_1000_);
return v_leantar_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0___boxed(lean_object* v_x_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lake_getLeantar___redArg___lam__0(v_x_1001_);
lean_dec_ref(v_x_1001_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg(lean_object* v_inst_1004_, lean_object* v_inst_1005_){
_start:
{
lean_object* v_map_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_map_1006_ = lean_ctor_get(v_inst_1005_, 0);
lean_inc_n(v_map_1006_, 2);
lean_dec_ref(v_inst_1005_);
v___f_1007_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1008_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1009_ = lean_apply_4(v_map_1006_, lean_box(0), lean_box(0), v___f_1008_, v_inst_1004_);
v___x_1010_ = lean_apply_4(v_map_1006_, lean_box(0), lean_box(0), v___f_1007_, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar(lean_object* v_m_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_){
_start:
{
lean_object* v_map_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_map_1014_ = lean_ctor_get(v_inst_1013_, 0);
lean_inc_n(v_map_1014_, 2);
lean_dec_ref(v_inst_1013_);
v___f_1015_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1016_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1017_ = lean_apply_4(v_map_1014_, lean_box(0), lean_box(0), v___f_1016_, v_inst_1012_);
v___x_1018_ = lean_apply_4(v_map_1014_, lean_box(0), lean_box(0), v___f_1015_, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0(lean_object* v_x_1019_){
_start:
{
lean_object* v_sharedLib_1020_; 
v_sharedLib_1020_ = lean_ctor_get(v_x_1019_, 11);
lean_inc_ref(v_sharedLib_1020_);
return v_sharedLib_1020_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0___boxed(lean_object* v_x_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lake_getLeanSharedLib___redArg___lam__0(v_x_1021_);
lean_dec_ref(v_x_1021_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg(lean_object* v_inst_1024_, lean_object* v_inst_1025_){
_start:
{
lean_object* v_map_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_map_1026_ = lean_ctor_get(v_inst_1025_, 0);
lean_inc_n(v_map_1026_, 2);
lean_dec_ref(v_inst_1025_);
v___f_1027_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1028_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1029_ = lean_apply_4(v_map_1026_, lean_box(0), lean_box(0), v___f_1028_, v_inst_1024_);
v___x_1030_ = lean_apply_4(v_map_1026_, lean_box(0), lean_box(0), v___f_1027_, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object* v_m_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_){
_start:
{
lean_object* v_map_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_map_1034_ = lean_ctor_get(v_inst_1033_, 0);
lean_inc_n(v_map_1034_, 2);
lean_dec_ref(v_inst_1033_);
v___f_1035_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1036_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1037_ = lean_apply_4(v_map_1034_, lean_box(0), lean_box(0), v___f_1036_, v_inst_1032_);
v___x_1038_ = lean_apply_4(v_map_1034_, lean_box(0), lean_box(0), v___f_1035_, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0(lean_object* v_x_1039_){
_start:
{
lean_object* v_ar_1040_; 
v_ar_1040_ = lean_ctor_get(v_x_1039_, 13);
lean_inc_ref(v_ar_1040_);
return v_ar_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0___boxed(lean_object* v_x_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lake_getLeanAr___redArg___lam__0(v_x_1041_);
lean_dec_ref(v_x_1041_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg(lean_object* v_inst_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v_map_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_map_1046_ = lean_ctor_get(v_inst_1045_, 0);
lean_inc_n(v_map_1046_, 2);
lean_dec_ref(v_inst_1045_);
v___f_1047_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1048_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1049_ = lean_apply_4(v_map_1046_, lean_box(0), lean_box(0), v___f_1048_, v_inst_1044_);
v___x_1050_ = lean_apply_4(v_map_1046_, lean_box(0), lean_box(0), v___f_1047_, v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object* v_m_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_){
_start:
{
lean_object* v_map_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_map_1054_ = lean_ctor_get(v_inst_1053_, 0);
lean_inc_n(v_map_1054_, 2);
lean_dec_ref(v_inst_1053_);
v___f_1055_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1056_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1057_ = lean_apply_4(v_map_1054_, lean_box(0), lean_box(0), v___f_1056_, v_inst_1052_);
v___x_1058_ = lean_apply_4(v_map_1054_, lean_box(0), lean_box(0), v___f_1055_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0(lean_object* v_x_1059_){
_start:
{
lean_object* v_cc_1060_; 
v_cc_1060_ = lean_ctor_get(v_x_1059_, 14);
lean_inc_ref(v_cc_1060_);
return v_cc_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0___boxed(lean_object* v_x_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lake_getLeanCc___redArg___lam__0(v_x_1061_);
lean_dec_ref(v_x_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg(lean_object* v_inst_1064_, lean_object* v_inst_1065_){
_start:
{
lean_object* v_map_1066_; lean_object* v___f_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_map_1066_ = lean_ctor_get(v_inst_1065_, 0);
lean_inc_n(v_map_1066_, 2);
lean_dec_ref(v_inst_1065_);
v___f_1067_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1068_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1069_ = lean_apply_4(v_map_1066_, lean_box(0), lean_box(0), v___f_1068_, v_inst_1064_);
v___x_1070_ = lean_apply_4(v_map_1066_, lean_box(0), lean_box(0), v___f_1067_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object* v_m_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_){
_start:
{
lean_object* v_map_1074_; lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_map_1074_ = lean_ctor_get(v_inst_1073_, 0);
lean_inc_n(v_map_1074_, 2);
lean_dec_ref(v_inst_1073_);
v___f_1075_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1076_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1077_ = lean_apply_4(v_map_1074_, lean_box(0), lean_box(0), v___f_1076_, v_inst_1072_);
v___x_1078_ = lean_apply_4(v_map_1074_, lean_box(0), lean_box(0), v___f_1075_, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___redArg(lean_object* v_inst_1080_, lean_object* v_inst_1081_){
_start:
{
lean_object* v_map_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_map_1082_ = lean_ctor_get(v_inst_1081_, 0);
lean_inc_n(v_map_1082_, 2);
lean_dec_ref(v_inst_1081_);
v___f_1083_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1084_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1085_ = lean_apply_4(v_map_1082_, lean_box(0), lean_box(0), v___f_1084_, v_inst_1080_);
v___x_1086_ = lean_apply_4(v_map_1082_, lean_box(0), lean_box(0), v___f_1083_, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object* v_m_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_){
_start:
{
lean_object* v_map_1090_; lean_object* v___f_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v_map_1090_ = lean_ctor_get(v_inst_1089_, 0);
lean_inc_n(v_map_1090_, 2);
lean_dec_ref(v_inst_1089_);
v___f_1091_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1092_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1093_ = lean_apply_4(v_map_1090_, lean_box(0), lean_box(0), v___f_1092_, v_inst_1088_);
v___x_1094_ = lean_apply_4(v_map_1090_, lean_box(0), lean_box(0), v___f_1091_, v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0(lean_object* v_x_1095_){
_start:
{
lean_object* v_ccLinkSharedFlags_1096_; 
v_ccLinkSharedFlags_1096_ = lean_ctor_get(v_x_1095_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1096_);
return v_ccLinkSharedFlags_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed(lean_object* v_x_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lake_getLeanLinkSharedFlags___redArg___lam__0(v_x_1097_);
lean_dec_ref(v_x_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg(lean_object* v_inst_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v_map_1102_; lean_object* v___f_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_map_1102_ = lean_ctor_get(v_inst_1101_, 0);
lean_inc_n(v_map_1102_, 2);
lean_dec_ref(v_inst_1101_);
v___f_1103_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1104_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1105_ = lean_apply_4(v_map_1102_, lean_box(0), lean_box(0), v___f_1104_, v_inst_1100_);
v___x_1106_ = lean_apply_4(v_map_1102_, lean_box(0), lean_box(0), v___f_1103_, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags(lean_object* v_m_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_){
_start:
{
lean_object* v_map_1110_; lean_object* v___f_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_map_1110_ = lean_ctor_get(v_inst_1109_, 0);
lean_inc_n(v_map_1110_, 2);
lean_dec_ref(v_inst_1109_);
v___f_1111_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1112_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1113_ = lean_apply_4(v_map_1110_, lean_box(0), lean_box(0), v___f_1112_, v_inst_1108_);
v___x_1114_ = lean_apply_4(v_map_1110_, lean_box(0), lean_box(0), v___f_1111_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0(lean_object* v_x_1115_){
_start:
{
lean_object* v_lake_1116_; 
v_lake_1116_ = lean_ctor_get(v_x_1115_, 0);
lean_inc_ref(v_lake_1116_);
return v_lake_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0___boxed(lean_object* v_x_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lake_getLakeInstall___redArg___lam__0(v_x_1117_);
lean_dec_ref(v_x_1117_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg(lean_object* v_inst_1120_, lean_object* v_inst_1121_){
_start:
{
lean_object* v_map_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; 
v_map_1122_ = lean_ctor_get(v_inst_1121_, 0);
lean_inc(v_map_1122_);
lean_dec_ref(v_inst_1121_);
v___f_1123_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1124_ = lean_apply_4(v_map_1122_, lean_box(0), lean_box(0), v___f_1123_, v_inst_1120_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object* v_m_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_){
_start:
{
lean_object* v_map_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; 
v_map_1128_ = lean_ctor_get(v_inst_1127_, 0);
lean_inc(v_map_1128_);
lean_dec_ref(v_inst_1127_);
v___f_1129_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1130_ = lean_apply_4(v_map_1128_, lean_box(0), lean_box(0), v___f_1129_, v_inst_1126_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0(lean_object* v_x_1131_){
_start:
{
lean_object* v_home_1132_; 
v_home_1132_ = lean_ctor_get(v_x_1131_, 0);
lean_inc_ref(v_home_1132_);
return v_home_1132_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0___boxed(lean_object* v_x_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lake_getLakeHome___redArg___lam__0(v_x_1133_);
lean_dec_ref(v_x_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg(lean_object* v_inst_1136_, lean_object* v_inst_1137_){
_start:
{
lean_object* v_map_1138_; lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_map_1138_ = lean_ctor_get(v_inst_1137_, 0);
lean_inc_n(v_map_1138_, 2);
lean_dec_ref(v_inst_1137_);
v___f_1139_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1140_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1141_ = lean_apply_4(v_map_1138_, lean_box(0), lean_box(0), v___f_1140_, v_inst_1136_);
v___x_1142_ = lean_apply_4(v_map_1138_, lean_box(0), lean_box(0), v___f_1139_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object* v_m_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_){
_start:
{
lean_object* v_map_1146_; lean_object* v___f_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_map_1146_ = lean_ctor_get(v_inst_1145_, 0);
lean_inc_n(v_map_1146_, 2);
lean_dec_ref(v_inst_1145_);
v___f_1147_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1148_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1149_ = lean_apply_4(v_map_1146_, lean_box(0), lean_box(0), v___f_1148_, v_inst_1144_);
v___x_1150_ = lean_apply_4(v_map_1146_, lean_box(0), lean_box(0), v___f_1147_, v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0(lean_object* v_x_1151_){
_start:
{
lean_object* v_srcDir_1152_; 
v_srcDir_1152_ = lean_ctor_get(v_x_1151_, 1);
lean_inc_ref(v_srcDir_1152_);
return v_srcDir_1152_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0___boxed(lean_object* v_x_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lake_getLakeSrcDir___redArg___lam__0(v_x_1153_);
lean_dec_ref(v_x_1153_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg(lean_object* v_inst_1156_, lean_object* v_inst_1157_){
_start:
{
lean_object* v_map_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_map_1158_ = lean_ctor_get(v_inst_1157_, 0);
lean_inc_n(v_map_1158_, 2);
lean_dec_ref(v_inst_1157_);
v___f_1159_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1160_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1161_ = lean_apply_4(v_map_1158_, lean_box(0), lean_box(0), v___f_1160_, v_inst_1156_);
v___x_1162_ = lean_apply_4(v_map_1158_, lean_box(0), lean_box(0), v___f_1159_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object* v_m_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_){
_start:
{
lean_object* v_map_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_map_1166_ = lean_ctor_get(v_inst_1165_, 0);
lean_inc_n(v_map_1166_, 2);
lean_dec_ref(v_inst_1165_);
v___f_1167_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1168_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1169_ = lean_apply_4(v_map_1166_, lean_box(0), lean_box(0), v___f_1168_, v_inst_1164_);
v___x_1170_ = lean_apply_4(v_map_1166_, lean_box(0), lean_box(0), v___f_1167_, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0(lean_object* v_x_1171_){
_start:
{
lean_object* v_libDir_1172_; 
v_libDir_1172_ = lean_ctor_get(v_x_1171_, 3);
lean_inc_ref(v_libDir_1172_);
return v_libDir_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0___boxed(lean_object* v_x_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lake_getLakeLibDir___redArg___lam__0(v_x_1173_);
lean_dec_ref(v_x_1173_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg(lean_object* v_inst_1176_, lean_object* v_inst_1177_){
_start:
{
lean_object* v_map_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_map_1178_ = lean_ctor_get(v_inst_1177_, 0);
lean_inc_n(v_map_1178_, 2);
lean_dec_ref(v_inst_1177_);
v___f_1179_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1180_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1181_ = lean_apply_4(v_map_1178_, lean_box(0), lean_box(0), v___f_1180_, v_inst_1176_);
v___x_1182_ = lean_apply_4(v_map_1178_, lean_box(0), lean_box(0), v___f_1179_, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object* v_m_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_){
_start:
{
lean_object* v_map_1186_; lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_map_1186_ = lean_ctor_get(v_inst_1185_, 0);
lean_inc_n(v_map_1186_, 2);
lean_dec_ref(v_inst_1185_);
v___f_1187_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1188_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1189_ = lean_apply_4(v_map_1186_, lean_box(0), lean_box(0), v___f_1188_, v_inst_1184_);
v___x_1190_ = lean_apply_4(v_map_1186_, lean_box(0), lean_box(0), v___f_1187_, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0(lean_object* v_x_1191_){
_start:
{
lean_object* v_lake_1192_; 
v_lake_1192_ = lean_ctor_get(v_x_1191_, 5);
lean_inc_ref(v_lake_1192_);
return v_lake_1192_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0___boxed(lean_object* v_x_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lake_getLake___redArg___lam__0(v_x_1193_);
lean_dec_ref(v_x_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg(lean_object* v_inst_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v_map_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_map_1198_ = lean_ctor_get(v_inst_1197_, 0);
lean_inc_n(v_map_1198_, 2);
lean_dec_ref(v_inst_1197_);
v___f_1199_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1200_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1201_ = lean_apply_4(v_map_1198_, lean_box(0), lean_box(0), v___f_1200_, v_inst_1196_);
v___x_1202_ = lean_apply_4(v_map_1198_, lean_box(0), lean_box(0), v___f_1199_, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object* v_m_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_){
_start:
{
lean_object* v_map_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_map_1206_ = lean_ctor_get(v_inst_1205_, 0);
lean_inc_n(v_map_1206_, 2);
lean_dec_ref(v_inst_1205_);
v___f_1207_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1208_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1209_ = lean_apply_4(v_map_1206_, lean_box(0), lean_box(0), v___f_1208_, v_inst_1204_);
v___x_1210_ = lean_apply_4(v_map_1206_, lean_box(0), lean_box(0), v___f_1207_, v___x_1209_);
return v___x_1210_;
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

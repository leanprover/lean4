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
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_getLakeSharedDynlib___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_getLakeSharedDynlib___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_getLakeSharedDynlib___redArg___closed__0 = (const lean_object*)&l_Lake_getLakeSharedDynlib___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lake_Package_restoreAllArtifacts___redArg___lam__0(lean_object* v_self_511_, lean_object* v_x_512_){
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
LEAN_EXPORT void l_Lake_Package_restoreAllArtifacts___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_511_ = stack[0].m_obj;
lean_object* v_x_512_ = stack[1].m_obj;
uint8_t v_res_529_;
v_res_529_ = l_Lake_Package_restoreAllArtifacts___redArg___lam__0(v_self_511_, v_x_512_);
stack->m_num = v_res_529_;
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed(lean_object* v_self_530_, lean_object* v_x_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Lake_Package_restoreAllArtifacts___redArg___lam__0(v_self_530_, v_x_531_);
lean_dec_ref(v_x_531_);
lean_dec_ref(v_self_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts___redArg(lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_self_536_){
_start:
{
lean_object* v_map_537_; lean_object* v___f_538_; lean_object* v___x_539_; 
v_map_537_ = lean_ctor_get(v_inst_534_, 0);
lean_inc(v_map_537_);
lean_dec_ref(v_inst_534_);
v___f_538_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_538_, 0, v_self_536_);
v___x_539_ = lean_apply_4(v_map_537_, lean_box(0), lean_box(0), v___f_538_, v_inst_535_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_restoreAllArtifacts(lean_object* v_m_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_self_543_){
_start:
{
lean_object* v_map_544_; lean_object* v___f_545_; lean_object* v___x_546_; 
v_map_544_ = lean_ctor_get(v_inst_541_, 0);
lean_inc(v_map_544_);
lean_dec_ref(v_inst_541_);
v___f_545_ = lean_alloc_closure((void*)(l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_545_, 0, v_self_543_);
v___x_546_ = lean_apply_4(v_map_544_, lean_box(0), lean_box(0), v___f_545_, v_inst_542_);
return v___x_546_;
}
}
uint8_t l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(lean_object* v_self_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_config_549_; lean_object* v_enableArtifactCache_x3f_550_; 
v_config_549_ = lean_ctor_get(v_self_547_, 6);
v_enableArtifactCache_x3f_550_ = lean_ctor_get(v_config_549_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_550_) == 0)
{
lean_object* v_lakeEnv_551_; lean_object* v_enableArtifactCache_x3f_552_; 
v_lakeEnv_551_ = lean_ctor_get(v_x_548_, 0);
v_enableArtifactCache_x3f_552_ = lean_ctor_get(v_lakeEnv_551_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_552_) == 0)
{
lean_object* v_packages_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_config_556_; lean_object* v_enableArtifactCache_x3f_557_; 
v_packages_553_ = lean_ctor_get(v_x_548_, 4);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_array_fget_borrowed(v_packages_553_, v___x_554_);
v_config_556_ = lean_ctor_get(v___x_555_, 6);
v_enableArtifactCache_x3f_557_ = lean_ctor_get(v_config_556_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_557_) == 0)
{
uint8_t v___x_558_; 
v___x_558_ = 1;
return v___x_558_;
}
else
{
lean_object* v_val_559_; uint8_t v___x_560_; 
v_val_559_ = lean_ctor_get(v_enableArtifactCache_x3f_557_, 0);
v___x_560_ = lean_unbox(v_val_559_);
return v___x_560_;
}
}
else
{
lean_object* v_val_561_; uint8_t v___x_562_; 
v_val_561_ = lean_ctor_get(v_enableArtifactCache_x3f_552_, 0);
v___x_562_ = lean_unbox(v_val_561_);
return v___x_562_;
}
}
else
{
lean_object* v_val_563_; uint8_t v___x_564_; 
v_val_563_ = lean_ctor_get(v_enableArtifactCache_x3f_550_, 0);
v___x_564_ = lean_unbox(v_val_563_);
return v___x_564_;
}
}
}
LEAN_EXPORT void l_Lake_Package_isArtifactCacheReadable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_547_ = stack[0].m_obj;
lean_object* v_x_548_ = stack[1].m_obj;
uint8_t v_res_565_;
v_res_565_ = l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(v_self_547_, v_x_548_);
stack->m_num = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed(lean_object* v_self_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(v_self_566_, v_x_567_);
lean_dec_ref(v_x_567_);
lean_dec_ref(v_self_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable___redArg(lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_self_572_){
_start:
{
lean_object* v_map_573_; lean_object* v___f_574_; lean_object* v___x_575_; 
v_map_573_ = lean_ctor_get(v_inst_570_, 0);
lean_inc(v_map_573_);
lean_dec_ref(v_inst_570_);
v___f_574_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_574_, 0, v_self_572_);
v___x_575_ = lean_apply_4(v_map_573_, lean_box(0), lean_box(0), v___f_574_, v_inst_571_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheReadable(lean_object* v_m_576_, lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_self_579_){
_start:
{
lean_object* v_map_580_; lean_object* v___f_581_; lean_object* v___x_582_; 
v_map_580_ = lean_ctor_get(v_inst_577_, 0);
lean_inc(v_map_580_);
lean_dec_ref(v_inst_577_);
v___f_581_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_581_, 0, v_self_579_);
v___x_582_ = lean_apply_4(v_map_580_, lean_box(0), lean_box(0), v___f_581_, v_inst_578_);
return v___x_582_;
}
}
uint8_t l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(lean_object* v_self_583_, lean_object* v_x_584_){
_start:
{
lean_object* v_config_585_; lean_object* v_enableArtifactCache_x3f_586_; 
v_config_585_ = lean_ctor_get(v_self_583_, 6);
v_enableArtifactCache_x3f_586_ = lean_ctor_get(v_config_585_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_586_) == 0)
{
lean_object* v_lakeEnv_587_; lean_object* v_enableArtifactCache_x3f_588_; 
v_lakeEnv_587_ = lean_ctor_get(v_x_584_, 0);
v_enableArtifactCache_x3f_588_ = lean_ctor_get(v_lakeEnv_587_, 6);
if (lean_obj_tag(v_enableArtifactCache_x3f_588_) == 0)
{
lean_object* v_packages_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_config_592_; lean_object* v_enableArtifactCache_x3f_593_; 
v_packages_589_ = lean_ctor_get(v_x_584_, 4);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_array_fget_borrowed(v_packages_589_, v___x_590_);
v_config_592_ = lean_ctor_get(v___x_591_, 6);
v_enableArtifactCache_x3f_593_ = lean_ctor_get(v_config_592_, 24);
if (lean_obj_tag(v_enableArtifactCache_x3f_593_) == 0)
{
uint8_t v___x_594_; 
v___x_594_ = 0;
return v___x_594_;
}
else
{
lean_object* v_val_595_; uint8_t v___x_596_; 
v_val_595_ = lean_ctor_get(v_enableArtifactCache_x3f_593_, 0);
v___x_596_ = lean_unbox(v_val_595_);
return v___x_596_;
}
}
else
{
lean_object* v_val_597_; uint8_t v___x_598_; 
v_val_597_ = lean_ctor_get(v_enableArtifactCache_x3f_588_, 0);
v___x_598_ = lean_unbox(v_val_597_);
return v___x_598_;
}
}
else
{
lean_object* v_val_599_; uint8_t v___x_600_; 
v_val_599_ = lean_ctor_get(v_enableArtifactCache_x3f_586_, 0);
v___x_600_ = lean_unbox(v_val_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT void l_Lake_Package_isArtifactCacheWritable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_583_ = stack[0].m_obj;
lean_object* v_x_584_ = stack[1].m_obj;
uint8_t v_res_601_;
v_res_601_ = l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(v_self_583_, v_x_584_);
stack->m_num = v_res_601_;
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed(lean_object* v_self_602_, lean_object* v_x_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(v_self_602_, v_x_603_);
lean_dec_ref(v_x_603_);
lean_dec_ref(v_self_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable___redArg(lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_self_608_){
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
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheWritable(lean_object* v_m_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_self_615_){
_start:
{
lean_object* v_map_616_; lean_object* v___f_617_; lean_object* v___x_618_; 
v_map_616_ = lean_ctor_get(v_inst_613_, 0);
lean_inc(v_map_616_);
lean_dec_ref(v_inst_613_);
v___f_617_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_617_, 0, v_self_615_);
v___x_618_ = lean_apply_4(v_map_616_, lean_box(0), lean_box(0), v___f_617_, v_inst_614_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled___redArg(lean_object* v_inst_619_, lean_object* v_inst_620_, lean_object* v_self_621_){
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
LEAN_EXPORT lean_object* l_Lake_Package_isArtifactCacheEnabled(lean_object* v_m_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_self_628_){
_start:
{
lean_object* v_map_629_; lean_object* v___f_630_; lean_object* v___x_631_; 
v_map_629_ = lean_ctor_get(v_inst_626_, 0);
lean_inc(v_map_629_);
lean_dec_ref(v_inst_626_);
v___f_630_ = lean_alloc_closure((void*)(l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_630_, 0, v_self_628_);
v___x_631_ = lean_apply_4(v_map_629_, lean_box(0), lean_box(0), v___f_630_, v_inst_627_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg(lean_object* v_inst_632_){
_start:
{
lean_inc(v_inst_632_);
return v_inst_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___redArg___boxed(lean_object* v_inst_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lake_getLakeEnv___redArg(v_inst_633_);
lean_dec(v_inst_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv(lean_object* v_m_635_, lean_object* v_inst_636_){
_start:
{
lean_inc(v_inst_636_);
return v_inst_636_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___boxed(lean_object* v_m_637_, lean_object* v_inst_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lake_getLakeEnv(v_m_637_, v_inst_638_);
lean_dec(v_inst_638_);
return v_res_639_;
}
}
uint8_t l_Lake_getNoCache___redArg___lam__0(lean_object* v_x_640_){
_start:
{
uint8_t v_noCache_641_; 
v_noCache_641_ = lean_ctor_get_uint8(v_x_640_, sizeof(void*)*20);
return v_noCache_641_;
}
}
LEAN_EXPORT void l_Lake_getNoCache___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_640_ = stack[0].m_obj;
uint8_t v_res_642_;
v_res_642_ = l_Lake_getNoCache___redArg___lam__0(v_x_640_);
stack->m_num = v_res_642_;
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg___lam__0___boxed(lean_object* v_x_643_){
_start:
{
uint8_t v_res_644_; lean_object* v_r_645_; 
v_res_644_ = l_Lake_getNoCache___redArg___lam__0(v_x_643_);
lean_dec_ref(v_x_643_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___redArg(lean_object* v_inst_647_, lean_object* v_inst_648_){
_start:
{
lean_object* v_map_649_; lean_object* v___f_650_; lean_object* v___x_651_; 
v_map_649_ = lean_ctor_get(v_inst_648_, 0);
lean_inc(v_map_649_);
lean_dec_ref(v_inst_648_);
v___f_650_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_651_ = lean_apply_4(v_map_649_, lean_box(0), lean_box(0), v___f_650_, v_inst_647_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache(lean_object* v_m_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_){
_start:
{
lean_object* v_map_656_; lean_object* v___f_657_; lean_object* v___x_658_; 
v_map_656_ = lean_ctor_get(v_inst_654_, 0);
lean_inc(v_map_656_);
lean_dec_ref(v_inst_654_);
v___f_657_ = ((lean_object*)(l_Lake_getNoCache___redArg___closed__0));
v___x_658_ = lean_apply_4(v_map_656_, lean_box(0), lean_box(0), v___f_657_, v_inst_653_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___boxed(lean_object* v_m_659_, lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_inst_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lake_getNoCache(v_m_659_, v_inst_660_, v_inst_661_, v_inst_662_);
lean_dec(v_inst_662_);
return v_res_663_;
}
}
uint8_t l_Lake_getTryCache___redArg___lam__0(lean_object* v_x_664_){
_start:
{
uint8_t v_noCache_665_; 
v_noCache_665_ = lean_ctor_get_uint8(v_x_664_, sizeof(void*)*20);
if (v_noCache_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = 1;
return v___x_666_;
}
else
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
}
}
LEAN_EXPORT void l_Lake_getTryCache___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_664_ = stack[0].m_obj;
uint8_t v_res_668_;
v_res_668_ = l_Lake_getTryCache___redArg___lam__0(v_x_664_);
stack->m_num = v_res_668_;
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg___lam__0___boxed(lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Lake_getTryCache___redArg___lam__0(v_x_669_);
lean_dec_ref(v_x_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___redArg(lean_object* v_inst_673_, lean_object* v_inst_674_){
_start:
{
lean_object* v_map_675_; lean_object* v___f_676_; lean_object* v___x_677_; 
v_map_675_ = lean_ctor_get(v_inst_674_, 0);
lean_inc(v_map_675_);
lean_dec_ref(v_inst_674_);
v___f_676_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_677_ = lean_apply_4(v_map_675_, lean_box(0), lean_box(0), v___f_676_, v_inst_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object* v_m_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_){
_start:
{
lean_object* v_map_682_; lean_object* v___f_683_; lean_object* v___x_684_; 
v_map_682_ = lean_ctor_get(v_inst_680_, 0);
lean_inc(v_map_682_);
lean_dec_ref(v_inst_680_);
v___f_683_ = ((lean_object*)(l_Lake_getTryCache___redArg___closed__0));
v___x_684_ = lean_apply_4(v_map_682_, lean_box(0), lean_box(0), v___f_683_, v_inst_679_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___boxed(lean_object* v_m_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lake_getTryCache(v_m_685_, v_inst_686_, v_inst_687_, v_inst_688_);
lean_dec(v_inst_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0(lean_object* v_x_690_){
_start:
{
lean_object* v_pkgUrlMap_691_; 
v_pkgUrlMap_691_ = lean_ctor_get(v_x_690_, 5);
lean_inc(v_pkgUrlMap_691_);
return v_pkgUrlMap_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg___lam__0___boxed(lean_object* v_x_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lake_getPkgUrlMap___redArg___lam__0(v_x_692_);
lean_dec_ref(v_x_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___redArg(lean_object* v_inst_695_, lean_object* v_inst_696_){
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
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object* v_m_700_, lean_object* v_inst_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v_map_703_; lean_object* v___f_704_; lean_object* v___x_705_; 
v_map_703_ = lean_ctor_get(v_inst_702_, 0);
lean_inc(v_map_703_);
lean_dec_ref(v_inst_702_);
v___f_704_ = ((lean_object*)(l_Lake_getPkgUrlMap___redArg___closed__0));
v___x_705_ = lean_apply_4(v_map_703_, lean_box(0), lean_box(0), v___f_704_, v_inst_701_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0(lean_object* v_x_706_){
_start:
{
lean_object* v_toolchain_707_; 
v_toolchain_707_ = lean_ctor_get(v_x_706_, 19);
lean_inc_ref(v_toolchain_707_);
return v_toolchain_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg___lam__0___boxed(lean_object* v_x_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lake_getElanToolchain___redArg___lam__0(v_x_708_);
lean_dec_ref(v_x_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___redArg(lean_object* v_inst_711_, lean_object* v_inst_712_){
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
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object* v_m_716_, lean_object* v_inst_717_, lean_object* v_inst_718_){
_start:
{
lean_object* v_map_719_; lean_object* v___f_720_; lean_object* v___x_721_; 
v_map_719_ = lean_ctor_get(v_inst_718_, 0);
lean_inc(v_map_719_);
lean_dec_ref(v_inst_718_);
v___f_720_ = ((lean_object*)(l_Lake_getElanToolchain___redArg___closed__0));
v___x_721_ = lean_apply_4(v_map_719_, lean_box(0), lean_box(0), v___f_720_, v_inst_717_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___redArg(lean_object* v_inst_723_, lean_object* v_inst_724_){
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
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object* v_m_728_, lean_object* v_inst_729_, lean_object* v_inst_730_){
_start:
{
lean_object* v_map_731_; lean_object* v___f_732_; lean_object* v___x_733_; 
v_map_731_ = lean_ctor_get(v_inst_730_, 0);
lean_inc(v_map_731_);
lean_dec_ref(v_inst_730_);
v___f_732_ = ((lean_object*)(l_Lake_getEnvLeanPath___redArg___closed__0));
v___x_733_ = lean_apply_4(v_map_731_, lean_box(0), lean_box(0), v___f_732_, v_inst_729_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___redArg(lean_object* v_inst_735_, lean_object* v_inst_736_){
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
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object* v_m_740_, lean_object* v_inst_741_, lean_object* v_inst_742_){
_start:
{
lean_object* v_map_743_; lean_object* v___f_744_; lean_object* v___x_745_; 
v_map_743_ = lean_ctor_get(v_inst_742_, 0);
lean_inc(v_map_743_);
lean_dec_ref(v_inst_742_);
v___f_744_ = ((lean_object*)(l_Lake_getEnvLeanSrcPath___redArg___closed__0));
v___x_745_ = lean_apply_4(v_map_743_, lean_box(0), lean_box(0), v___f_744_, v_inst_741_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___redArg(lean_object* v_inst_747_, lean_object* v_inst_748_){
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
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object* v_m_752_, lean_object* v_inst_753_, lean_object* v_inst_754_){
_start:
{
lean_object* v_map_755_; lean_object* v___f_756_; lean_object* v___x_757_; 
v_map_755_ = lean_ctor_get(v_inst_754_, 0);
lean_inc(v_map_755_);
lean_dec_ref(v_inst_754_);
v___f_756_ = ((lean_object*)(l_Lake_getEnvSharedLibPath___redArg___closed__0));
v___x_757_ = lean_apply_4(v_map_755_, lean_box(0), lean_box(0), v___f_756_, v_inst_753_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0(lean_object* v_x_758_){
_start:
{
lean_object* v_elan_x3f_759_; 
v_elan_x3f_759_ = lean_ctor_get(v_x_758_, 2);
lean_inc(v_elan_x3f_759_);
return v_elan_x3f_759_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg___lam__0___boxed(lean_object* v_x_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lake_getElanInstall_x3f___redArg___lam__0(v_x_760_);
lean_dec_ref(v_x_760_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___redArg(lean_object* v_inst_763_, lean_object* v_inst_764_){
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
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object* v_m_768_, lean_object* v_inst_769_, lean_object* v_inst_770_){
_start:
{
lean_object* v_map_771_; lean_object* v___f_772_; lean_object* v___x_773_; 
v_map_771_ = lean_ctor_get(v_inst_770_, 0);
lean_inc(v_map_771_);
lean_dec_ref(v_inst_770_);
v___f_772_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_773_ = lean_apply_4(v_map_771_, lean_box(0), lean_box(0), v___f_772_, v_inst_769_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg___lam__0(lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v___x_775_; 
v___x_775_ = lean_box(0);
return v___x_775_;
}
else
{
lean_object* v_val_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
v_val_776_ = lean_ctor_get(v_x_774_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_784_ == 0)
{
v___x_778_ = v_x_774_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_val_776_);
lean_dec(v_x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_home_780_; lean_object* v___x_782_; 
v_home_780_ = lean_ctor_get(v_val_776_, 0);
lean_inc_ref(v_home_780_);
lean_dec(v_val_776_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v_home_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_home_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___redArg(lean_object* v_inst_786_, lean_object* v_inst_787_){
_start:
{
lean_object* v_map_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_map_788_ = lean_ctor_get(v_inst_787_, 0);
lean_inc_n(v_map_788_, 2);
lean_dec_ref(v_inst_787_);
v___f_789_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_790_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_791_ = lean_apply_4(v_map_788_, lean_box(0), lean_box(0), v___f_790_, v_inst_786_);
v___x_792_ = lean_apply_4(v_map_788_, lean_box(0), lean_box(0), v___f_789_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object* v_m_793_, lean_object* v_inst_794_, lean_object* v_inst_795_){
_start:
{
lean_object* v_map_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_map_796_ = lean_ctor_get(v_inst_795_, 0);
lean_inc_n(v_map_796_, 2);
lean_dec_ref(v_inst_795_);
v___f_797_ = ((lean_object*)(l_Lake_getElanHome_x3f___redArg___closed__0));
v___f_798_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_799_ = lean_apply_4(v_map_796_, lean_box(0), lean_box(0), v___f_798_, v_inst_794_);
v___x_800_ = lean_apply_4(v_map_796_, lean_box(0), lean_box(0), v___f_797_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg___lam__0(lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_801_) == 0)
{
lean_object* v___x_802_; 
v___x_802_ = lean_box(0);
return v___x_802_;
}
else
{
lean_object* v_val_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v_val_803_ = lean_ctor_get(v_x_801_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_801_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v_x_801_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_val_803_);
lean_dec(v_x_801_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_elan_807_; lean_object* v___x_809_; 
v_elan_807_ = lean_ctor_get(v_val_803_, 1);
lean_inc_ref(v_elan_807_);
lean_dec(v_val_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v_elan_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_elan_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_){
_start:
{
lean_object* v_map_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_map_815_ = lean_ctor_get(v_inst_814_, 0);
lean_inc_n(v_map_815_, 2);
lean_dec_ref(v_inst_814_);
v___f_816_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_817_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_818_ = lean_apply_4(v_map_815_, lean_box(0), lean_box(0), v___f_817_, v_inst_813_);
v___x_819_ = lean_apply_4(v_map_815_, lean_box(0), lean_box(0), v___f_816_, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object* v_m_820_, lean_object* v_inst_821_, lean_object* v_inst_822_){
_start:
{
lean_object* v_map_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_map_823_ = lean_ctor_get(v_inst_822_, 0);
lean_inc_n(v_map_823_, 2);
lean_dec_ref(v_inst_822_);
v___f_824_ = ((lean_object*)(l_Lake_getElan_x3f___redArg___closed__0));
v___f_825_ = ((lean_object*)(l_Lake_getElanInstall_x3f___redArg___closed__0));
v___x_826_ = lean_apply_4(v_map_823_, lean_box(0), lean_box(0), v___f_825_, v_inst_821_);
v___x_827_ = lean_apply_4(v_map_823_, lean_box(0), lean_box(0), v___f_824_, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0(lean_object* v_x_828_){
_start:
{
lean_object* v_lean_829_; 
v_lean_829_ = lean_ctor_get(v_x_828_, 1);
lean_inc_ref(v_lean_829_);
return v_lean_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg___lam__0___boxed(lean_object* v_x_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lake_getLeanInstall___redArg___lam__0(v_x_830_);
lean_dec_ref(v_x_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___redArg(lean_object* v_inst_833_, lean_object* v_inst_834_){
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
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object* v_m_838_, lean_object* v_inst_839_, lean_object* v_inst_840_){
_start:
{
lean_object* v_map_841_; lean_object* v___f_842_; lean_object* v___x_843_; 
v_map_841_ = lean_ctor_get(v_inst_840_, 0);
lean_inc(v_map_841_);
lean_dec_ref(v_inst_840_);
v___f_842_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_843_ = lean_apply_4(v_map_841_, lean_box(0), lean_box(0), v___f_842_, v_inst_839_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0(lean_object* v_x_844_){
_start:
{
lean_object* v_sysroot_845_; 
v_sysroot_845_ = lean_ctor_get(v_x_844_, 0);
lean_inc_ref(v_sysroot_845_);
return v_sysroot_845_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg___lam__0___boxed(lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lake_getLeanSysroot___redArg___lam__0(v_x_846_);
lean_dec_ref(v_x_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___redArg(lean_object* v_inst_849_, lean_object* v_inst_850_){
_start:
{
lean_object* v_map_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_map_851_ = lean_ctor_get(v_inst_850_, 0);
lean_inc_n(v_map_851_, 2);
lean_dec_ref(v_inst_850_);
v___f_852_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_853_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_854_ = lean_apply_4(v_map_851_, lean_box(0), lean_box(0), v___f_853_, v_inst_849_);
v___x_855_ = lean_apply_4(v_map_851_, lean_box(0), lean_box(0), v___f_852_, v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object* v_m_856_, lean_object* v_inst_857_, lean_object* v_inst_858_){
_start:
{
lean_object* v_map_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_map_859_ = lean_ctor_get(v_inst_858_, 0);
lean_inc_n(v_map_859_, 2);
lean_dec_ref(v_inst_858_);
v___f_860_ = ((lean_object*)(l_Lake_getLeanSysroot___redArg___closed__0));
v___f_861_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_862_ = lean_apply_4(v_map_859_, lean_box(0), lean_box(0), v___f_861_, v_inst_857_);
v___x_863_ = lean_apply_4(v_map_859_, lean_box(0), lean_box(0), v___f_860_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0(lean_object* v_x_864_){
_start:
{
lean_object* v_srcDir_865_; 
v_srcDir_865_ = lean_ctor_get(v_x_864_, 2);
lean_inc_ref(v_srcDir_865_);
return v_srcDir_865_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg___lam__0___boxed(lean_object* v_x_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lake_getLeanSrcDir___redArg___lam__0(v_x_866_);
lean_dec_ref(v_x_866_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___redArg(lean_object* v_inst_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v_map_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_map_871_ = lean_ctor_get(v_inst_870_, 0);
lean_inc_n(v_map_871_, 2);
lean_dec_ref(v_inst_870_);
v___f_872_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_873_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_874_ = lean_apply_4(v_map_871_, lean_box(0), lean_box(0), v___f_873_, v_inst_869_);
v___x_875_ = lean_apply_4(v_map_871_, lean_box(0), lean_box(0), v___f_872_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object* v_m_876_, lean_object* v_inst_877_, lean_object* v_inst_878_){
_start:
{
lean_object* v_map_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_map_879_ = lean_ctor_get(v_inst_878_, 0);
lean_inc_n(v_map_879_, 2);
lean_dec_ref(v_inst_878_);
v___f_880_ = ((lean_object*)(l_Lake_getLeanSrcDir___redArg___closed__0));
v___f_881_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_882_ = lean_apply_4(v_map_879_, lean_box(0), lean_box(0), v___f_881_, v_inst_877_);
v___x_883_ = lean_apply_4(v_map_879_, lean_box(0), lean_box(0), v___f_880_, v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0(lean_object* v_x_884_){
_start:
{
lean_object* v_leanLibDir_885_; 
v_leanLibDir_885_ = lean_ctor_get(v_x_884_, 3);
lean_inc_ref(v_leanLibDir_885_);
return v_leanLibDir_885_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg___lam__0___boxed(lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lake_getLeanLibDir___redArg___lam__0(v_x_886_);
lean_dec_ref(v_x_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___redArg(lean_object* v_inst_889_, lean_object* v_inst_890_){
_start:
{
lean_object* v_map_891_; lean_object* v___f_892_; lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_map_891_ = lean_ctor_get(v_inst_890_, 0);
lean_inc_n(v_map_891_, 2);
lean_dec_ref(v_inst_890_);
v___f_892_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_893_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_894_ = lean_apply_4(v_map_891_, lean_box(0), lean_box(0), v___f_893_, v_inst_889_);
v___x_895_ = lean_apply_4(v_map_891_, lean_box(0), lean_box(0), v___f_892_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object* v_m_896_, lean_object* v_inst_897_, lean_object* v_inst_898_){
_start:
{
lean_object* v_map_899_; lean_object* v___f_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_map_899_ = lean_ctor_get(v_inst_898_, 0);
lean_inc_n(v_map_899_, 2);
lean_dec_ref(v_inst_898_);
v___f_900_ = ((lean_object*)(l_Lake_getLeanLibDir___redArg___closed__0));
v___f_901_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_902_ = lean_apply_4(v_map_899_, lean_box(0), lean_box(0), v___f_901_, v_inst_897_);
v___x_903_ = lean_apply_4(v_map_899_, lean_box(0), lean_box(0), v___f_900_, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0(lean_object* v_x_904_){
_start:
{
lean_object* v_includeDir_905_; 
v_includeDir_905_ = lean_ctor_get(v_x_904_, 4);
lean_inc_ref(v_includeDir_905_);
return v_includeDir_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg___lam__0___boxed(lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lake_getLeanIncludeDir___redArg___lam__0(v_x_906_);
lean_dec_ref(v_x_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___redArg(lean_object* v_inst_909_, lean_object* v_inst_910_){
_start:
{
lean_object* v_map_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_map_911_ = lean_ctor_get(v_inst_910_, 0);
lean_inc_n(v_map_911_, 2);
lean_dec_ref(v_inst_910_);
v___f_912_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_913_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_914_ = lean_apply_4(v_map_911_, lean_box(0), lean_box(0), v___f_913_, v_inst_909_);
v___x_915_ = lean_apply_4(v_map_911_, lean_box(0), lean_box(0), v___f_912_, v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object* v_m_916_, lean_object* v_inst_917_, lean_object* v_inst_918_){
_start:
{
lean_object* v_map_919_; lean_object* v___f_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_map_919_ = lean_ctor_get(v_inst_918_, 0);
lean_inc_n(v_map_919_, 2);
lean_dec_ref(v_inst_918_);
v___f_920_ = ((lean_object*)(l_Lake_getLeanIncludeDir___redArg___closed__0));
v___f_921_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_922_ = lean_apply_4(v_map_919_, lean_box(0), lean_box(0), v___f_921_, v_inst_917_);
v___x_923_ = lean_apply_4(v_map_919_, lean_box(0), lean_box(0), v___f_920_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0(lean_object* v_x_924_){
_start:
{
lean_object* v_systemLibDir_925_; 
v_systemLibDir_925_ = lean_ctor_get(v_x_924_, 5);
lean_inc_ref(v_systemLibDir_925_);
return v_systemLibDir_925_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed(lean_object* v_x_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lake_getLeanSystemLibDir___redArg___lam__0(v_x_926_);
lean_dec_ref(v_x_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___redArg(lean_object* v_inst_929_, lean_object* v_inst_930_){
_start:
{
lean_object* v_map_931_; lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_map_931_ = lean_ctor_get(v_inst_930_, 0);
lean_inc_n(v_map_931_, 2);
lean_dec_ref(v_inst_930_);
v___f_932_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_933_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_934_ = lean_apply_4(v_map_931_, lean_box(0), lean_box(0), v___f_933_, v_inst_929_);
v___x_935_ = lean_apply_4(v_map_931_, lean_box(0), lean_box(0), v___f_932_, v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object* v_m_936_, lean_object* v_inst_937_, lean_object* v_inst_938_){
_start:
{
lean_object* v_map_939_; lean_object* v___f_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_map_939_ = lean_ctor_get(v_inst_938_, 0);
lean_inc_n(v_map_939_, 2);
lean_dec_ref(v_inst_938_);
v___f_940_ = ((lean_object*)(l_Lake_getLeanSystemLibDir___redArg___closed__0));
v___f_941_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_942_ = lean_apply_4(v_map_939_, lean_box(0), lean_box(0), v___f_941_, v_inst_937_);
v___x_943_ = lean_apply_4(v_map_939_, lean_box(0), lean_box(0), v___f_940_, v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0(lean_object* v_x_944_){
_start:
{
lean_object* v_lean_945_; 
v_lean_945_ = lean_ctor_get(v_x_944_, 7);
lean_inc_ref(v_lean_945_);
return v_lean_945_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg___lam__0___boxed(lean_object* v_x_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lake_getLean___redArg___lam__0(v_x_946_);
lean_dec_ref(v_x_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___redArg(lean_object* v_inst_949_, lean_object* v_inst_950_){
_start:
{
lean_object* v_map_951_; lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_map_951_ = lean_ctor_get(v_inst_950_, 0);
lean_inc_n(v_map_951_, 2);
lean_dec_ref(v_inst_950_);
v___f_952_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_953_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_954_ = lean_apply_4(v_map_951_, lean_box(0), lean_box(0), v___f_953_, v_inst_949_);
v___x_955_ = lean_apply_4(v_map_951_, lean_box(0), lean_box(0), v___f_952_, v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object* v_m_956_, lean_object* v_inst_957_, lean_object* v_inst_958_){
_start:
{
lean_object* v_map_959_; lean_object* v___f_960_; lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_map_959_ = lean_ctor_get(v_inst_958_, 0);
lean_inc_n(v_map_959_, 2);
lean_dec_ref(v_inst_958_);
v___f_960_ = ((lean_object*)(l_Lake_getLean___redArg___closed__0));
v___f_961_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_962_ = lean_apply_4(v_map_959_, lean_box(0), lean_box(0), v___f_961_, v_inst_957_);
v___x_963_ = lean_apply_4(v_map_959_, lean_box(0), lean_box(0), v___f_960_, v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0(lean_object* v_x_964_){
_start:
{
lean_object* v_leanir_965_; 
v_leanir_965_ = lean_ctor_get(v_x_964_, 8);
lean_inc_ref(v_leanir_965_);
return v_leanir_965_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg___lam__0___boxed(lean_object* v_x_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lake_getLeanir___redArg___lam__0(v_x_966_);
lean_dec_ref(v_x_966_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir___redArg(lean_object* v_inst_969_, lean_object* v_inst_970_){
_start:
{
lean_object* v_map_971_; lean_object* v___f_972_; lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_map_971_ = lean_ctor_get(v_inst_970_, 0);
lean_inc_n(v_map_971_, 2);
lean_dec_ref(v_inst_970_);
v___f_972_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_973_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_974_ = lean_apply_4(v_map_971_, lean_box(0), lean_box(0), v___f_973_, v_inst_969_);
v___x_975_ = lean_apply_4(v_map_971_, lean_box(0), lean_box(0), v___f_972_, v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanir(lean_object* v_m_976_, lean_object* v_inst_977_, lean_object* v_inst_978_){
_start:
{
lean_object* v_map_979_; lean_object* v___f_980_; lean_object* v___f_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_map_979_ = lean_ctor_get(v_inst_978_, 0);
lean_inc_n(v_map_979_, 2);
lean_dec_ref(v_inst_978_);
v___f_980_ = ((lean_object*)(l_Lake_getLeanir___redArg___closed__0));
v___f_981_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_982_ = lean_apply_4(v_map_979_, lean_box(0), lean_box(0), v___f_981_, v_inst_977_);
v___x_983_ = lean_apply_4(v_map_979_, lean_box(0), lean_box(0), v___f_980_, v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0(lean_object* v_x_984_){
_start:
{
lean_object* v_leanc_985_; 
v_leanc_985_ = lean_ctor_get(v_x_984_, 9);
lean_inc_ref(v_leanc_985_);
return v_leanc_985_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg___lam__0___boxed(lean_object* v_x_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lake_getLeanc___redArg___lam__0(v_x_986_);
lean_dec_ref(v_x_986_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___redArg(lean_object* v_inst_989_, lean_object* v_inst_990_){
_start:
{
lean_object* v_map_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_map_991_ = lean_ctor_get(v_inst_990_, 0);
lean_inc_n(v_map_991_, 2);
lean_dec_ref(v_inst_990_);
v___f_992_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_993_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_994_ = lean_apply_4(v_map_991_, lean_box(0), lean_box(0), v___f_993_, v_inst_989_);
v___x_995_ = lean_apply_4(v_map_991_, lean_box(0), lean_box(0), v___f_992_, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object* v_m_996_, lean_object* v_inst_997_, lean_object* v_inst_998_){
_start:
{
lean_object* v_map_999_; lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_map_999_ = lean_ctor_get(v_inst_998_, 0);
lean_inc_n(v_map_999_, 2);
lean_dec_ref(v_inst_998_);
v___f_1000_ = ((lean_object*)(l_Lake_getLeanc___redArg___closed__0));
v___f_1001_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1002_ = lean_apply_4(v_map_999_, lean_box(0), lean_box(0), v___f_1001_, v_inst_997_);
v___x_1003_ = lean_apply_4(v_map_999_, lean_box(0), lean_box(0), v___f_1000_, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0(lean_object* v_x_1004_){
_start:
{
lean_object* v_leantar_1005_; 
v_leantar_1005_ = lean_ctor_get(v_x_1004_, 10);
lean_inc_ref(v_leantar_1005_);
return v_leantar_1005_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg___lam__0___boxed(lean_object* v_x_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lake_getLeantar___redArg___lam__0(v_x_1006_);
lean_dec_ref(v_x_1006_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar___redArg(lean_object* v_inst_1009_, lean_object* v_inst_1010_){
_start:
{
lean_object* v_map_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_map_1011_ = lean_ctor_get(v_inst_1010_, 0);
lean_inc_n(v_map_1011_, 2);
lean_dec_ref(v_inst_1010_);
v___f_1012_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1013_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1014_ = lean_apply_4(v_map_1011_, lean_box(0), lean_box(0), v___f_1013_, v_inst_1009_);
v___x_1015_ = lean_apply_4(v_map_1011_, lean_box(0), lean_box(0), v___f_1012_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeantar(lean_object* v_m_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_){
_start:
{
lean_object* v_map_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_map_1019_ = lean_ctor_get(v_inst_1018_, 0);
lean_inc_n(v_map_1019_, 2);
lean_dec_ref(v_inst_1018_);
v___f_1020_ = ((lean_object*)(l_Lake_getLeantar___redArg___closed__0));
v___f_1021_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1022_ = lean_apply_4(v_map_1019_, lean_box(0), lean_box(0), v___f_1021_, v_inst_1017_);
v___x_1023_ = lean_apply_4(v_map_1019_, lean_box(0), lean_box(0), v___f_1020_, v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg___lam__0(lean_object* v_x_1024_){
_start:
{
lean_object* v_sharedDynlib_1025_; 
v_sharedDynlib_1025_ = lean_ctor_get(v_x_1024_, 12);
lean_inc_ref(v_sharedDynlib_1025_);
return v_sharedDynlib_1025_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg___lam__0___boxed(lean_object* v_x_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lake_getLeanSharedDynlib___redArg___lam__0(v_x_1026_);
lean_dec_ref(v_x_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib___redArg(lean_object* v_inst_1029_, lean_object* v_inst_1030_){
_start:
{
lean_object* v_map_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_map_1031_ = lean_ctor_get(v_inst_1030_, 0);
lean_inc_n(v_map_1031_, 2);
lean_dec_ref(v_inst_1030_);
v___f_1032_ = ((lean_object*)(l_Lake_getLeanSharedDynlib___redArg___closed__0));
v___f_1033_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1034_ = lean_apply_4(v_map_1031_, lean_box(0), lean_box(0), v___f_1033_, v_inst_1029_);
v___x_1035_ = lean_apply_4(v_map_1031_, lean_box(0), lean_box(0), v___f_1032_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlib(lean_object* v_m_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_){
_start:
{
lean_object* v_map_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_map_1039_ = lean_ctor_get(v_inst_1038_, 0);
lean_inc_n(v_map_1039_, 2);
lean_dec_ref(v_inst_1038_);
v___f_1040_ = ((lean_object*)(l_Lake_getLeanSharedDynlib___redArg___closed__0));
v___f_1041_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1042_ = lean_apply_4(v_map_1039_, lean_box(0), lean_box(0), v___f_1041_, v_inst_1037_);
v___x_1043_ = lean_apply_4(v_map_1039_, lean_box(0), lean_box(0), v___f_1040_, v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg___lam__0(lean_object* v_x_1044_){
_start:
{
lean_object* v_sharedDynlibs_1045_; 
v_sharedDynlibs_1045_ = lean_ctor_get(v_x_1044_, 11);
lean_inc_ref(v_sharedDynlibs_1045_);
return v_sharedDynlibs_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg___lam__0___boxed(lean_object* v_x_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lake_getLeanSharedDynlibs___redArg___lam__0(v_x_1046_);
lean_dec_ref(v_x_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs___redArg(lean_object* v_inst_1049_, lean_object* v_inst_1050_){
_start:
{
lean_object* v_map_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_map_1051_ = lean_ctor_get(v_inst_1050_, 0);
lean_inc_n(v_map_1051_, 2);
lean_dec_ref(v_inst_1050_);
v___f_1052_ = ((lean_object*)(l_Lake_getLeanSharedDynlibs___redArg___closed__0));
v___f_1053_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1054_ = lean_apply_4(v_map_1051_, lean_box(0), lean_box(0), v___f_1053_, v_inst_1049_);
v___x_1055_ = lean_apply_4(v_map_1051_, lean_box(0), lean_box(0), v___f_1052_, v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedDynlibs(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_){
_start:
{
lean_object* v_map_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_map_1059_ = lean_ctor_get(v_inst_1058_, 0);
lean_inc_n(v_map_1059_, 2);
lean_dec_ref(v_inst_1058_);
v___f_1060_ = ((lean_object*)(l_Lake_getLeanSharedDynlibs___redArg___closed__0));
v___f_1061_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1062_ = lean_apply_4(v_map_1059_, lean_box(0), lean_box(0), v___f_1061_, v_inst_1057_);
v___x_1063_ = lean_apply_4(v_map_1059_, lean_box(0), lean_box(0), v___f_1060_, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0(lean_object* v_x_1064_){
_start:
{
lean_object* v_sharedDynlib_1065_; lean_object* v_path_1066_; 
v_sharedDynlib_1065_ = lean_ctor_get(v_x_1064_, 12);
v_path_1066_ = lean_ctor_get(v_sharedDynlib_1065_, 0);
lean_inc_ref(v_path_1066_);
return v_path_1066_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg___lam__0___boxed(lean_object* v_x_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lake_getLeanSharedLib___redArg___lam__0(v_x_1067_);
lean_dec_ref(v_x_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___redArg(lean_object* v_inst_1070_, lean_object* v_inst_1071_){
_start:
{
lean_object* v_map_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_map_1072_ = lean_ctor_get(v_inst_1071_, 0);
lean_inc_n(v_map_1072_, 2);
lean_dec_ref(v_inst_1071_);
v___f_1073_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1074_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1075_ = lean_apply_4(v_map_1072_, lean_box(0), lean_box(0), v___f_1074_, v_inst_1070_);
v___x_1076_ = lean_apply_4(v_map_1072_, lean_box(0), lean_box(0), v___f_1073_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object* v_m_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_){
_start:
{
lean_object* v_map_1080_; lean_object* v___f_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_map_1080_ = lean_ctor_get(v_inst_1079_, 0);
lean_inc_n(v_map_1080_, 2);
lean_dec_ref(v_inst_1079_);
v___f_1081_ = ((lean_object*)(l_Lake_getLeanSharedLib___redArg___closed__0));
v___f_1082_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1083_ = lean_apply_4(v_map_1080_, lean_box(0), lean_box(0), v___f_1082_, v_inst_1078_);
v___x_1084_ = lean_apply_4(v_map_1080_, lean_box(0), lean_box(0), v___f_1081_, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0(lean_object* v_x_1085_){
_start:
{
lean_object* v_ar_1086_; 
v_ar_1086_ = lean_ctor_get(v_x_1085_, 13);
lean_inc_ref(v_ar_1086_);
return v_ar_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg___lam__0___boxed(lean_object* v_x_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lake_getLeanAr___redArg___lam__0(v_x_1087_);
lean_dec_ref(v_x_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___redArg(lean_object* v_inst_1090_, lean_object* v_inst_1091_){
_start:
{
lean_object* v_map_1092_; lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_map_1092_ = lean_ctor_get(v_inst_1091_, 0);
lean_inc_n(v_map_1092_, 2);
lean_dec_ref(v_inst_1091_);
v___f_1093_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1094_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1095_ = lean_apply_4(v_map_1092_, lean_box(0), lean_box(0), v___f_1094_, v_inst_1090_);
v___x_1096_ = lean_apply_4(v_map_1092_, lean_box(0), lean_box(0), v___f_1093_, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object* v_m_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_){
_start:
{
lean_object* v_map_1100_; lean_object* v___f_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_map_1100_ = lean_ctor_get(v_inst_1099_, 0);
lean_inc_n(v_map_1100_, 2);
lean_dec_ref(v_inst_1099_);
v___f_1101_ = ((lean_object*)(l_Lake_getLeanAr___redArg___closed__0));
v___f_1102_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1103_ = lean_apply_4(v_map_1100_, lean_box(0), lean_box(0), v___f_1102_, v_inst_1098_);
v___x_1104_ = lean_apply_4(v_map_1100_, lean_box(0), lean_box(0), v___f_1101_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0(lean_object* v_x_1105_){
_start:
{
lean_object* v_cc_1106_; 
v_cc_1106_ = lean_ctor_get(v_x_1105_, 14);
lean_inc_ref(v_cc_1106_);
return v_cc_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg___lam__0___boxed(lean_object* v_x_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lake_getLeanCc___redArg___lam__0(v_x_1107_);
lean_dec_ref(v_x_1107_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___redArg(lean_object* v_inst_1110_, lean_object* v_inst_1111_){
_start:
{
lean_object* v_map_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_map_1112_ = lean_ctor_get(v_inst_1111_, 0);
lean_inc_n(v_map_1112_, 2);
lean_dec_ref(v_inst_1111_);
v___f_1113_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1114_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1115_ = lean_apply_4(v_map_1112_, lean_box(0), lean_box(0), v___f_1114_, v_inst_1110_);
v___x_1116_ = lean_apply_4(v_map_1112_, lean_box(0), lean_box(0), v___f_1113_, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object* v_m_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_){
_start:
{
lean_object* v_map_1120_; lean_object* v___f_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_map_1120_ = lean_ctor_get(v_inst_1119_, 0);
lean_inc_n(v_map_1120_, 2);
lean_dec_ref(v_inst_1119_);
v___f_1121_ = ((lean_object*)(l_Lake_getLeanCc___redArg___closed__0));
v___f_1122_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1123_ = lean_apply_4(v_map_1120_, lean_box(0), lean_box(0), v___f_1122_, v_inst_1118_);
v___x_1124_ = lean_apply_4(v_map_1120_, lean_box(0), lean_box(0), v___f_1121_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___redArg(lean_object* v_inst_1126_, lean_object* v_inst_1127_){
_start:
{
lean_object* v_map_1128_; lean_object* v___f_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_map_1128_ = lean_ctor_get(v_inst_1127_, 0);
lean_inc_n(v_map_1128_, 2);
lean_dec_ref(v_inst_1127_);
v___f_1129_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1130_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1131_ = lean_apply_4(v_map_1128_, lean_box(0), lean_box(0), v___f_1130_, v_inst_1126_);
v___x_1132_ = lean_apply_4(v_map_1128_, lean_box(0), lean_box(0), v___f_1129_, v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object* v_m_1133_, lean_object* v_inst_1134_, lean_object* v_inst_1135_){
_start:
{
lean_object* v_map_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_map_1136_ = lean_ctor_get(v_inst_1135_, 0);
lean_inc_n(v_map_1136_, 2);
lean_dec_ref(v_inst_1135_);
v___f_1137_ = ((lean_object*)(l_Lake_getLeanCc_x3f___redArg___closed__0));
v___f_1138_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1139_ = lean_apply_4(v_map_1136_, lean_box(0), lean_box(0), v___f_1138_, v_inst_1134_);
v___x_1140_ = lean_apply_4(v_map_1136_, lean_box(0), lean_box(0), v___f_1137_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0(lean_object* v_x_1141_){
_start:
{
lean_object* v_ccLinkSharedFlags_1142_; 
v_ccLinkSharedFlags_1142_ = lean_ctor_get(v_x_1141_, 20);
lean_inc_ref(v_ccLinkSharedFlags_1142_);
return v_ccLinkSharedFlags_1142_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed(lean_object* v_x_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lake_getLeanLinkSharedFlags___redArg___lam__0(v_x_1143_);
lean_dec_ref(v_x_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags___redArg(lean_object* v_inst_1146_, lean_object* v_inst_1147_){
_start:
{
lean_object* v_map_1148_; lean_object* v___f_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_map_1148_ = lean_ctor_get(v_inst_1147_, 0);
lean_inc_n(v_map_1148_, 2);
lean_dec_ref(v_inst_1147_);
v___f_1149_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1150_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1151_ = lean_apply_4(v_map_1148_, lean_box(0), lean_box(0), v___f_1150_, v_inst_1146_);
v___x_1152_ = lean_apply_4(v_map_1148_, lean_box(0), lean_box(0), v___f_1149_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLinkSharedFlags(lean_object* v_m_1153_, lean_object* v_inst_1154_, lean_object* v_inst_1155_){
_start:
{
lean_object* v_map_1156_; lean_object* v___f_1157_; lean_object* v___f_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_map_1156_ = lean_ctor_get(v_inst_1155_, 0);
lean_inc_n(v_map_1156_, 2);
lean_dec_ref(v_inst_1155_);
v___f_1157_ = ((lean_object*)(l_Lake_getLeanLinkSharedFlags___redArg___closed__0));
v___f_1158_ = ((lean_object*)(l_Lake_getLeanInstall___redArg___closed__0));
v___x_1159_ = lean_apply_4(v_map_1156_, lean_box(0), lean_box(0), v___f_1158_, v_inst_1154_);
v___x_1160_ = lean_apply_4(v_map_1156_, lean_box(0), lean_box(0), v___f_1157_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0(lean_object* v_x_1161_){
_start:
{
lean_object* v_lake_1162_; 
v_lake_1162_ = lean_ctor_get(v_x_1161_, 0);
lean_inc_ref(v_lake_1162_);
return v_lake_1162_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg___lam__0___boxed(lean_object* v_x_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lake_getLakeInstall___redArg___lam__0(v_x_1163_);
lean_dec_ref(v_x_1163_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___redArg(lean_object* v_inst_1166_, lean_object* v_inst_1167_){
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
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object* v_m_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v_map_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v_map_1174_ = lean_ctor_get(v_inst_1173_, 0);
lean_inc(v_map_1174_);
lean_dec_ref(v_inst_1173_);
v___f_1175_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1176_ = lean_apply_4(v_map_1174_, lean_box(0), lean_box(0), v___f_1175_, v_inst_1172_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0(lean_object* v_x_1177_){
_start:
{
lean_object* v_home_1178_; 
v_home_1178_ = lean_ctor_get(v_x_1177_, 0);
lean_inc_ref(v_home_1178_);
return v_home_1178_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg___lam__0___boxed(lean_object* v_x_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lake_getLakeHome___redArg___lam__0(v_x_1179_);
lean_dec_ref(v_x_1179_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___redArg(lean_object* v_inst_1182_, lean_object* v_inst_1183_){
_start:
{
lean_object* v_map_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_map_1184_ = lean_ctor_get(v_inst_1183_, 0);
lean_inc_n(v_map_1184_, 2);
lean_dec_ref(v_inst_1183_);
v___f_1185_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1186_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1187_ = lean_apply_4(v_map_1184_, lean_box(0), lean_box(0), v___f_1186_, v_inst_1182_);
v___x_1188_ = lean_apply_4(v_map_1184_, lean_box(0), lean_box(0), v___f_1185_, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object* v_m_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_){
_start:
{
lean_object* v_map_1192_; lean_object* v___f_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_map_1192_ = lean_ctor_get(v_inst_1191_, 0);
lean_inc_n(v_map_1192_, 2);
lean_dec_ref(v_inst_1191_);
v___f_1193_ = ((lean_object*)(l_Lake_getLakeHome___redArg___closed__0));
v___f_1194_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1195_ = lean_apply_4(v_map_1192_, lean_box(0), lean_box(0), v___f_1194_, v_inst_1190_);
v___x_1196_ = lean_apply_4(v_map_1192_, lean_box(0), lean_box(0), v___f_1193_, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0(lean_object* v_x_1197_){
_start:
{
lean_object* v_srcDir_1198_; 
v_srcDir_1198_ = lean_ctor_get(v_x_1197_, 1);
lean_inc_ref(v_srcDir_1198_);
return v_srcDir_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg___lam__0___boxed(lean_object* v_x_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lake_getLakeSrcDir___redArg___lam__0(v_x_1199_);
lean_dec_ref(v_x_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___redArg(lean_object* v_inst_1202_, lean_object* v_inst_1203_){
_start:
{
lean_object* v_map_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_map_1204_ = lean_ctor_get(v_inst_1203_, 0);
lean_inc_n(v_map_1204_, 2);
lean_dec_ref(v_inst_1203_);
v___f_1205_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1206_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1207_ = lean_apply_4(v_map_1204_, lean_box(0), lean_box(0), v___f_1206_, v_inst_1202_);
v___x_1208_ = lean_apply_4(v_map_1204_, lean_box(0), lean_box(0), v___f_1205_, v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object* v_m_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_){
_start:
{
lean_object* v_map_1212_; lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_map_1212_ = lean_ctor_get(v_inst_1211_, 0);
lean_inc_n(v_map_1212_, 2);
lean_dec_ref(v_inst_1211_);
v___f_1213_ = ((lean_object*)(l_Lake_getLakeSrcDir___redArg___closed__0));
v___f_1214_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1215_ = lean_apply_4(v_map_1212_, lean_box(0), lean_box(0), v___f_1214_, v_inst_1210_);
v___x_1216_ = lean_apply_4(v_map_1212_, lean_box(0), lean_box(0), v___f_1213_, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0(lean_object* v_x_1217_){
_start:
{
lean_object* v_libDir_1218_; 
v_libDir_1218_ = lean_ctor_get(v_x_1217_, 3);
lean_inc_ref(v_libDir_1218_);
return v_libDir_1218_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg___lam__0___boxed(lean_object* v_x_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lake_getLakeLibDir___redArg___lam__0(v_x_1219_);
lean_dec_ref(v_x_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___redArg(lean_object* v_inst_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v_map_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_map_1224_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc_n(v_map_1224_, 2);
lean_dec_ref(v_inst_1223_);
v___f_1225_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1226_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1227_ = lean_apply_4(v_map_1224_, lean_box(0), lean_box(0), v___f_1226_, v_inst_1222_);
v___x_1228_ = lean_apply_4(v_map_1224_, lean_box(0), lean_box(0), v___f_1225_, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object* v_m_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_){
_start:
{
lean_object* v_map_1232_; lean_object* v___f_1233_; lean_object* v___f_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_map_1232_ = lean_ctor_get(v_inst_1231_, 0);
lean_inc_n(v_map_1232_, 2);
lean_dec_ref(v_inst_1231_);
v___f_1233_ = ((lean_object*)(l_Lake_getLakeLibDir___redArg___closed__0));
v___f_1234_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1235_ = lean_apply_4(v_map_1232_, lean_box(0), lean_box(0), v___f_1234_, v_inst_1230_);
v___x_1236_ = lean_apply_4(v_map_1232_, lean_box(0), lean_box(0), v___f_1233_, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0(lean_object* v_x_1237_){
_start:
{
lean_object* v_lake_1238_; 
v_lake_1238_ = lean_ctor_get(v_x_1237_, 5);
lean_inc_ref(v_lake_1238_);
return v_lake_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg___lam__0___boxed(lean_object* v_x_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lake_getLake___redArg___lam__0(v_x_1239_);
lean_dec_ref(v_x_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___redArg(lean_object* v_inst_1242_, lean_object* v_inst_1243_){
_start:
{
lean_object* v_map_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_map_1244_ = lean_ctor_get(v_inst_1243_, 0);
lean_inc_n(v_map_1244_, 2);
lean_dec_ref(v_inst_1243_);
v___f_1245_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1246_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1247_ = lean_apply_4(v_map_1244_, lean_box(0), lean_box(0), v___f_1246_, v_inst_1242_);
v___x_1248_ = lean_apply_4(v_map_1244_, lean_box(0), lean_box(0), v___f_1245_, v___x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object* v_m_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_){
_start:
{
lean_object* v_map_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_map_1252_ = lean_ctor_get(v_inst_1251_, 0);
lean_inc_n(v_map_1252_, 2);
lean_dec_ref(v_inst_1251_);
v___f_1253_ = ((lean_object*)(l_Lake_getLake___redArg___closed__0));
v___f_1254_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1255_ = lean_apply_4(v_map_1252_, lean_box(0), lean_box(0), v___f_1254_, v_inst_1250_);
v___x_1256_ = lean_apply_4(v_map_1252_, lean_box(0), lean_box(0), v___f_1253_, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib___redArg___lam__0(lean_object* v_x_1257_){
_start:
{
lean_object* v_sharedDynlib_1258_; 
v_sharedDynlib_1258_ = lean_ctor_get(v_x_1257_, 4);
lean_inc_ref(v_sharedDynlib_1258_);
return v_sharedDynlib_1258_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib___redArg___lam__0___boxed(lean_object* v_x_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lake_getLakeSharedDynlib___redArg___lam__0(v_x_1259_);
lean_dec_ref(v_x_1259_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib___redArg(lean_object* v_inst_1262_, lean_object* v_inst_1263_){
_start:
{
lean_object* v_map_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_map_1264_ = lean_ctor_get(v_inst_1263_, 0);
lean_inc_n(v_map_1264_, 2);
lean_dec_ref(v_inst_1263_);
v___f_1265_ = ((lean_object*)(l_Lake_getLakeSharedDynlib___redArg___closed__0));
v___f_1266_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1267_ = lean_apply_4(v_map_1264_, lean_box(0), lean_box(0), v___f_1266_, v_inst_1262_);
v___x_1268_ = lean_apply_4(v_map_1264_, lean_box(0), lean_box(0), v___f_1265_, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSharedDynlib(lean_object* v_m_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_){
_start:
{
lean_object* v_map_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_map_1272_ = lean_ctor_get(v_inst_1271_, 0);
lean_inc_n(v_map_1272_, 2);
lean_dec_ref(v_inst_1271_);
v___f_1273_ = ((lean_object*)(l_Lake_getLakeSharedDynlib___redArg___closed__0));
v___f_1274_ = ((lean_object*)(l_Lake_getLakeInstall___redArg___closed__0));
v___x_1275_ = lean_apply_4(v_map_1272_, lean_box(0), lean_box(0), v___f_1274_, v_inst_1270_);
v___x_1276_ = lean_apply_4(v_map_1272_, lean_box(0), lean_box(0), v___f_1273_, v___x_1275_);
return v___x_1276_;
}
}
lean_object* runtime_initialize_Lake_Config_Workspace(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Monad(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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

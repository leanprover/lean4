// Lean compiler output
// Module: Lake.Config.Monad
// Imports: Init Lake.Config.Context Lake.Config.Workspace
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
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanAr___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getLeanSrcPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getLeanPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLean___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object*);
static lean_object* l_Lake_getLake___rarg___closed__1;
static lean_object* l_Lake_getLeanc___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Context_workspace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanAr___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath(lean_object*);
lean_object* l_Lake_Env_leanPath___boxed(lean_object*);
lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object*);
static lean_object* l_Lake_getLeanLibDir___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object*);
static lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___closed__1;
static lean_object* l_Lake_getLeanSysroot___rarg___closed__1;
static lean_object* l_Lake_getElanToolchain___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object*);
static lean_object* l_Lake_getNoCache___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTryCache___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanAr___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_getLeanSharedLib___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getRootPackage___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getAugmentedLeanSrcPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLean___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTryCache___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLean___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getLeanCc_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_getEnvLeanPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanPath___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___rarg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_getLakeSrcDir___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLakeContext___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanc___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getEnvSharedLibPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getNoCache___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getNoCache___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getRootPackage(lean_object*);
lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___rarg___lambda__1(lean_object*);
static lean_object* l_Lake_getEnvLeanSrcPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___rarg(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getLeanCc___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getElanHome_x3f___rarg___closed__1;
static lean_object* l_Lake_getLakeLibDir___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___rarg___lambda__1(lean_object*);
static lean_object* l_Lake_getLeanIncludeDir___rarg___closed__1;
static lean_object* l_Lake_getRootPackage___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object*);
LEAN_EXPORT uint8_t l_Lake_getTryCache___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_getLean___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkLakeContext(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoCache___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Context_workspace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object*);
static lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___closed__1;
static lean_object* l_Lake_getTryCache___rarg___closed__1;
lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findModule_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanc___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTryCache___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_getLeanInstall___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___rarg(lean_object*, lean_object*);
lean_object* l_Lake_LeanInstall_leanCc_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanCc___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run___rarg(lean_object*, lean_object*);
lean_object* l_Lake_Env_toolchain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT(lean_object*, lean_object*);
static lean_object* l_Lake_getLakeHome___rarg___closed__1;
static lean_object* l_Lake_getLakeInstall___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___rarg___lambda__1(lean_object*);
lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object*);
lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLake___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath(lean_object*);
static lean_object* l_Lake_getElanInstall_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object*);
static lean_object* l_Lake_getLeanAr___rarg___closed__1;
static lean_object* l_Lake_getLeanSystemLibDir___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f(lean_object*);
static lean_object* l_Lake_getElan_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanc___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLake___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoCache(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getRootPackage___rarg___lambda__1(lean_object*);
lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_getAugmentedEnv___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___rarg___lambda__1(lean_object*);
lean_object* l_Lake_Workspace_leanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object*);
static lean_object* l_Lake_getPkgUrlMap___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getRootPackage___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f(lean_object*);
lean_object* l_Lake_Env_sharedLibPath(lean_object*);
static lean_object* l_Lake_getSharedLibPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLake___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_findPackage_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSrcPath___boxed(lean_object*);
static lean_object* l_Lake_getLeanSrcDir___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeHome___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeHome___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_getAugmentedSharedLibPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeHome___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoCache___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___rarg(lean_object*);
static lean_object* l_Lake_getAugmentedLeanPath___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeEnvT_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_LakeEnvT_run___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLakeContext(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mkLakeContext___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_mkLakeContext(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_runLakeT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_Workspace_runLakeT___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Context_workspace(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Context_workspace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Context_workspace(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getRootPackage___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getRootPackage___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getRootPackage___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getRootPackage___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getRootPackage___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getRootPackage___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_Workspace_findPackage_x3f___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_findPackage_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_findPackage_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_Workspace_findModule_x3f___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_findModule_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_findModule_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_Workspace_findLeanExe_x3f___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanExe_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_findLeanExe_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_Workspace_findLeanLib_x3f___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_findLeanLib_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_findLeanLib_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_Workspace_findExternLib_x3f___boxed), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_findExternLib_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_findExternLib_x3f___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_leanPath___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanSrcPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_leanSrcPath___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanSrcPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanSrcPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getSharedLibPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_sharedLibPath___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getSharedLibPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getSharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getSharedLibPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getAugmentedLeanPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_augmentedLeanPath___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getAugmentedLeanPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getAugmentedLeanPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getAugmentedLeanSrcPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_augmentedLeanSrcPath___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getAugmentedLeanSrcPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedLeanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getAugmentedLeanSrcPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getAugmentedSharedLibPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_augmentedSharedLibPath), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getAugmentedSharedLibPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedSharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getAugmentedSharedLibPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getAugmentedEnv___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Workspace_augmentedEnvVars), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getAugmentedEnv___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getAugmentedEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getAugmentedEnv___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLakeEnv___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeEnv___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLakeEnv___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoCache___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
return x_2;
}
}
static lean_object* _init_l_Lake_getNoCache___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getNoCache___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lake_getNoCache___rarg___closed__1;
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getNoCache___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_getNoCache___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoCache___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_getNoCache___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_getTryCache___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
static lean_object* _init_l_Lake_getTryCache___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getTryCache___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lake_getTryCache___rarg___closed__1;
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getTryCache___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_getTryCache___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getTryCache___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_getTryCache___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getPkgUrlMap___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getPkgUrlMap___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getPkgUrlMap___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getPkgUrlMap___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getPkgUrlMap___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getPkgUrlMap___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_getElanToolchain___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Env_toolchain___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getElanToolchain___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanToolchain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getElanToolchain___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getEnvLeanPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Env_leanPath___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getEnvLeanPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getEnvLeanPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getEnvLeanSrcPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Env_leanSrcPath___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getEnvLeanSrcPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvLeanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getEnvLeanSrcPath___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_getEnvSharedLibPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Env_sharedLibPath), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getEnvSharedLibPath___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getEnvSharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getEnvSharedLibPath___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getElanInstall_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getElanInstall_x3f___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getElanInstall_x3f___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getElanInstall_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanInstall_x3f___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getElanInstall_x3f___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___rarg___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lake_getElanHome_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getElanHome_x3f___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getElanInstall_x3f___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getElanHome_x3f___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getElanHome_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getElanHome_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___rarg___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lake_getElan_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getElan_x3f___rarg___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getElanInstall_x3f___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getElan_x3f___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getElan_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getElan_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanInstall___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanInstall___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanInstall___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanInstall___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanInstall___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanSysroot___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanSysroot___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanSysroot___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanSysroot___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSysroot___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanSysroot___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanSrcDir___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanSrcDir___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanSrcDir___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanSrcDir___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSrcDir___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanSrcDir___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanLibDir___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanLibDir___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanLibDir___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanLibDir___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanLibDir___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanLibDir___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanIncludeDir___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanIncludeDir___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanIncludeDir___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanIncludeDir___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanIncludeDir___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanIncludeDir___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanSystemLibDir___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanSystemLibDir___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanSystemLibDir___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanSystemLibDir___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSystemLibDir___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanSystemLibDir___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 7);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLean___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLean___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLean___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLean___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLean___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLean___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 8);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanc___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanc___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanc___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanc___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanc___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanc___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 9);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanSharedLib___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanSharedLib___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanSharedLib___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanSharedLib___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanSharedLib___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanSharedLib___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 11);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanAr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanAr___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanAr___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanAr___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanAr___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanAr___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 12);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanCc___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanCc___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanCc___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanCc___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanCc___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanCc_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanInstall_leanCc_x3f___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLeanInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLeanCc_x3f___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanCc_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanCc_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLakeInstall___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLakeInstall___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLakeInstall___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLakeInstall___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeInstall___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLakeInstall___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLakeHome___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLakeHome___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLakeInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLakeHome___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLakeHome___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeHome___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLakeHome___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLakeSrcDir___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLakeSrcDir___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLakeInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLakeSrcDir___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLakeSrcDir___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeSrcDir___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLakeSrcDir___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLakeLibDir___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLakeLibDir___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLakeInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLakeLibDir___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLakeLibDir___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLakeLibDir___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLakeLibDir___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLake___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLake___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_getLakeInstall___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_1);
x_6 = l_Lake_getLake___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLake___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLake___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLake___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Context(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Context(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___closed__1 = _init_l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___closed__1();
lean_mark_persistent(l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___rarg___closed__1);
l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___closed__1 = _init_l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___closed__1();
lean_mark_persistent(l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___rarg___closed__1);
l_Lake_getRootPackage___rarg___closed__1 = _init_l_Lake_getRootPackage___rarg___closed__1();
lean_mark_persistent(l_Lake_getRootPackage___rarg___closed__1);
l_Lake_getLeanPath___rarg___closed__1 = _init_l_Lake_getLeanPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanPath___rarg___closed__1);
l_Lake_getLeanSrcPath___rarg___closed__1 = _init_l_Lake_getLeanSrcPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanSrcPath___rarg___closed__1);
l_Lake_getSharedLibPath___rarg___closed__1 = _init_l_Lake_getSharedLibPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getSharedLibPath___rarg___closed__1);
l_Lake_getAugmentedLeanPath___rarg___closed__1 = _init_l_Lake_getAugmentedLeanPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getAugmentedLeanPath___rarg___closed__1);
l_Lake_getAugmentedLeanSrcPath___rarg___closed__1 = _init_l_Lake_getAugmentedLeanSrcPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getAugmentedLeanSrcPath___rarg___closed__1);
l_Lake_getAugmentedSharedLibPath___rarg___closed__1 = _init_l_Lake_getAugmentedSharedLibPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getAugmentedSharedLibPath___rarg___closed__1);
l_Lake_getAugmentedEnv___rarg___closed__1 = _init_l_Lake_getAugmentedEnv___rarg___closed__1();
lean_mark_persistent(l_Lake_getAugmentedEnv___rarg___closed__1);
l_Lake_getNoCache___rarg___closed__1 = _init_l_Lake_getNoCache___rarg___closed__1();
lean_mark_persistent(l_Lake_getNoCache___rarg___closed__1);
l_Lake_getTryCache___rarg___closed__1 = _init_l_Lake_getTryCache___rarg___closed__1();
lean_mark_persistent(l_Lake_getTryCache___rarg___closed__1);
l_Lake_getPkgUrlMap___rarg___closed__1 = _init_l_Lake_getPkgUrlMap___rarg___closed__1();
lean_mark_persistent(l_Lake_getPkgUrlMap___rarg___closed__1);
l_Lake_getElanToolchain___rarg___closed__1 = _init_l_Lake_getElanToolchain___rarg___closed__1();
lean_mark_persistent(l_Lake_getElanToolchain___rarg___closed__1);
l_Lake_getEnvLeanPath___rarg___closed__1 = _init_l_Lake_getEnvLeanPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getEnvLeanPath___rarg___closed__1);
l_Lake_getEnvLeanSrcPath___rarg___closed__1 = _init_l_Lake_getEnvLeanSrcPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getEnvLeanSrcPath___rarg___closed__1);
l_Lake_getEnvSharedLibPath___rarg___closed__1 = _init_l_Lake_getEnvSharedLibPath___rarg___closed__1();
lean_mark_persistent(l_Lake_getEnvSharedLibPath___rarg___closed__1);
l_Lake_getElanInstall_x3f___rarg___closed__1 = _init_l_Lake_getElanInstall_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_getElanInstall_x3f___rarg___closed__1);
l_Lake_getElanHome_x3f___rarg___closed__1 = _init_l_Lake_getElanHome_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_getElanHome_x3f___rarg___closed__1);
l_Lake_getElan_x3f___rarg___closed__1 = _init_l_Lake_getElan_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_getElan_x3f___rarg___closed__1);
l_Lake_getLeanInstall___rarg___closed__1 = _init_l_Lake_getLeanInstall___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanInstall___rarg___closed__1);
l_Lake_getLeanSysroot___rarg___closed__1 = _init_l_Lake_getLeanSysroot___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanSysroot___rarg___closed__1);
l_Lake_getLeanSrcDir___rarg___closed__1 = _init_l_Lake_getLeanSrcDir___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanSrcDir___rarg___closed__1);
l_Lake_getLeanLibDir___rarg___closed__1 = _init_l_Lake_getLeanLibDir___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanLibDir___rarg___closed__1);
l_Lake_getLeanIncludeDir___rarg___closed__1 = _init_l_Lake_getLeanIncludeDir___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanIncludeDir___rarg___closed__1);
l_Lake_getLeanSystemLibDir___rarg___closed__1 = _init_l_Lake_getLeanSystemLibDir___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanSystemLibDir___rarg___closed__1);
l_Lake_getLean___rarg___closed__1 = _init_l_Lake_getLean___rarg___closed__1();
lean_mark_persistent(l_Lake_getLean___rarg___closed__1);
l_Lake_getLeanc___rarg___closed__1 = _init_l_Lake_getLeanc___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanc___rarg___closed__1);
l_Lake_getLeanSharedLib___rarg___closed__1 = _init_l_Lake_getLeanSharedLib___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanSharedLib___rarg___closed__1);
l_Lake_getLeanAr___rarg___closed__1 = _init_l_Lake_getLeanAr___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanAr___rarg___closed__1);
l_Lake_getLeanCc___rarg___closed__1 = _init_l_Lake_getLeanCc___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanCc___rarg___closed__1);
l_Lake_getLeanCc_x3f___rarg___closed__1 = _init_l_Lake_getLeanCc_x3f___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanCc_x3f___rarg___closed__1);
l_Lake_getLakeInstall___rarg___closed__1 = _init_l_Lake_getLakeInstall___rarg___closed__1();
lean_mark_persistent(l_Lake_getLakeInstall___rarg___closed__1);
l_Lake_getLakeHome___rarg___closed__1 = _init_l_Lake_getLakeHome___rarg___closed__1();
lean_mark_persistent(l_Lake_getLakeHome___rarg___closed__1);
l_Lake_getLakeSrcDir___rarg___closed__1 = _init_l_Lake_getLakeSrcDir___rarg___closed__1();
lean_mark_persistent(l_Lake_getLakeSrcDir___rarg___closed__1);
l_Lake_getLakeLibDir___rarg___closed__1 = _init_l_Lake_getLakeLibDir___rarg___closed__1();
lean_mark_persistent(l_Lake_getLakeLibDir___rarg___closed__1);
l_Lake_getLake___rarg___closed__1 = _init_l_Lake_getLake___rarg___closed__1();
lean_mark_persistent(l_Lake_getLake___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

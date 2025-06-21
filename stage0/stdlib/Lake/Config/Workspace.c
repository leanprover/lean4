// Lean compiler output
// Module: Lake.Config.Workspace
// Imports: Lean.Util.Paths Lake.Config.FacetConfig Lake.Config.TargetConfig Lake.Config.Env Lake.Util.Log
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
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findExternLib_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_findTargetConfig_x3f___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_clean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object*);
static lean_object* l_Lake_OpaqueWorkspace_instCoeWorkspace___closed__0;
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lake_Workspace_isLocalModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_LeanInstall_sharedLibPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
extern lean_object* l_Lake_Package_keyword;
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instCoeWorkspace__1;
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanExe_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Env_leanSrcPath(lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lake_Workspace_isLocalModule_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_findScript_x3f___closed__0;
uint8_t l_Lake_Package_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_clean_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_Package_findTargetModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object*, lean_object*);
static lean_object* l_Lake_OpaqueWorkspace_instCoeWorkspace__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Package_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModule_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanPath_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_binPath_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Package_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeGet(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object*);
lean_object* l_Lake_Package_findTargetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lake_Workspace_isBuildableModule_spec__0(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeMk(lean_object*);
static lean_object* l_Lake_Workspace_findPackage_x3f___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object*);
static lean_object* l_Lake_Workspace_augmentedEnvVars___closed__3;
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_binPath_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object*);
lean_object* l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeMk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instCoeWorkspace;
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeGet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Workspace_augmentedEnvVars___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_sharedLibPath_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object*);
extern lean_object* l_Lake_sharedLibPathEnvVar;
static lean_object* l_Lake_Workspace_augmentedEnvVars___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_findLeanLib_x3f___closed__0;
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lake_Env_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_packageOverridesFile___closed__0;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Package_isBuildableModule(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(lean_object*);
extern lean_object* l_Lake_Module_keyword;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object*);
static lean_object* l_Lake_Workspace_findModule_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findScript_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object*);
lean_object* l_Lake_Env_path(lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
static lean_object* l_Lake_Workspace_augmentedEnvVars___closed__1;
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Workspace_relLakeDir___closed__0;
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeMk(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeMk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaqueWorkspace_unsafeMk(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OpaqueWorkspace_instCoeWorkspace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_OpaqueWorkspace_unsafeMk___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OpaqueWorkspace_instCoeWorkspace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OpaqueWorkspace_instCoeWorkspace___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeGet(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_unsafeGet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaqueWorkspace_unsafeGet(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OpaqueWorkspace_instCoeWorkspace__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_OpaqueWorkspace_unsafeGet___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OpaqueWorkspace_instCoeWorkspace__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OpaqueWorkspace_instCoeWorkspace__1___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_dir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_dir(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_config___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_config(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Workspace_relLakeDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lake", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_relLakeDir___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relLakeDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_relLakeDir(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_lakeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_Workspace_relLakeDir___closed__0;
x_5 = l_Lake_joinRelative(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_relPkgsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_System_FilePath_normalize(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_pkgsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_System_FilePath_normalize(x_5);
x_7 = l_Lake_joinRelative(x_4, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Lean_LeanOptions_ofArray(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_leanOptions(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 4);
x_7 = l_Lean_LeanOptions_ofArray(x_5);
x_8 = l_Lean_LeanOptions_appendArray(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_serverOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_serverOptions(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_manifestFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 6);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lake_joinRelative(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Workspace_packageOverridesFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package-overrides.json", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_packageOverridesFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_Workspace_relLakeDir___closed__0;
x_5 = l_Lake_joinRelative(x_3, x_4);
x_6 = l_Lake_Workspace_packageOverridesFile___closed__0;
x_7 = l_Lake_joinRelative(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackage(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_array_push(x_4, x_1);
x_8 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_5, x_6, x_1);
lean_ctor_set(x_2, 4, x_8);
lean_ctor_set(x_2, 3, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
x_13 = lean_ctor_get(x_2, 4);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_array_push(x_12, x_1);
x_17 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_13, x_15, x_1);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_14);
return x_18;
}
}
}
static lean_object* _init_l_Lake_Workspace_findPackage_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackage_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lake_Workspace_findPackage_x3f___closed__0;
x_5 = l_Lake_RBNode_dFind___redArg(x_4, x_3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findScript_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_ctor_get(x_9, 13);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
{
size_t _tmp_5 = x_13;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_findScript_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findScript_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findScript_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findScript_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findScript_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findScript_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findScript_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lake_Workspace_isLocalModule_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lake_Package_isLocalModule(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isLocalModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lake_Workspace_isLocalModule_spec__0(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lake_Workspace_isLocalModule_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lake_Workspace_isLocalModule_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isLocalModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Workspace_isLocalModule(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lake_Workspace_isBuildableModule_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lake_Package_isBuildableModule(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Workspace_isBuildableModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lake_Workspace_isBuildableModule_spec__0(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lake_Workspace_isBuildableModule_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lake_Workspace_isBuildableModule_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_isBuildableModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Workspace_isBuildableModule(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModule_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_4, x_6);
lean_inc(x_1);
x_10 = l_Lake_Package_findModule_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_6, x_11);
{
size_t _tmp_5 = x_12;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_findModule_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findModule_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModule_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModule_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModule_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModule_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findModule_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetModule_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_4, x_6);
lean_inc(x_1);
x_10 = l_Lake_Package_findTargetModule_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_6, x_11);
{
size_t _tmp_5 = x_12;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findModule_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetModule_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetModule_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetModule_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetModule_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findTargetModule_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModuleBySrc_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_4, x_6);
lean_inc(x_1);
x_10 = l_Lake_Package_findModuleBySrc_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_6, x_11);
{
size_t _tmp_5 = x_12;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findModule_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModuleBySrc_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findModuleBySrc_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleBySrc_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findModuleBySrc_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_6);
x_15 = l_Lake_Package_findTargetDecl_x3f(x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1;
x_22 = lean_name_eq(x_19, x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
lean_free_object(x_15);
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 3);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1;
x_31 = lean_name_eq(x_28, x_30);
lean_dec(x_28);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
}
}
static lean_object* _init_l_Lake_Workspace_findLeanLib_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findLeanLib_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanLib_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findLeanLib_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanExe_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_6);
x_15 = l_Lake_Package_findTargetDecl_x3f(x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lake_LeanExe_keyword;
x_22 = lean_name_eq(x_19, x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
lean_free_object(x_15);
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 3);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lake_LeanExe_keyword;
x_31 = lean_name_eq(x_28, x_30);
lean_dec(x_28);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findLeanLib_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanExe_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanExe_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanExe_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLeanExe_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findLeanExe_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findExternLib_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_6);
x_15 = l_Lake_Package_findTargetDecl_x3f(x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lake_ExternLib_keyword;
x_22 = lean_name_eq(x_19, x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
lean_free_object(x_15);
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 3);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lake_ExternLib_keyword;
x_31 = lean_name_eq(x_28, x_30);
lean_dec(x_28);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_14);
x_8 = x_2;
goto block_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
x_6 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findLeanLib_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findExternLib_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findExternLib_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findExternLib_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findExternLib_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findExternLib_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___Lake_Workspace_findTargetConfig_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Functor_mapRev___at___Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_4, x_6);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lake_Package_findTargetConfig_x3f(x_1, x_9);
lean_dec(x_9);
x_12 = l_Functor_mapRev___at___Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
{
size_t _tmp_5 = x_14;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
static lean_object* _init_l_Lake_Workspace_findTargetConfig_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findTargetConfig_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetConfig_x3f_spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetConfig_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findTargetConfig_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_4, x_6);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lake_Package_findTargetDecl_x3f(x_1, x_9);
lean_dec(x_9);
x_12 = l_Functor_mapRev___at___Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
{
size_t _tmp_5 = x_14;
lean_object* _tmp_6 = x_2;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_box(0);
x_5 = l_Lake_Workspace_findTargetConfig_x3f___closed__0;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0(x_1, x_5, x_4, x_3, x_6, x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findTargetDecl_x3f_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findTargetDecl_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findTargetDecl_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_5, x_1, x_2);
lean_ctor_set(x_3, 5, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_ctor_get(x_3, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_13 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_12, x_1, x_2);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 5);
x_4 = l_Lake_RBNode_dFind___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findFacetConfig_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findFacetConfig_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addModuleFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_addFacetConfig(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findFacetConfig_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lake_Module_keyword;
x_7 = l_Lake_FacetConfig_toKind_x3f___redArg(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findModuleFacetConfig_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addPackageFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_addFacetConfig(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findFacetConfig_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lake_Package_keyword;
x_7 = l_Lake_FacetConfig_toKind_x3f___redArg(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findPackageFacetConfig_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_addLibraryFacetConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Workspace_addFacetConfig(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findFacetConfig_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1;
x_7 = l_Lake_FacetConfig_toKind_x3f___redArg(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_findLibraryFacetConfig_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_binPath_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 6);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 9);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_System_FilePath_normalize(x_9);
x_12 = l_Lake_joinRelative(x_8, x_11);
lean_dec(x_11);
x_13 = l_System_FilePath_normalize(x_10);
x_14 = l_Lake_joinRelative(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_binPath_spec__0(x_2, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_binPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_binPath_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_binPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_binPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanPath_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 6);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 7);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_System_FilePath_normalize(x_9);
x_12 = l_Lake_joinRelative(x_8, x_11);
lean_dec(x_11);
x_13 = l_System_FilePath_normalize(x_10);
x_14 = l_Lake_joinRelative(x_12, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanPath_spec__0(x_2, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanPath_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_leanPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1;
x_13 = lean_name_eq(x_10, x_12);
lean_dec(x_10);
if (x_13 == 0)
{
lean_dec(x_11);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 5);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = l_System_FilePath_normalize(x_17);
x_20 = l_Lake_joinRelative(x_16, x_19);
lean_dec(x_19);
x_21 = l_Lake_joinRelative(x_20, x_18);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
x_3 = x_8;
x_5 = x_22;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 10);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_17 = 0;
x_18 = l_Array_foldrMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__0(x_11, x_12, x_16, x_17, x_4);
lean_dec(x_12);
x_5 = x_18;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 10);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_17 = 0;
x_18 = l_Array_foldrMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__0(x_11, x_12, x_16, x_17, x_4);
lean_dec(x_12);
x_5 = x_18;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1_spec__1(x_1, x_7, x_3, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1(x_2, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_leanSrcPath_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_leanSrcPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_leanSrcPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_sharedLibPath_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 8);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_System_FilePath_normalize(x_11);
x_14 = l_Lake_joinRelative(x_10, x_13);
lean_dec(x_13);
x_15 = l_System_FilePath_normalize(x_12);
x_16 = l_Lake_joinRelative(x_14, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_2 = x_7;
x_4 = x_17;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_box(0);
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = 0;
x_9 = l_Array_foldrMUnsafe_fold___at___Lake_Workspace_sharedLibPath_spec__0(x_2, x_7, x_8, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lake_Workspace_sharedLibPath_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lake_Workspace_sharedLibPath_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_sharedLibPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_sharedLibPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lake_Workspace_binPath(x_1);
x_5 = l_Lake_Env_path(x_3);
x_6 = l_List_appendTR___redArg(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lake_Workspace_binPath(x_1);
x_9 = l_Lake_Workspace_sharedLibPath(x_1);
x_10 = l_List_appendTR___redArg(x_8, x_9);
x_11 = l_Lake_Env_path(x_7);
x_12 = l_List_appendTR___redArg(x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_augmentedPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lake_Workspace_leanPath(x_1);
x_4 = l_Lake_Env_leanPath(x_2);
x_5 = l_List_appendTR___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_augmentedLeanPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lake_Workspace_leanSrcPath(x_1);
x_4 = l_Lake_Env_leanSrcPath(x_2);
x_5 = l_List_appendTR___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedLeanSrcPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Workspace_augmentedLeanSrcPath(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedSharedLibPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 9);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lake_LeanInstall_sharedLibPath(x_3);
lean_dec(x_3);
x_6 = l_Lake_Workspace_sharedLibPath(x_1);
lean_dec(x_1);
x_7 = l_List_appendTR___redArg(x_5, x_6);
x_8 = l_List_appendTR___redArg(x_7, x_4);
return x_8;
}
}
static lean_object* _init_l_Lake_Workspace_augmentedEnvVars___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_augmentedEnvVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_augmentedEnvVars___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PATH", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Workspace_augmentedEnvVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lake_Env_baseVars(x_2);
x_4 = l_Lake_Workspace_augmentedEnvVars___closed__0;
x_5 = l_Lake_Workspace_augmentedLeanPath(x_1);
x_6 = l_System_SearchPath_toString(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_Workspace_augmentedEnvVars___closed__1;
x_10 = l_Lake_Workspace_augmentedLeanSrcPath(x_1);
x_11 = l_System_SearchPath_toString(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_Workspace_augmentedEnvVars___closed__2;
x_15 = l_Lake_Workspace_augmentedPath(x_1);
x_16 = l_System_SearchPath_toString(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_Workspace_augmentedEnvVars___closed__3;
x_20 = lean_array_push(x_19, x_8);
x_21 = lean_array_push(x_20, x_13);
x_22 = lean_array_push(x_21, x_18);
x_23 = l_Array_append___redArg(x_3, x_22);
lean_dec(x_22);
x_24 = l_System_Platform_isWindows;
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Lake_sharedLibPathEnvVar;
x_26 = l_Lake_Workspace_augmentedSharedLibPath(x_1);
x_27 = l_System_SearchPath_toString(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_23, x_29);
return x_30;
}
else
{
lean_dec(x_1);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_clean_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lake_Package_clean(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_clean_spec__0(x_3, x_11, x_12, x_6, x_2);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_clean_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_clean_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Workspace_clean___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Workspace_clean(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_TargetConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_FacetConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_TargetConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Env(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_OpaqueWorkspace_instCoeWorkspace___closed__0 = _init_l_Lake_OpaqueWorkspace_instCoeWorkspace___closed__0();
lean_mark_persistent(l_Lake_OpaqueWorkspace_instCoeWorkspace___closed__0);
l_Lake_OpaqueWorkspace_instCoeWorkspace = _init_l_Lake_OpaqueWorkspace_instCoeWorkspace();
lean_mark_persistent(l_Lake_OpaqueWorkspace_instCoeWorkspace);
l_Lake_OpaqueWorkspace_instCoeWorkspace__1___closed__0 = _init_l_Lake_OpaqueWorkspace_instCoeWorkspace__1___closed__0();
lean_mark_persistent(l_Lake_OpaqueWorkspace_instCoeWorkspace__1___closed__0);
l_Lake_OpaqueWorkspace_instCoeWorkspace__1 = _init_l_Lake_OpaqueWorkspace_instCoeWorkspace__1();
lean_mark_persistent(l_Lake_OpaqueWorkspace_instCoeWorkspace__1);
l_Lake_Workspace_relLakeDir___closed__0 = _init_l_Lake_Workspace_relLakeDir___closed__0();
lean_mark_persistent(l_Lake_Workspace_relLakeDir___closed__0);
l_Lake_Workspace_packageOverridesFile___closed__0 = _init_l_Lake_Workspace_packageOverridesFile___closed__0();
lean_mark_persistent(l_Lake_Workspace_packageOverridesFile___closed__0);
l_Lake_Workspace_findPackage_x3f___closed__0 = _init_l_Lake_Workspace_findPackage_x3f___closed__0();
lean_mark_persistent(l_Lake_Workspace_findPackage_x3f___closed__0);
l_Lake_Workspace_findScript_x3f___closed__0 = _init_l_Lake_Workspace_findScript_x3f___closed__0();
lean_mark_persistent(l_Lake_Workspace_findScript_x3f___closed__0);
l_Lake_Workspace_findModule_x3f___closed__0 = _init_l_Lake_Workspace_findModule_x3f___closed__0();
lean_mark_persistent(l_Lake_Workspace_findModule_x3f___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lake_Workspace_findLeanLib_x3f_spec__0___closed__1);
l_Lake_Workspace_findLeanLib_x3f___closed__0 = _init_l_Lake_Workspace_findLeanLib_x3f___closed__0();
lean_mark_persistent(l_Lake_Workspace_findLeanLib_x3f___closed__0);
l_Lake_Workspace_findTargetConfig_x3f___closed__0 = _init_l_Lake_Workspace_findTargetConfig_x3f___closed__0();
lean_mark_persistent(l_Lake_Workspace_findTargetConfig_x3f___closed__0);
l_Lake_Workspace_augmentedEnvVars___closed__0 = _init_l_Lake_Workspace_augmentedEnvVars___closed__0();
lean_mark_persistent(l_Lake_Workspace_augmentedEnvVars___closed__0);
l_Lake_Workspace_augmentedEnvVars___closed__1 = _init_l_Lake_Workspace_augmentedEnvVars___closed__1();
lean_mark_persistent(l_Lake_Workspace_augmentedEnvVars___closed__1);
l_Lake_Workspace_augmentedEnvVars___closed__2 = _init_l_Lake_Workspace_augmentedEnvVars___closed__2();
lean_mark_persistent(l_Lake_Workspace_augmentedEnvVars___closed__2);
l_Lake_Workspace_augmentedEnvVars___closed__3 = _init_l_Lake_Workspace_augmentedEnvVars___closed__3();
lean_mark_persistent(l_Lake_Workspace_augmentedEnvVars___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

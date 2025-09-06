// Lean compiler output
// Module: Lake.Config.Package
// Imports: Lake.Config.Cache Lake.Config.Script Lake.Config.ConfigDecl Lake.Config.Dependency Lake.Config.PackageConfig Lake.Util.FilePath Lake.Util.OrdHashSet Lake.Util.Name Lake.Util.OpaqueType
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
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook___lam__0____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isBuildableModule_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lake_instImpl___closed__0____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object*, lean_object*);
static lean_object* l_Lake_defaultPackage___closed__2____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lean_LeanOptions_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instBEqPackage___lam__0(lean_object*, lean_object*);
uint8_t l_Lake_LeanLibConfig_isBuildableModule___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lake_OrdPackageSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__6;
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object*, lean_object*);
static lean_object* l_Lake_Package_barrelFile___closed__0;
static lean_object* l_Lake_Package_relLicenseFiles___closed__5;
extern lean_object* l_System_defaultFilePath____x40_Init_System_FilePath_3398306____hygCtx___hyg_14_;
static lean_object* l_Lake_instImpl___closed__1____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_inputsFileIn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringPackage;
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqPackage___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object*);
static lean_object* l_Lake_OrdPackageSet_empty___closed__2;
LEAN_EXPORT lean_object* l_Lake_PostUpdateHook_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackage;
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PostUpdateHookDecl_ctorIdx___boxed(lean_object*);
static lean_object* l_Lake_instImpl___closed__2____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdPackageSet_empty;
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqPackage;
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PostUpdateHookDecl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDepPackageNPackageName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object*);
static lean_object* l_Lake_Package_relLakeDir___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_nativeLibDir(lean_object*);
static lean_object* l_Lake_defaultPackage___closed__3____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instImpl____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object*);
static lean_object* l_Lake_PackageSet_empty___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageSet_empty;
LEAN_EXPORT lean_object* l_Lake_instHashablePackage;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PostUpdateHook_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object*);
static lean_object* l_Lake_OrdPackageSet_empty___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object*);
static lean_object* l_Lake_instInhabitedPostUpdateHook___closed__0;
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instHashablePackage___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__7;
static lean_object* l_Lake_PackageSet_empty___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDepPackageNPackageName(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringPackage___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultPackage____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isBuildableModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instTypeNamePostUpdateHookDecl;
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object*);
lean_object* l_Lake_defaultPackageConfig____x40_Lake_Config_PackageConfig_3174597290____hygCtx___hyg_391_(lean_object*);
lean_object* l_Lean_LeanOptions_appendArray(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_defaultPackage___closed__1____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
static lean_object* l_Lake_defaultPackage___closed__4____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
LEAN_EXPORT lean_object* l_Lake_Package_ctorIdx___boxed(lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__8;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonPackage;
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Cache_inputsFile(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_defaultPackage___closed__0____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
LEAN_EXPORT lean_object* l_Lake_instToJsonPackage___lam__0(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lake_LeanLibConfig_isLocalModule___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageSet_empty___closed__0;
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashablePackage___lam__0(lean_object*);
static lean_object* l_Lake_Package_relLicenseFiles___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object*);
lean_object* l_Lake_OrdHashSet_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object*);
static lean_object* l_Lake_PackageSet_empty___closed__4;
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook___lam__0____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17_(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_licenseFiles___closed__0;
static lean_object* l_Lake_PackageSet_empty___closed__1;
static lean_object* l_Lake_Package_relLicenseFiles___closed__9;
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_defaultPackage___closed__0____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_() {
_start:
{
lean_object* x_1; 
x_1 = l_System_defaultFilePath____x40_Init_System_FilePath_3398306____hygCtx___hyg_14_;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultPackage___closed__1____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lake_defaultPackageConfig____x40_Lake_Config_PackageConfig_3174597290____hygCtx___hyg_391_(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_defaultPackage___closed__2____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultPackage___closed__3____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_defaultPackage___closed__4____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = l_Lake_defaultPackage___closed__3____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
x_4 = l_Lake_defaultPackage___closed__2____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
x_5 = l_Lake_defaultPackage___closed__1____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
x_6 = l_Lake_defaultPackage___closed__0____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 20, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_6);
lean_ctor_set(x_8, 6, x_6);
lean_ctor_set(x_8, 7, x_4);
lean_ctor_set(x_8, 8, x_4);
lean_ctor_set(x_8, 9, x_3);
lean_ctor_set(x_8, 10, x_3);
lean_ctor_set(x_8, 11, x_2);
lean_ctor_set(x_8, 12, x_3);
lean_ctor_set(x_8, 13, x_2);
lean_ctor_set(x_8, 14, x_3);
lean_ctor_set(x_8, 15, x_3);
lean_ctor_set(x_8, 16, x_4);
lean_ctor_set(x_8, 17, x_4);
lean_ctor_set(x_8, 18, x_4);
lean_ctor_set(x_8, 19, x_1);
return x_8;
}
}
static lean_object* _init_l_Lake_defaultPackage____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultPackage___closed__4____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultPackage____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashablePackage___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Name_hash___override(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instHashablePackage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashablePackage___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_instHashablePackage___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instBEqPackage___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instBEqPackage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqPackage___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instBEqPackage___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lake_PackageSet_empty___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageSet_empty___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageSet_empty___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageSet_empty___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageSet_empty___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageSet_empty___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdPackageSet_empty___closed__1;
x_2 = l_Lake_OrdPackageSet_empty___closed__0;
x_3 = l_Lake_OrdHashSet_empty(lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdPackageSet_empty___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonPackage___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = 1;
x_4 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instToJsonPackage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonPackage___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringPackage___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instToStringPackage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToStringPackage___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_NPackage_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instCoeOutNPackagePackage___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeOutNPackagePackage___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeOutNPackagePackage(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepPackageNPackageName(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepPackageNPackageName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeDepPackageNPackageName(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PostUpdateHook_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PostUpdateHook_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PostUpdateHook_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook___lam__0____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_defaultPostUpdateHook___lam__0____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17____boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook___lam__0____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_defaultPostUpdateHook___lam__0____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17_(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_defaultPostUpdateHook____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultPostUpdateHook____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedPostUpdateHook___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_defaultPostUpdateHook___lam__0____x40_Lake_Config_Package_1490217461____hygCtx___hyg_17____boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedPostUpdateHook___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedPostUpdateHook(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeMk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoeGet(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PostUpdateHookDecl_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PostUpdateHookDecl_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PostUpdateHookDecl_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instImpl___closed__0____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_instImpl___closed__1____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PostUpdateHookDecl", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_instImpl___closed__2____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instImpl___closed__1____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
x_2 = l_Lake_instImpl___closed__0____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instImpl____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instImpl___closed__2____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
return x_1;
}
}
static lean_object* _init_l_Lake_instTypeNamePostUpdateHookDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instImpl____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_bootstrap(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*26);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_bootstrap___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_bootstrap(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 17);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_version___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_version(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 18);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_versionTags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_versionTags(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 19);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_description___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_description(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 20);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_keywords___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_keywords(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 21);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_homepage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_homepage(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_reservoir(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_reservoir___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_reservoir(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 22);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_license___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_license(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_normalize(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_relLicenseFiles___closed__1;
x_2 = l_Lake_Package_relLicenseFiles___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_Package_relLicenseFiles___closed__5;
x_2 = l_Lake_Package_relLicenseFiles___closed__4;
x_3 = l_Lake_Package_relLicenseFiles___closed__3;
x_4 = l_Lake_Package_relLicenseFiles___closed__2;
x_5 = l_Lake_Package_relLicenseFiles___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Package_relLicenseFiles___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_relLicenseFiles___closed__6;
x_2 = l_Lake_Package_relLicenseFiles___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLicenseFiles(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 23);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_Package_relLicenseFiles___lam__0), 1, 0);
x_5 = l_Lake_Package_relLicenseFiles___closed__9;
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_5, x_4, x_6, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_System_FilePath_normalize(x_2);
x_4 = l_Lake_joinRelative(x_1, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_licenseFiles___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Package_relLicenseFiles___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_licenseFiles(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; size_t x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 23);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_Lake_Package_licenseFiles___closed__0;
x_6 = lean_alloc_closure((void*)(l_Lake_Package_licenseFiles___lam__1), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = l_Lake_Package_relLicenseFiles___closed__9;
x_8 = lean_array_size(x_4);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_7, x_5, x_8, x_9, x_4);
x_11 = lean_array_size(x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_7, x_6, x_11, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relReadmeFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 24);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = l_System_FilePath_normalize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_readmeFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 24);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_System_FilePath_normalize(x_4);
x_6 = l_Lake_joinRelative(x_3, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Package_relLakeDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLakeDir;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_relLakeDir___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_relLakeDir(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lake_Package_relLakeDir___closed__0;
x_4 = l_Lake_joinRelative(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = l_System_FilePath_normalize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_System_FilePath_normalize(x_4);
x_6 = l_Lake_joinRelative(x_3, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_joinRelative(x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_System_FilePath_normalize(x_4);
x_6 = l_Lake_joinRelative(x_3, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 14);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_testDriverArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 16);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_lintDriverArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_extraDepTargets(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 10);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_platformIndependent(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 11);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_releaseRepo_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 8);
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc_ref(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_remoteUrl_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 16);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_Package_relLakeDir___closed__0;
x_5 = l_Lake_joinRelative(x_2, x_4);
x_6 = l_Lake_joinRelative(x_5, x_3);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Package_barrelFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build.barrel", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lake_Package_relLakeDir___closed__0;
x_4 = l_Lake_joinRelative(x_2, x_3);
x_5 = l_Lake_Package_barrelFile___closed__0;
x_6 = l_Lake_joinRelative(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_preferReleaseBuild(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_precompileModules(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreGlobalServerArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 4);
x_6 = l_Lean_LeanOptions_ofArray(x_4);
x_7 = l_Lean_LeanOptions_appendArray(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreServerOptions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*13);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_buildType(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*13 + 1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_backend(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 11);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_dynlibs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_dynlibs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 12);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_plugins___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_plugins(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_LeanOptions_ofArray(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_leanOptions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreLeanArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_weakLeanArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreLeancArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_weakLeancArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkObjs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreLinkObjs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkLibs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreLinkLibs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 8);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreLinkArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 9);
lean_inc_ref(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_weakLinkArgs(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_System_FilePath_normalize(x_4);
x_6 = l_Lake_joinRelative(x_3, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_System_FilePath_normalize(x_4);
x_6 = l_Lake_joinRelative(x_3, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 7);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = l_System_FilePath_normalize(x_4);
x_7 = l_Lake_joinRelative(x_3, x_6);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_normalize(x_5);
x_9 = l_Lake_joinRelative(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_staticLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = l_System_FilePath_normalize(x_4);
x_7 = l_Lake_joinRelative(x_3, x_6);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_normalize(x_5);
x_9 = l_Lake_joinRelative(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_sharedLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = l_System_FilePath_normalize(x_4);
x_7 = l_Lake_joinRelative(x_3, x_6);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_normalize(x_5);
x_9 = l_Lake_joinRelative(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_nativeLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = l_System_FilePath_normalize(x_4);
x_7 = l_Lake_joinRelative(x_3, x_6);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_normalize(x_5);
x_9 = l_Lake_joinRelative(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 9);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = l_System_FilePath_normalize(x_4);
x_7 = l_Lake_joinRelative(x_3, x_6);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_normalize(x_5);
x_9 = l_Lake_joinRelative(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 6);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 10);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = l_System_FilePath_normalize(x_4);
x_7 = l_Lake_joinRelative(x_3, x_6);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_normalize(x_5);
x_9 = l_Lake_joinRelative(x_7, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_libPrefixOnWindows(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*26 + 4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_libPrefixOnWindows___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_libPrefixOnWindows(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 25);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_enableArtifactCache_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_enableArtifactCache_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_inputsFileIn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = 0;
x_5 = l_Lean_Name_toString(x_3, x_4);
x_6 = l_Lake_Cache_inputsFile(x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 11);
x_4 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_get_x3f___at___Lake_Package_findTargetDecl_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_findTargetDecl_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Package_findTargetDecl_x3f(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_15; uint8_t x_16; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = 1;
x_15 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__1;
x_16 = lean_name_eq(x_7, x_15);
lean_dec(x_7);
if (x_16 == 0)
{
lean_dec(x_8);
x_10 = x_5;
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = l_Lake_LeanLibConfig_isLocalModule___redArg(x_1, x_8);
lean_dec(x_8);
x_10 = x_17;
goto block_14;
}
block_14:
{
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
return x_9;
}
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 10);
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Package_isLocalModule(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isBuildableModule_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_22; uint8_t x_23; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
x_9 = 1;
x_22 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__1;
x_23 = lean_name_eq(x_7, x_22);
lean_dec(x_7);
if (x_23 == 0)
{
lean_dec(x_8);
goto block_21;
}
else
{
uint8_t x_24; 
x_24 = l_Lake_LeanLibConfig_isBuildableModule___redArg(x_1, x_8);
lean_dec(x_8);
if (x_24 == 0)
{
goto block_21;
}
else
{
lean_dec_ref(x_6);
x_10 = x_24;
goto block_14;
}
}
block_14:
{
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
return x_9;
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_dec_ref(x_6);
x_17 = l_Lake_LeanExe_keyword;
x_18 = lean_name_eq(x_15, x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_dec(x_16);
x_10 = x_5;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_name_eq(x_19, x_1);
lean_dec(x_19);
x_10 = x_20;
goto block_14;
}
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 10);
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
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isBuildableModule_spec__0(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isBuildableModule_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isBuildableModule_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Package_isBuildableModule(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 6);
lean_inc_ref(x_5);
lean_dec_ref(x_3);
x_6 = l_System_FilePath_normalize(x_5);
x_7 = l_Lake_joinRelative(x_4, x_6);
lean_dec_ref(x_6);
x_8 = l_System_FilePath_pathExists(x_7, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_7);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = l_IO_FS_removeDirAll(x_7, x_17);
lean_dec_ref(x_7);
return x_18;
}
}
}
lean_object* initialize_Lake_Config_Cache(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Script(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_ConfigDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_PackageConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Cache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Script(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_ConfigDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_PackageConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OrdHashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OpaqueType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_defaultPackage___closed__0____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_ = _init_l_Lake_defaultPackage___closed__0____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_();
lean_mark_persistent(l_Lake_defaultPackage___closed__0____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_);
l_Lake_defaultPackage___closed__1____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_ = _init_l_Lake_defaultPackage___closed__1____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_();
lean_mark_persistent(l_Lake_defaultPackage___closed__1____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_);
l_Lake_defaultPackage___closed__2____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_ = _init_l_Lake_defaultPackage___closed__2____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_();
lean_mark_persistent(l_Lake_defaultPackage___closed__2____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_);
l_Lake_defaultPackage___closed__3____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_ = _init_l_Lake_defaultPackage___closed__3____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_();
lean_mark_persistent(l_Lake_defaultPackage___closed__3____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_);
l_Lake_defaultPackage___closed__4____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_ = _init_l_Lake_defaultPackage___closed__4____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_();
lean_mark_persistent(l_Lake_defaultPackage___closed__4____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_);
l_Lake_defaultPackage____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_ = _init_l_Lake_defaultPackage____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_();
lean_mark_persistent(l_Lake_defaultPackage____x40_Lake_Config_Package_1354092012____hygCtx___hyg_276_);
l_Lake_instInhabitedPackage = _init_l_Lake_instInhabitedPackage();
lean_mark_persistent(l_Lake_instInhabitedPackage);
l_Lake_instHashablePackage = _init_l_Lake_instHashablePackage();
lean_mark_persistent(l_Lake_instHashablePackage);
l_Lake_instBEqPackage = _init_l_Lake_instBEqPackage();
lean_mark_persistent(l_Lake_instBEqPackage);
l_Lake_PackageSet_empty___closed__0 = _init_l_Lake_PackageSet_empty___closed__0();
lean_mark_persistent(l_Lake_PackageSet_empty___closed__0);
l_Lake_PackageSet_empty___closed__1 = _init_l_Lake_PackageSet_empty___closed__1();
lean_mark_persistent(l_Lake_PackageSet_empty___closed__1);
l_Lake_PackageSet_empty___closed__2 = _init_l_Lake_PackageSet_empty___closed__2();
lean_mark_persistent(l_Lake_PackageSet_empty___closed__2);
l_Lake_PackageSet_empty___closed__3 = _init_l_Lake_PackageSet_empty___closed__3();
lean_mark_persistent(l_Lake_PackageSet_empty___closed__3);
l_Lake_PackageSet_empty___closed__4 = _init_l_Lake_PackageSet_empty___closed__4();
lean_mark_persistent(l_Lake_PackageSet_empty___closed__4);
l_Lake_PackageSet_empty = _init_l_Lake_PackageSet_empty();
lean_mark_persistent(l_Lake_PackageSet_empty);
l_Lake_OrdPackageSet_empty___closed__0 = _init_l_Lake_OrdPackageSet_empty___closed__0();
lean_mark_persistent(l_Lake_OrdPackageSet_empty___closed__0);
l_Lake_OrdPackageSet_empty___closed__1 = _init_l_Lake_OrdPackageSet_empty___closed__1();
lean_mark_persistent(l_Lake_OrdPackageSet_empty___closed__1);
l_Lake_OrdPackageSet_empty___closed__2 = _init_l_Lake_OrdPackageSet_empty___closed__2();
lean_mark_persistent(l_Lake_OrdPackageSet_empty___closed__2);
l_Lake_OrdPackageSet_empty = _init_l_Lake_OrdPackageSet_empty();
lean_mark_persistent(l_Lake_OrdPackageSet_empty);
l_Lake_instToJsonPackage = _init_l_Lake_instToJsonPackage();
lean_mark_persistent(l_Lake_instToJsonPackage);
l_Lake_instToStringPackage = _init_l_Lake_instToStringPackage();
lean_mark_persistent(l_Lake_instToStringPackage);
l_Lake_instInhabitedPostUpdateHook___closed__0 = _init_l_Lake_instInhabitedPostUpdateHook___closed__0();
lean_mark_persistent(l_Lake_instInhabitedPostUpdateHook___closed__0);
l_Lake_instImpl___closed__0____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_ = _init_l_Lake_instImpl___closed__0____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_();
lean_mark_persistent(l_Lake_instImpl___closed__0____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_);
l_Lake_instImpl___closed__1____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_ = _init_l_Lake_instImpl___closed__1____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_();
lean_mark_persistent(l_Lake_instImpl___closed__1____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_);
l_Lake_instImpl___closed__2____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_ = _init_l_Lake_instImpl___closed__2____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_();
lean_mark_persistent(l_Lake_instImpl___closed__2____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_);
l_Lake_instImpl____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_ = _init_l_Lake_instImpl____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_();
lean_mark_persistent(l_Lake_instImpl____x40_Lake_Config_Package_1275829001____hygCtx___hyg_24_);
l_Lake_instTypeNamePostUpdateHookDecl = _init_l_Lake_instTypeNamePostUpdateHookDecl();
lean_mark_persistent(l_Lake_instTypeNamePostUpdateHookDecl);
l_Lake_Package_relLicenseFiles___closed__0 = _init_l_Lake_Package_relLicenseFiles___closed__0();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__0);
l_Lake_Package_relLicenseFiles___closed__1 = _init_l_Lake_Package_relLicenseFiles___closed__1();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__1);
l_Lake_Package_relLicenseFiles___closed__2 = _init_l_Lake_Package_relLicenseFiles___closed__2();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__2);
l_Lake_Package_relLicenseFiles___closed__3 = _init_l_Lake_Package_relLicenseFiles___closed__3();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__3);
l_Lake_Package_relLicenseFiles___closed__4 = _init_l_Lake_Package_relLicenseFiles___closed__4();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__4);
l_Lake_Package_relLicenseFiles___closed__5 = _init_l_Lake_Package_relLicenseFiles___closed__5();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__5);
l_Lake_Package_relLicenseFiles___closed__6 = _init_l_Lake_Package_relLicenseFiles___closed__6();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__6);
l_Lake_Package_relLicenseFiles___closed__7 = _init_l_Lake_Package_relLicenseFiles___closed__7();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__7);
l_Lake_Package_relLicenseFiles___closed__8 = _init_l_Lake_Package_relLicenseFiles___closed__8();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__8);
l_Lake_Package_relLicenseFiles___closed__9 = _init_l_Lake_Package_relLicenseFiles___closed__9();
lean_mark_persistent(l_Lake_Package_relLicenseFiles___closed__9);
l_Lake_Package_licenseFiles___closed__0 = _init_l_Lake_Package_licenseFiles___closed__0();
lean_mark_persistent(l_Lake_Package_licenseFiles___closed__0);
l_Lake_Package_relLakeDir___closed__0 = _init_l_Lake_Package_relLakeDir___closed__0();
lean_mark_persistent(l_Lake_Package_relLakeDir___closed__0);
l_Lake_Package_barrelFile___closed__0 = _init_l_Lake_Package_barrelFile___closed__0();
lean_mark_persistent(l_Lake_Package_barrelFile___closed__0);
l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lake_Package_isLocalModule_spec__0___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

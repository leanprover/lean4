// Lean compiler output
// Module: Lake.Config.Package
// Imports: Init Lake.Config.Opaque Lake.Config.Defaults Lake.Config.LeanLibConfig Lake.Config.LeanExeConfig Lake.Config.ExternLibConfig Lake.Config.WorkspaceConfig Lake.Config.Dependency Lake.Config.Script Lake.Load.Config Lake.Util.DRBMap Lake.Util.OrdHashSet
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
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_instCoePackage;
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_instInhabitedOfPackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___default(lean_object*, lean_object*);
static lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_nativeLibDir___default;
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object*);
extern lean_object* l_Lake_defaultBuildDir;
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object*);
static lean_object* l_Lake_OpaquePackage_instCoePackage___closed__1;
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Package_isLocalModule___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_externLibConfigs___default___boxed(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeGet(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_defaultTargets___default;
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet___rarg___boxed(lean_object*);
static lean_object* l_Lake_Package_leanLibConfigs___default___closed__1;
static lean_object* l_Lake_PackageConfig_extraDepTargets___default___closed__1;
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object*);
static lean_object* l_Lake_defaultBuildArchive___closed__1;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive_x3f___default;
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object*);
static lean_object* l_Lake_instInhabitedPackageConfig___closed__2;
lean_object* l_Lake_RBArray_empty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_instInhabitedOfPackage(lean_object*);
static lean_object* l_Lake_instInhabitedPackageConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanLibConfigs___default;
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_manifestFile___default;
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_postUpdateHooks___default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriver___default;
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isLocalModule___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdPackageSet_empty;
LEAN_EXPORT uint8_t l_Lake_instBEqPackage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_opaqueDeps___default;
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriver___default;
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_depConfigs___default;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreServerArgs___default;
LEAN_EXPORT lean_object* l_Lake_instCoeDepPackageNPackageName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_extraDepTargets___default;
static lean_object* l_Lake_Package_leanLibConfigs___default___closed__2;
static lean_object* l_Lake_PackageConfig_srcDir___default___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_irDir___default;
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_lintDriverArgs___default;
LEAN_EXPORT lean_object* l_Lake_Package_nativeLibDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_testDriverArgs___default;
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_nonemptyType(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_opaqueTargetConfigs___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultBuildArchive(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_scripts___default;
LEAN_EXPORT lean_object* l_Lake_PackageSet_empty;
LEAN_EXPORT lean_object* l_Lake_Package_configFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk(lean_object*);
LEAN_EXPORT uint64_t l_Lake_instHashablePackage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___boxed(lean_object*);
lean_object* l_IO_FS_removeDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object*);
uint8_t l_Lake_LeanLibConfig_isLocalModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_opaqueTargetConfigs___default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_postUpdateHooks___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeMk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isLocalModule___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_isBuildableModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_srcDir___default;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relManifestFile___default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object*);
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Lake_Package_externLibConfigs___default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_testDriver___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_preferReleaseBuild___default;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeDepPackageNPackageName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPackageConfig;
static lean_object* l_Lake_OpaquePackage_instCoePackage__1___closed__1;
static lean_object* l_Lake_defaultBuildArchive___closed__3;
LEAN_EXPORT lean_object* l_Lake_Package_lintDriver___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lake_PackageSet_empty___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeMk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeGet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NPackage_name___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_defaultScripts___default;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lake_PackageSet_empty___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashablePackage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultNativeLibDir;
lean_object* l_Lake_LeanOption_asCliArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relManifestFile___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_testDriver___default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Package_buildArchive(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_lintDriver___default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir___boxed(lean_object*);
static lean_object* l_Lake_defaultBuildArchive___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_leanLibDir___default;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_leanExeConfigs___default;
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___default___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo___default;
uint8_t l_Lake_LeanLibConfig_isBuildableModule(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqPackage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_instCoePackage__1;
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildDir___default;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___closed__1;
extern lean_object* l_Lake_defaultBinDir;
LEAN_EXPORT lean_object* l_Lake_Package_remoteUrl_x3f___default;
extern lean_object* l_Lake_defaultIrDir;
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object*);
extern lean_object* l_System_Platform_target;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_releaseRepo_x3f___default;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___rarg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lake_PackageConfig_precompileModules___default;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_binDir___default;
static lean_object* l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__2;
extern lean_object* l_Lake_defaultLeanLibDir;
extern lean_object* l_Lake_defaultManifestFile;
LEAN_EXPORT lean_object* l_Lake_Package_buildArchive___boxed(lean_object*);
static lean_object* _init_l_Lake_defaultBuildArchive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultBuildArchive___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultBuildArchive___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".tar.gz", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_defaultBuildArchive(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = 0;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = l_Lake_defaultBuildArchive___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lake_defaultBuildArchive___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_System_Platform_target;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lake_defaultBuildArchive___closed__3;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lake_PackageConfig_manifestFile___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_extraDepTargets___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_extraDepTargets___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lake_PackageConfig_precompileModules___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_moreServerArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_moreGlobalServerArgs___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_moreGlobalServerArgs___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_srcDir___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_srcDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_srcDir___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultBuildDir;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_leanLibDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLeanLibDir;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_nativeLibDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultNativeLibDir;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_binDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultBinDir;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_irDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultIrDir;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_releaseRepo_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_releaseRepo___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_buildArchive_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___default(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = 0;
x_4 = l_Lean_Name_toString(x_1, x_3);
x_5 = l_Lake_defaultBuildArchive___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lake_defaultBuildArchive___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_System_Platform_target;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lake_defaultBuildArchive___closed__3;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_buildArchive___default___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_PackageConfig_buildArchive___default(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static uint8_t _init_l_Lake_PackageConfig_preferReleaseBuild___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriver___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultBuildArchive___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_testDriverArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriver___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultBuildArchive___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_lintDriverArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
x_4 = 2;
x_5 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_3);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*9, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*9 + 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lake_defaultBuildArchive___closed__1;
x_3 = l_Lake_instInhabitedPackageConfig___closed__1;
x_4 = lean_box(0);
x_5 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_5);
lean_ctor_set(x_7, 6, x_5);
lean_ctor_set(x_7, 7, x_2);
lean_ctor_set(x_7, 8, x_2);
lean_ctor_set(x_7, 9, x_2);
lean_ctor_set(x_7, 10, x_2);
lean_ctor_set(x_7, 11, x_2);
lean_ctor_set(x_7, 12, x_2);
lean_ctor_set(x_7, 13, x_1);
lean_ctor_set(x_7, 14, x_1);
lean_ctor_set(x_7, 15, x_1);
lean_ctor_set(x_7, 16, x_2);
lean_ctor_set(x_7, 17, x_2);
lean_ctor_set(x_7, 18, x_5);
lean_ctor_set(x_7, 19, x_2);
lean_ctor_set(x_7, 20, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*21, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*21 + 1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lake_instInhabitedPackageConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedPackageConfig___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_nonemptyType(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_nonemptyType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_nonemptyType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relManifestFile___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lake_defaultManifestFile;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relManifestFile___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_relManifestFile___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_remoteUrl_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_opaqueDeps___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_depConfigs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_leanLibConfigs___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_leanLibConfigs___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_leanLibConfigs___default___closed__1;
x_2 = l_Lake_RBArray_empty___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_leanLibConfigs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_leanLibConfigs___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_leanExeConfigs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Package_leanLibConfigs___default___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_externLibConfigs___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_externLibConfigs___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_externLibConfigs___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_opaqueTargetConfigs___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_opaqueTargetConfigs___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_opaqueTargetConfigs___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_defaultTargets___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_scripts___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_defaultScripts___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_postUpdateHooks___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_postUpdateHooks___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_postUpdateHooks___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriver___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 17);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriver___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_testDriver___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriver___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 19);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriver___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_lintDriver___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeMk(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeMk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePackage_unsafeMk(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OpaquePackage_instCoePackage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_OpaquePackage_unsafeMk___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OpaquePackage_instCoePackage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OpaquePackage_instCoePackage___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeGet(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_unsafeGet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePackage_unsafeGet(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OpaquePackage_instCoePackage__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_OpaquePackage_unsafeGet___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OpaquePackage_instCoePackage__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OpaquePackage_instCoePackage__1___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_instInhabitedOfPackage(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePackage_instInhabitedOfPackage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePackage_instInhabitedOfPackage(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashablePackage(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
x_4 = l_Lean_Name_hash___override(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instHashablePackage___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_instHashablePackage(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instBEqPackage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_5, 2);
x_7 = lean_name_eq(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instBEqPackage___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instBEqPackage(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lake_PackageSet_empty___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageSet_empty() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lake_PackageSet_empty___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSet___at_Lake_PackageSet_empty___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHashablePackage___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instBEqPackage___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__1;
x_2 = l_Lake_PackageConfig_extraDepTargets___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lake_OrdPackageSet_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_name(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instCoeOutNPackagePackage___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutNPackagePackage___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeOutNPackagePackage___rarg(x_1);
lean_dec(x_1);
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
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeDepPackageNPackageName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeDepPackageNPackageName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_NPackage_name___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_NPackage_name(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_instInhabitedPostUpdateHook___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedPostUpdateHook___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instInhabitedPostUpdateHook(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_OpaquePostUpdateHook_unsafeMk___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_unsafeMk___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeMk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_unsafeMk(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_OpaquePostUpdateHook_unsafeMk___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_OpaquePostUpdateHook_unsafeGet___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_unsafeGet___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_unsafeGet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_unsafeGet(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_OpaquePostUpdateHook_unsafeGet___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_deps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 6);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(x_4, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_deps___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_defaultLakeDir;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relLakeDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_relLakeDir(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lakeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lake_defaultLakeDir;
x_4 = l_System_FilePath_join(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_relPkgsDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_relPkgsDir(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_pkgsDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_System_FilePath_join(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_configFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_join(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_manifestFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_join(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 8);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_System_FilePath_join(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 18);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_testDriverArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_testDriverArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 20);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_lintDriverArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_lintDriverArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepTargets___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_extraDepTargets(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 8);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_platformIndependent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_platformIndependent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_releaseRepo_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 14);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 13);
lean_inc(x_4);
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 16);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchive___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_buildArchive(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildArchiveFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lake_defaultLakeDir;
x_4 = l_System_FilePath_join(x_2, x_3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 16);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_System_FilePath_join(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_preferReleaseBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*21 + 1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_preferReleaseBuild___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_preferReleaseBuild(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_precompileModules(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*21);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_precompileModules___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_precompileModules(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 6);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreGlobalServerArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreGlobalServerArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreServerOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 4);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Array_append___rarg(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_buildType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_buildType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_Package_backend(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*9 + 1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_backend___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Package_backend(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanOptions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_leanOptions(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_LeanOption_asCliArg(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeanArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_6, x_7, x_4);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Array_append___rarg(x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_Package_moreLeanArgs___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeanArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_weakLeanArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLeancArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreLeancArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 5);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLeancArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_weakLeancArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 6);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_moreLinkArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_moreLinkArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_weakLinkArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Package_weakLinkArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_srcDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_System_FilePath_join(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_rootDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_System_FilePath_join(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_leanLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 8);
lean_inc(x_4);
x_5 = l_System_FilePath_join(x_2, x_4);
x_6 = lean_ctor_get(x_3, 9);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_System_FilePath_join(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_nativeLibDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 8);
lean_inc(x_4);
x_5 = l_System_FilePath_join(x_2, x_4);
x_6 = lean_ctor_get(x_3, 10);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_System_FilePath_join(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_binDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 8);
lean_inc(x_4);
x_5 = l_System_FilePath_join(x_2, x_4);
x_6 = lean_ctor_get(x_3, 11);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_System_FilePath_join(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_irDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 8);
lean_inc(x_4);
x_5 = l_System_FilePath_join(x_2, x_4);
x_6 = lean_ctor_get(x_3, 12);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_System_FilePath_join(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isLocalModule___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lake_LeanLibConfig_isLocalModule(x_1, x_6);
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
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isLocalModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 8);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lake_Package_isLocalModule___spec__1(x_1, x_4, x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isLocalModule___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lake_Package_isLocalModule___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
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
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lake_LeanLibConfig_isBuildableModule(x_1, x_6);
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
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Package_isBuildableModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 8);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 9);
x_9 = lean_ctor_get(x_8, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_nat_dec_lt(x_6, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_15 = l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__1(x_1, x_9, x_13, x_14);
return x_15;
}
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_18 = l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__2(x_1, x_4, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_2, 9);
x_20 = lean_ctor_get(x_19, 1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_6, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_21);
x_23 = 0;
return x_23;
}
else
{
size_t x_24; uint8_t x_25; 
x_24 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_25 = l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__3(x_1, x_20, x_16, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lake_Package_isBuildableModule___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
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
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_clean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 8);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_System_FilePath_join(x_3, x_5);
x_7 = l_System_FilePath_pathExists(x_6, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_IO_FS_removeDirAll(x_6, x_16);
lean_dec(x_6);
return x_17;
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Opaque(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_LeanLibConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_LeanExeConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_ExternLibConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_WorkspaceConfig(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dependency(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Script(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_DRBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_OrdHashSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Opaque(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanLibConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanExeConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_ExternLibConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_WorkspaceConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dependency(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Script(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_DRBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OrdHashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_defaultBuildArchive___closed__1 = _init_l_Lake_defaultBuildArchive___closed__1();
lean_mark_persistent(l_Lake_defaultBuildArchive___closed__1);
l_Lake_defaultBuildArchive___closed__2 = _init_l_Lake_defaultBuildArchive___closed__2();
lean_mark_persistent(l_Lake_defaultBuildArchive___closed__2);
l_Lake_defaultBuildArchive___closed__3 = _init_l_Lake_defaultBuildArchive___closed__3();
lean_mark_persistent(l_Lake_defaultBuildArchive___closed__3);
l_Lake_PackageConfig_manifestFile___default = _init_l_Lake_PackageConfig_manifestFile___default();
lean_mark_persistent(l_Lake_PackageConfig_manifestFile___default);
l_Lake_PackageConfig_extraDepTargets___default___closed__1 = _init_l_Lake_PackageConfig_extraDepTargets___default___closed__1();
lean_mark_persistent(l_Lake_PackageConfig_extraDepTargets___default___closed__1);
l_Lake_PackageConfig_extraDepTargets___default = _init_l_Lake_PackageConfig_extraDepTargets___default();
lean_mark_persistent(l_Lake_PackageConfig_extraDepTargets___default);
l_Lake_PackageConfig_precompileModules___default = _init_l_Lake_PackageConfig_precompileModules___default();
l_Lake_PackageConfig_moreServerArgs___default = _init_l_Lake_PackageConfig_moreServerArgs___default();
lean_mark_persistent(l_Lake_PackageConfig_moreServerArgs___default);
l_Lake_PackageConfig_srcDir___default___closed__1 = _init_l_Lake_PackageConfig_srcDir___default___closed__1();
lean_mark_persistent(l_Lake_PackageConfig_srcDir___default___closed__1);
l_Lake_PackageConfig_srcDir___default = _init_l_Lake_PackageConfig_srcDir___default();
lean_mark_persistent(l_Lake_PackageConfig_srcDir___default);
l_Lake_PackageConfig_buildDir___default = _init_l_Lake_PackageConfig_buildDir___default();
lean_mark_persistent(l_Lake_PackageConfig_buildDir___default);
l_Lake_PackageConfig_leanLibDir___default = _init_l_Lake_PackageConfig_leanLibDir___default();
lean_mark_persistent(l_Lake_PackageConfig_leanLibDir___default);
l_Lake_PackageConfig_nativeLibDir___default = _init_l_Lake_PackageConfig_nativeLibDir___default();
lean_mark_persistent(l_Lake_PackageConfig_nativeLibDir___default);
l_Lake_PackageConfig_binDir___default = _init_l_Lake_PackageConfig_binDir___default();
lean_mark_persistent(l_Lake_PackageConfig_binDir___default);
l_Lake_PackageConfig_irDir___default = _init_l_Lake_PackageConfig_irDir___default();
lean_mark_persistent(l_Lake_PackageConfig_irDir___default);
l_Lake_PackageConfig_releaseRepo_x3f___default = _init_l_Lake_PackageConfig_releaseRepo_x3f___default();
lean_mark_persistent(l_Lake_PackageConfig_releaseRepo_x3f___default);
l_Lake_PackageConfig_releaseRepo___default = _init_l_Lake_PackageConfig_releaseRepo___default();
lean_mark_persistent(l_Lake_PackageConfig_releaseRepo___default);
l_Lake_PackageConfig_buildArchive_x3f___default = _init_l_Lake_PackageConfig_buildArchive_x3f___default();
lean_mark_persistent(l_Lake_PackageConfig_buildArchive_x3f___default);
l_Lake_PackageConfig_preferReleaseBuild___default = _init_l_Lake_PackageConfig_preferReleaseBuild___default();
l_Lake_PackageConfig_testDriver___default = _init_l_Lake_PackageConfig_testDriver___default();
lean_mark_persistent(l_Lake_PackageConfig_testDriver___default);
l_Lake_PackageConfig_testDriverArgs___default = _init_l_Lake_PackageConfig_testDriverArgs___default();
lean_mark_persistent(l_Lake_PackageConfig_testDriverArgs___default);
l_Lake_PackageConfig_lintDriver___default = _init_l_Lake_PackageConfig_lintDriver___default();
lean_mark_persistent(l_Lake_PackageConfig_lintDriver___default);
l_Lake_PackageConfig_lintDriverArgs___default = _init_l_Lake_PackageConfig_lintDriverArgs___default();
lean_mark_persistent(l_Lake_PackageConfig_lintDriverArgs___default);
l_Lake_instInhabitedPackageConfig___closed__1 = _init_l_Lake_instInhabitedPackageConfig___closed__1();
lean_mark_persistent(l_Lake_instInhabitedPackageConfig___closed__1);
l_Lake_instInhabitedPackageConfig___closed__2 = _init_l_Lake_instInhabitedPackageConfig___closed__2();
lean_mark_persistent(l_Lake_instInhabitedPackageConfig___closed__2);
l_Lake_instInhabitedPackageConfig = _init_l_Lake_instInhabitedPackageConfig();
lean_mark_persistent(l_Lake_instInhabitedPackageConfig);
l_Lake_Package_remoteUrl_x3f___default = _init_l_Lake_Package_remoteUrl_x3f___default();
lean_mark_persistent(l_Lake_Package_remoteUrl_x3f___default);
l_Lake_Package_opaqueDeps___default = _init_l_Lake_Package_opaqueDeps___default();
lean_mark_persistent(l_Lake_Package_opaqueDeps___default);
l_Lake_Package_depConfigs___default = _init_l_Lake_Package_depConfigs___default();
lean_mark_persistent(l_Lake_Package_depConfigs___default);
l_Lake_Package_leanLibConfigs___default___closed__1 = _init_l_Lake_Package_leanLibConfigs___default___closed__1();
lean_mark_persistent(l_Lake_Package_leanLibConfigs___default___closed__1);
l_Lake_Package_leanLibConfigs___default___closed__2 = _init_l_Lake_Package_leanLibConfigs___default___closed__2();
lean_mark_persistent(l_Lake_Package_leanLibConfigs___default___closed__2);
l_Lake_Package_leanLibConfigs___default = _init_l_Lake_Package_leanLibConfigs___default();
lean_mark_persistent(l_Lake_Package_leanLibConfigs___default);
l_Lake_Package_leanExeConfigs___default = _init_l_Lake_Package_leanExeConfigs___default();
lean_mark_persistent(l_Lake_Package_leanExeConfigs___default);
l_Lake_Package_defaultTargets___default = _init_l_Lake_Package_defaultTargets___default();
lean_mark_persistent(l_Lake_Package_defaultTargets___default);
l_Lake_Package_scripts___default = _init_l_Lake_Package_scripts___default();
lean_mark_persistent(l_Lake_Package_scripts___default);
l_Lake_Package_defaultScripts___default = _init_l_Lake_Package_defaultScripts___default();
lean_mark_persistent(l_Lake_Package_defaultScripts___default);
l_Lake_OpaquePackage_instCoePackage___closed__1 = _init_l_Lake_OpaquePackage_instCoePackage___closed__1();
lean_mark_persistent(l_Lake_OpaquePackage_instCoePackage___closed__1);
l_Lake_OpaquePackage_instCoePackage = _init_l_Lake_OpaquePackage_instCoePackage();
lean_mark_persistent(l_Lake_OpaquePackage_instCoePackage);
l_Lake_OpaquePackage_instCoePackage__1___closed__1 = _init_l_Lake_OpaquePackage_instCoePackage__1___closed__1();
lean_mark_persistent(l_Lake_OpaquePackage_instCoePackage__1___closed__1);
l_Lake_OpaquePackage_instCoePackage__1 = _init_l_Lake_OpaquePackage_instCoePackage__1();
lean_mark_persistent(l_Lake_OpaquePackage_instCoePackage__1);
l_Lake_PackageSet_empty = _init_l_Lake_PackageSet_empty();
lean_mark_persistent(l_Lake_PackageSet_empty);
l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__1 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__1();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__1);
l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__2 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__2();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__2);
l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__3 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__3();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__3);
l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__4 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__4();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1___closed__4);
l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1 = _init_l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at_Lake_OrdPackageSet_empty___spec__1);
l_Lake_OrdPackageSet_empty = _init_l_Lake_OrdPackageSet_empty();
lean_mark_persistent(l_Lake_OrdPackageSet_empty);
l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___closed__1 = _init_l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___closed__1();
lean_mark_persistent(l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook___closed__1);
l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___closed__1 = _init_l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___closed__1();
lean_mark_persistent(l_Lake_OpaquePostUpdateHook_instCoePostUpdateHook__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lake.Config.Defaults
// Imports: Init.System.FilePath
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
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultTomlConfigFile;
LEAN_EXPORT lean_object* l_Lake_defaultBuildDir;
static lean_object* l_Lake_defaultConfigFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultPackagesDir;
static lean_object* l_Lake_defaultIrDir___closed__1;
static lean_object* l_Lake_defaultLeanLibDir___closed__2;
LEAN_EXPORT lean_object* l_Lake_defaultLeanConfigFile;
static lean_object* l_Lake_defaultTomlConfigFile___closed__2;
static lean_object* l_Lake_defaultPackagesDir___closed__1;
static lean_object* l_Lake_defaultBinDir___closed__1;
static lean_object* l_Lake_defaultLeanConfigFile___closed__2;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_defaultLeanLibDir___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultLakeDir;
static lean_object* l_Lake_defaultLeanConfigFile___closed__1;
static lean_object* l_Lake_defaultLakeDir___closed__1;
static lean_object* l_Lake_defaultBuildDir___closed__2;
LEAN_EXPORT lean_object* l_Lake_defaultNativeLibDir;
static lean_object* l_Lake_defaultPackagesDir___closed__2;
LEAN_EXPORT lean_object* l_Lake_defaultConfigFile;
static lean_object* l_Lake_defaultManifestFile___closed__1;
static lean_object* l_Lake_defaultBuildDir___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultBinDir;
LEAN_EXPORT lean_object* l_Lake_defaultIrDir;
static lean_object* l_Lake_defaultTomlConfigFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultLeanLibDir;
LEAN_EXPORT lean_object* l_Lake_defaultManifestFile;
static lean_object* _init_l_Lake_defaultLakeDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lake", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultLakeDir() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLakeDir___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultPackagesDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packages", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultPackagesDir___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_defaultLakeDir;
x_2 = l_Lake_defaultPackagesDir___closed__1;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_defaultPackagesDir() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultPackagesDir___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultConfigFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lakefile", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultConfigFile() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultConfigFile___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultLeanConfigFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultLeanConfigFile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_defaultConfigFile;
x_2 = l_Lake_defaultLeanConfigFile___closed__1;
x_3 = l_System_FilePath_addExtension(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_defaultLeanConfigFile() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLeanConfigFile___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultTomlConfigFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toml", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultTomlConfigFile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_defaultConfigFile;
x_2 = l_Lake_defaultTomlConfigFile___closed__1;
x_3 = l_System_FilePath_addExtension(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_defaultTomlConfigFile() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultTomlConfigFile___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultManifestFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake-manifest.json", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultManifestFile() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultManifestFile___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultBuildDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultBuildDir___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_defaultLakeDir;
x_2 = l_Lake_defaultBuildDir___closed__1;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_defaultBuildDir() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultBuildDir___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultLeanLibDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultLeanLibDir___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_defaultLeanLibDir___closed__1;
x_2 = l_Lake_defaultLeanConfigFile___closed__1;
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_defaultLeanLibDir() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLeanLibDir___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultNativeLibDir() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLeanLibDir___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultBinDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bin", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultBinDir() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultBinDir___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_defaultIrDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ir", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultIrDir() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultIrDir___closed__1;
return x_1;
}
}
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Defaults(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_defaultLakeDir___closed__1 = _init_l_Lake_defaultLakeDir___closed__1();
lean_mark_persistent(l_Lake_defaultLakeDir___closed__1);
l_Lake_defaultLakeDir = _init_l_Lake_defaultLakeDir();
lean_mark_persistent(l_Lake_defaultLakeDir);
l_Lake_defaultPackagesDir___closed__1 = _init_l_Lake_defaultPackagesDir___closed__1();
lean_mark_persistent(l_Lake_defaultPackagesDir___closed__1);
l_Lake_defaultPackagesDir___closed__2 = _init_l_Lake_defaultPackagesDir___closed__2();
lean_mark_persistent(l_Lake_defaultPackagesDir___closed__2);
l_Lake_defaultPackagesDir = _init_l_Lake_defaultPackagesDir();
lean_mark_persistent(l_Lake_defaultPackagesDir);
l_Lake_defaultConfigFile___closed__1 = _init_l_Lake_defaultConfigFile___closed__1();
lean_mark_persistent(l_Lake_defaultConfigFile___closed__1);
l_Lake_defaultConfigFile = _init_l_Lake_defaultConfigFile();
lean_mark_persistent(l_Lake_defaultConfigFile);
l_Lake_defaultLeanConfigFile___closed__1 = _init_l_Lake_defaultLeanConfigFile___closed__1();
lean_mark_persistent(l_Lake_defaultLeanConfigFile___closed__1);
l_Lake_defaultLeanConfigFile___closed__2 = _init_l_Lake_defaultLeanConfigFile___closed__2();
lean_mark_persistent(l_Lake_defaultLeanConfigFile___closed__2);
l_Lake_defaultLeanConfigFile = _init_l_Lake_defaultLeanConfigFile();
lean_mark_persistent(l_Lake_defaultLeanConfigFile);
l_Lake_defaultTomlConfigFile___closed__1 = _init_l_Lake_defaultTomlConfigFile___closed__1();
lean_mark_persistent(l_Lake_defaultTomlConfigFile___closed__1);
l_Lake_defaultTomlConfigFile___closed__2 = _init_l_Lake_defaultTomlConfigFile___closed__2();
lean_mark_persistent(l_Lake_defaultTomlConfigFile___closed__2);
l_Lake_defaultTomlConfigFile = _init_l_Lake_defaultTomlConfigFile();
lean_mark_persistent(l_Lake_defaultTomlConfigFile);
l_Lake_defaultManifestFile___closed__1 = _init_l_Lake_defaultManifestFile___closed__1();
lean_mark_persistent(l_Lake_defaultManifestFile___closed__1);
l_Lake_defaultManifestFile = _init_l_Lake_defaultManifestFile();
lean_mark_persistent(l_Lake_defaultManifestFile);
l_Lake_defaultBuildDir___closed__1 = _init_l_Lake_defaultBuildDir___closed__1();
lean_mark_persistent(l_Lake_defaultBuildDir___closed__1);
l_Lake_defaultBuildDir___closed__2 = _init_l_Lake_defaultBuildDir___closed__2();
lean_mark_persistent(l_Lake_defaultBuildDir___closed__2);
l_Lake_defaultBuildDir = _init_l_Lake_defaultBuildDir();
lean_mark_persistent(l_Lake_defaultBuildDir);
l_Lake_defaultLeanLibDir___closed__1 = _init_l_Lake_defaultLeanLibDir___closed__1();
lean_mark_persistent(l_Lake_defaultLeanLibDir___closed__1);
l_Lake_defaultLeanLibDir___closed__2 = _init_l_Lake_defaultLeanLibDir___closed__2();
lean_mark_persistent(l_Lake_defaultLeanLibDir___closed__2);
l_Lake_defaultLeanLibDir = _init_l_Lake_defaultLeanLibDir();
lean_mark_persistent(l_Lake_defaultLeanLibDir);
l_Lake_defaultNativeLibDir = _init_l_Lake_defaultNativeLibDir();
lean_mark_persistent(l_Lake_defaultNativeLibDir);
l_Lake_defaultBinDir___closed__1 = _init_l_Lake_defaultBinDir___closed__1();
lean_mark_persistent(l_Lake_defaultBinDir___closed__1);
l_Lake_defaultBinDir = _init_l_Lake_defaultBinDir();
lean_mark_persistent(l_Lake_defaultBinDir);
l_Lake_defaultIrDir___closed__1 = _init_l_Lake_defaultIrDir___closed__1();
lean_mark_persistent(l_Lake_defaultIrDir___closed__1);
l_Lake_defaultIrDir = _init_l_Lake_defaultIrDir();
lean_mark_persistent(l_Lake_defaultIrDir);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

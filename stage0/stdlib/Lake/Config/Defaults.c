// Lean compiler output
// Module: Lake.Config.Defaults
// Imports: public import Init.System.FilePath
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
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static const lean_string_object l_Lake_defaultLakeDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".lake"};
static const lean_object* l_Lake_defaultLakeDir___closed__0 = (const lean_object*)&l_Lake_defaultLakeDir___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_defaultLakeDir = (const lean_object*)&l_Lake_defaultLakeDir___closed__0_value;
static const lean_string_object l_Lake_defaultPackagesDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "packages"};
static const lean_object* l_Lake_defaultPackagesDir___closed__0 = (const lean_object*)&l_Lake_defaultPackagesDir___closed__0_value;
static lean_once_cell_t l_Lake_defaultPackagesDir___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_defaultPackagesDir___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultPackagesDir;
static const lean_string_object l_Lake_defaultConfigFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lakefile"};
static const lean_object* l_Lake_defaultConfigFile___closed__0 = (const lean_object*)&l_Lake_defaultConfigFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_defaultConfigFile = (const lean_object*)&l_Lake_defaultConfigFile___closed__0_value;
static const lean_string_object l_Lake_defaultLeanConfigFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lake_defaultLeanConfigFile___closed__0 = (const lean_object*)&l_Lake_defaultLeanConfigFile___closed__0_value;
static lean_once_cell_t l_Lake_defaultLeanConfigFile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_defaultLeanConfigFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultLeanConfigFile;
static const lean_string_object l_Lake_defaultTomlConfigFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l_Lake_defaultTomlConfigFile___closed__0 = (const lean_object*)&l_Lake_defaultTomlConfigFile___closed__0_value;
static lean_once_cell_t l_Lake_defaultTomlConfigFile___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_defaultTomlConfigFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultTomlConfigFile;
static const lean_string_object l_Lake_defaultManifestFile___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "lake-manifest.json"};
static const lean_object* l_Lake_defaultManifestFile___closed__0 = (const lean_object*)&l_Lake_defaultManifestFile___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_defaultManifestFile = (const lean_object*)&l_Lake_defaultManifestFile___closed__0_value;
static const lean_string_object l_Lake_defaultBuildDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "build"};
static const lean_object* l_Lake_defaultBuildDir___closed__0 = (const lean_object*)&l_Lake_defaultBuildDir___closed__0_value;
static lean_once_cell_t l_Lake_defaultBuildDir___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_defaultBuildDir___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultBuildDir;
static const lean_string_object l_Lake_defaultLeanLibDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_defaultLeanLibDir___closed__0 = (const lean_object*)&l_Lake_defaultLeanLibDir___closed__0_value;
static lean_once_cell_t l_Lake_defaultLeanLibDir___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_defaultLeanLibDir___closed__1;
LEAN_EXPORT lean_object* l_Lake_defaultLeanLibDir;
LEAN_EXPORT const lean_object* l_Lake_defaultNativeLibDir = (const lean_object*)&l_Lake_defaultLeanLibDir___closed__0_value;
static const lean_string_object l_Lake_defaultBinDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lake_defaultBinDir___closed__0 = (const lean_object*)&l_Lake_defaultBinDir___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_defaultBinDir = (const lean_object*)&l_Lake_defaultBinDir___closed__0_value;
static const lean_string_object l_Lake_defaultIrDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Lake_defaultIrDir___closed__0 = (const lean_object*)&l_Lake_defaultIrDir___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_defaultIrDir = (const lean_object*)&l_Lake_defaultIrDir___closed__0_value;
static lean_object* _init_l_Lake_defaultPackagesDir___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = ((lean_object*)(l_Lake_defaultPackagesDir___closed__0));
v___x_5_ = ((lean_object*)(l_Lake_defaultLakeDir___closed__0));
v___x_6_ = l_System_FilePath_join(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lake_defaultPackagesDir(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lake_defaultPackagesDir___closed__1, &l_Lake_defaultPackagesDir___closed__1_once, _init_l_Lake_defaultPackagesDir___closed__1);
return v___x_7_;
}
}
static lean_object* _init_l_Lake_defaultLeanConfigFile___closed__1(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l_Lake_defaultLeanConfigFile___closed__0));
v___x_12_ = ((lean_object*)(l_Lake_defaultConfigFile___closed__0));
v___x_13_ = l_System_FilePath_addExtension(v___x_12_, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lake_defaultLeanConfigFile(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lake_defaultLeanConfigFile___closed__1, &l_Lake_defaultLeanConfigFile___closed__1_once, _init_l_Lake_defaultLeanConfigFile___closed__1);
return v___x_14_;
}
}
static lean_object* _init_l_Lake_defaultTomlConfigFile___closed__1(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = ((lean_object*)(l_Lake_defaultTomlConfigFile___closed__0));
v___x_17_ = ((lean_object*)(l_Lake_defaultConfigFile___closed__0));
v___x_18_ = l_System_FilePath_addExtension(v___x_17_, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Lake_defaultTomlConfigFile(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&l_Lake_defaultTomlConfigFile___closed__1, &l_Lake_defaultTomlConfigFile___closed__1_once, _init_l_Lake_defaultTomlConfigFile___closed__1);
return v___x_19_;
}
}
static lean_object* _init_l_Lake_defaultBuildDir___closed__1(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = ((lean_object*)(l_Lake_defaultBuildDir___closed__0));
v___x_24_ = ((lean_object*)(l_Lake_defaultLakeDir___closed__0));
v___x_25_ = l_System_FilePath_join(v___x_24_, v___x_23_);
return v___x_25_;
}
}
static lean_object* _init_l_Lake_defaultBuildDir(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_obj_once(&l_Lake_defaultBuildDir___closed__1, &l_Lake_defaultBuildDir___closed__1_once, _init_l_Lake_defaultBuildDir___closed__1);
return v___x_26_;
}
}
static lean_object* _init_l_Lake_defaultLeanLibDir___closed__1(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = ((lean_object*)(l_Lake_defaultLeanConfigFile___closed__0));
v___x_29_ = ((lean_object*)(l_Lake_defaultLeanLibDir___closed__0));
v___x_30_ = l_System_FilePath_join(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_Lake_defaultLeanLibDir(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_obj_once(&l_Lake_defaultLeanLibDir___closed__1, &l_Lake_defaultLeanLibDir___closed__1_once, _init_l_Lake_defaultLeanLibDir___closed__1);
return v___x_31_;
}
}
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Defaults(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_defaultPackagesDir = _init_l_Lake_defaultPackagesDir();
lean_mark_persistent(l_Lake_defaultPackagesDir);
l_Lake_defaultLeanConfigFile = _init_l_Lake_defaultLeanConfigFile();
lean_mark_persistent(l_Lake_defaultLeanConfigFile);
l_Lake_defaultTomlConfigFile = _init_l_Lake_defaultTomlConfigFile();
lean_mark_persistent(l_Lake_defaultTomlConfigFile);
l_Lake_defaultBuildDir = _init_l_Lake_defaultBuildDir();
lean_mark_persistent(l_Lake_defaultBuildDir);
l_Lake_defaultLeanLibDir = _init_l_Lake_defaultLeanLibDir();
lean_mark_persistent(l_Lake_defaultLeanLibDir);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Defaults(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Defaults(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Defaults(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Defaults(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lake.Util.NativeLib
// Imports: public import Init.System.IO import Init.Data.ToString.Macro import Init.System.Platform
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
extern uint8_t l_System_Platform_isWindows;
extern uint8_t l_System_Platform_isOSX;
uint8_t lean_bool_not(uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* l_System_SearchPath_parse(lean_object*);
static const lean_string_object l_Lake_sharedLibExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "so"};
static const lean_object* l_Lake_sharedLibExt___closed__0 = (const lean_object*)&l_Lake_sharedLibExt___closed__0_value;
static const lean_string_object l_Lake_sharedLibExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dylib"};
static const lean_object* l_Lake_sharedLibExt___closed__1 = (const lean_object*)&l_Lake_sharedLibExt___closed__1_value;
static const lean_string_object l_Lake_sharedLibExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dll"};
static const lean_object* l_Lake_sharedLibExt___closed__2 = (const lean_object*)&l_Lake_sharedLibExt___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_sharedLibExt;
static const lean_string_object l_Lake_nameToStaticLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_nameToStaticLib___closed__0 = (const lean_object*)&l_Lake_nameToStaticLib___closed__0_value;
static const lean_string_object l_Lake_nameToStaticLib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".a"};
static const lean_object* l_Lake_nameToStaticLib___closed__1 = (const lean_object*)&l_Lake_nameToStaticLib___closed__1_value;
static lean_once_cell_t l_Lake_nameToStaticLib___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_nameToStaticLib___closed__2;
LEAN_EXPORT lean_object* l_Lake_nameToStaticLib(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_nameToStaticLib___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_nameToSharedLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_nameToSharedLib___closed__0 = (const lean_object*)&l_Lake_nameToSharedLib___closed__0_value;
static const lean_string_object l_Lake_nameToSharedLib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_nameToSharedLib___closed__1 = (const lean_object*)&l_Lake_nameToSharedLib___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_nameToSharedLib___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_sharedLibPathEnvVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "LD_LIBRARY_PATH"};
static const lean_object* l_Lake_sharedLibPathEnvVar___closed__0 = (const lean_object*)&l_Lake_sharedLibPathEnvVar___closed__0_value;
static const lean_string_object l_Lake_sharedLibPathEnvVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "DYLD_LIBRARY_PATH"};
static const lean_object* l_Lake_sharedLibPathEnvVar___closed__1 = (const lean_object*)&l_Lake_sharedLibPathEnvVar___closed__1_value;
static const lean_string_object l_Lake_sharedLibPathEnvVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PATH"};
static const lean_object* l_Lake_sharedLibPathEnvVar___closed__2 = (const lean_object*)&l_Lake_sharedLibPathEnvVar___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_sharedLibPathEnvVar;
LEAN_EXPORT lean_object* l_Lake_getSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSearchPath___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_sharedLibExt(void){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_System_Platform_isWindows;
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = l_System_Platform_isOSX;
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
v___x_6_ = ((lean_object*)(l_Lake_sharedLibExt___closed__0));
return v___x_6_;
}
else
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Lake_sharedLibExt___closed__1));
return v___x_7_;
}
}
else
{
lean_object* v___x_8_; 
v___x_8_ = ((lean_object*)(l_Lake_sharedLibExt___closed__2));
return v___x_8_;
}
}
}
static uint8_t _init_l_Lake_nameToStaticLib___closed__2(void){
_start:
{
uint8_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = l_System_Platform_isWindows;
v___x_12_ = lean_bool_not(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_nameToStaticLib(lean_object* v_name_13_, uint8_t v_libPrefixOnWindows_14_){
_start:
{
if (v_libPrefixOnWindows_14_ == 0)
{
uint8_t v___x_20_; 
v___x_20_ = lean_uint8_once(&l_Lake_nameToStaticLib___closed__2, &l_Lake_nameToStaticLib___closed__2_once, _init_l_Lake_nameToStaticLib___closed__2);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__1));
v___x_22_ = lean_string_append(v_name_13_, v___x_21_);
return v___x_22_;
}
else
{
goto v___jp_15_;
}
}
else
{
goto v___jp_15_;
}
v___jp_15_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__0));
v___x_17_ = lean_string_append(v___x_16_, v_name_13_);
lean_dec_ref(v_name_13_);
v___x_18_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__1));
v___x_19_ = lean_string_append(v___x_17_, v___x_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nameToStaticLib___boxed(lean_object* v_name_23_, lean_object* v_libPrefixOnWindows_24_){
_start:
{
uint8_t v_libPrefixOnWindows_boxed_25_; lean_object* v_res_26_; 
v_libPrefixOnWindows_boxed_25_ = lean_unbox(v_libPrefixOnWindows_24_);
v_res_26_ = l_Lake_nameToStaticLib(v_name_23_, v_libPrefixOnWindows_boxed_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_nameToSharedLib(lean_object* v_name_29_, uint8_t v_libPrefixOnWindows_30_){
_start:
{
lean_object* v___y_32_; 
if (v_libPrefixOnWindows_30_ == 0)
{
uint8_t v___x_40_; 
v___x_40_ = lean_uint8_once(&l_Lake_nameToStaticLib___closed__2, &l_Lake_nameToStaticLib___closed__2_once, _init_l_Lake_nameToStaticLib___closed__2);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; 
v___x_41_ = ((lean_object*)(l_Lake_nameToSharedLib___closed__1));
v___y_32_ = v___x_41_;
goto v___jp_31_;
}
else
{
goto v___jp_38_;
}
}
else
{
goto v___jp_38_;
}
v___jp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
lean_inc_ref(v___y_32_);
v___x_33_ = lean_string_append(v___y_32_, v_name_29_);
v___x_34_ = ((lean_object*)(l_Lake_nameToSharedLib___closed__0));
v___x_35_ = lean_string_append(v___x_33_, v___x_34_);
v___x_36_ = l_Lake_sharedLibExt;
v___x_37_ = lean_string_append(v___x_35_, v___x_36_);
return v___x_37_;
}
v___jp_38_:
{
lean_object* v___x_39_; 
v___x_39_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__0));
v___y_32_ = v___x_39_;
goto v___jp_31_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nameToSharedLib___boxed(lean_object* v_name_42_, lean_object* v_libPrefixOnWindows_43_){
_start:
{
uint8_t v_libPrefixOnWindows_boxed_44_; lean_object* v_res_45_; 
v_libPrefixOnWindows_boxed_44_ = lean_unbox(v_libPrefixOnWindows_43_);
v_res_45_ = l_Lake_nameToSharedLib(v_name_42_, v_libPrefixOnWindows_boxed_44_);
lean_dec_ref(v_name_42_);
return v_res_45_;
}
}
static lean_object* _init_l_Lake_sharedLibPathEnvVar(void){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = l_System_Platform_isWindows;
if (v___x_49_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = l_System_Platform_isOSX;
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
v___x_51_ = ((lean_object*)(l_Lake_sharedLibPathEnvVar___closed__0));
return v___x_51_;
}
else
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_Lake_sharedLibPathEnvVar___closed__1));
return v___x_52_;
}
}
else
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_Lake_sharedLibPathEnvVar___closed__2));
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSearchPath(lean_object* v_envVar_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_io_getenv(v_envVar_54_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v_val_58_; lean_object* v___x_59_; 
v_val_58_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_val_58_);
lean_dec_ref_known(v___x_56_, 1);
v___x_59_ = l_System_SearchPath_parse(v_val_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSearchPath___boxed(lean_object* v_envVar_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_getSearchPath(v_envVar_60_);
lean_dec_ref(v_envVar_60_);
return v_res_62_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_sharedLibExt = _init_l_Lake_sharedLibExt();
lean_mark_persistent(l_Lake_sharedLibExt);
l_Lake_sharedLibPathEnvVar = _init_l_Lake_sharedLibPathEnvVar();
lean_mark_persistent(l_Lake_sharedLibPathEnvVar);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_NativeLib(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_NativeLib(builtin);
}
#ifdef __cplusplus
}
#endif

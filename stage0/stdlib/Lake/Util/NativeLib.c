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
lean_object* l_Lake_nameToStaticLib(lean_object* v_name_11_, uint8_t v_libPrefixOnWindows_12_){
_start:
{
if (v_libPrefixOnWindows_12_ == 0)
{
uint8_t v___x_18_; 
v___x_18_ = l_System_Platform_isWindows;
if (v___x_18_ == 0)
{
goto v___jp_13_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__1));
v___x_20_ = lean_string_append(v_name_11_, v___x_19_);
return v___x_20_;
}
}
else
{
goto v___jp_13_;
}
v___jp_13_:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_14_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__0));
v___x_15_ = lean_string_append(v___x_14_, v_name_11_);
lean_dec_ref(v_name_11_);
v___x_16_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__1));
v___x_17_ = lean_string_append(v___x_15_, v___x_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT void l_Lake_nameToStaticLib_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_11_ = stack[0].m_obj;
uint8_t v_libPrefixOnWindows_12_ = stack[1].m_num;
lean_object* v_res_21_;
v_res_21_ = l_Lake_nameToStaticLib(v_name_11_, v_libPrefixOnWindows_12_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lake_nameToStaticLib___boxed(lean_object* v_name_22_, lean_object* v_libPrefixOnWindows_23_){
_start:
{
uint8_t v_libPrefixOnWindows_boxed_24_; lean_object* v_res_25_; 
v_libPrefixOnWindows_boxed_24_ = lean_unbox(v_libPrefixOnWindows_23_);
v_res_25_ = l_Lake_nameToStaticLib(v_name_22_, v_libPrefixOnWindows_boxed_24_);
return v_res_25_;
}
}
lean_object* l_Lake_nameToSharedLib(lean_object* v_name_28_, uint8_t v_libPrefixOnWindows_29_){
_start:
{
lean_object* v___y_31_; 
if (v_libPrefixOnWindows_29_ == 0)
{
uint8_t v___x_39_; 
v___x_39_ = l_System_Platform_isWindows;
if (v___x_39_ == 0)
{
goto v___jp_37_;
}
else
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(l_Lake_nameToSharedLib___closed__1));
v___y_31_ = v___x_40_;
goto v___jp_30_;
}
}
else
{
goto v___jp_37_;
}
v___jp_30_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
lean_inc_ref(v___y_31_);
v___x_32_ = lean_string_append(v___y_31_, v_name_28_);
v___x_33_ = ((lean_object*)(l_Lake_nameToSharedLib___closed__0));
v___x_34_ = lean_string_append(v___x_32_, v___x_33_);
v___x_35_ = l_Lake_sharedLibExt;
v___x_36_ = lean_string_append(v___x_34_, v___x_35_);
return v___x_36_;
}
v___jp_37_:
{
lean_object* v___x_38_; 
v___x_38_ = ((lean_object*)(l_Lake_nameToStaticLib___closed__0));
v___y_31_ = v___x_38_;
goto v___jp_30_;
}
}
}
LEAN_EXPORT void l_Lake_nameToSharedLib_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_28_ = stack[0].m_obj;
uint8_t v_libPrefixOnWindows_29_ = stack[1].m_num;
lean_object* v_res_41_;
v_res_41_ = l_Lake_nameToSharedLib(v_name_28_, v_libPrefixOnWindows_29_);
stack->m_obj
 = v_res_41_;
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
lean_object* l_Lake_getSearchPath(lean_object* v_envVar_54_){
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
LEAN_EXPORT void l_Lake_getSearchPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_envVar_54_ = stack[0].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lake_getSearchPath(v_envVar_54_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lake_getSearchPath___boxed(lean_object* v_envVar_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lake_getSearchPath(v_envVar_61_);
lean_dec_ref(v_envVar_61_);
return v_res_63_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_NativeLib(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

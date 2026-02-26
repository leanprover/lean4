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
static const lean_string_object l_Lake_sharedLibExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "so"};
static const lean_object* l_Lake_sharedLibExt___closed__0 = (const lean_object*)&l_Lake_sharedLibExt___closed__0_value;
static const lean_string_object l_Lake_sharedLibExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dylib"};
static const lean_object* l_Lake_sharedLibExt___closed__1 = (const lean_object*)&l_Lake_sharedLibExt___closed__1_value;
static const lean_string_object l_Lake_sharedLibExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dll"};
static const lean_object* l_Lake_sharedLibExt___closed__2 = (const lean_object*)&l_Lake_sharedLibExt___closed__2_value;
extern uint8_t l_System_Platform_isWindows;
extern uint8_t l_System_Platform_isOSX;
LEAN_EXPORT lean_object* l_Lake_sharedLibExt;
static const lean_string_object l_Lake_nameToStaticLib___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lib"};
static const lean_object* l_Lake_nameToStaticLib___closed__0 = (const lean_object*)&l_Lake_nameToStaticLib___closed__0_value;
static const lean_string_object l_Lake_nameToStaticLib___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".a"};
static const lean_object* l_Lake_nameToStaticLib___closed__1 = (const lean_object*)&l_Lake_nameToStaticLib___closed__1_value;
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_io_getenv(lean_object*);
lean_object* l_System_SearchPath_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getSearchPath___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_sharedLibExt(void) {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = l_System_Platform_isOSX;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_sharedLibExt___closed__0));
return x_3;
}
else
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Lake_sharedLibExt___closed__1));
return x_4;
}
}
else
{
lean_object* x_5; 
x_5 = ((lean_object*)(l_Lake_sharedLibExt___closed__2));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nameToStaticLib(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
uint8_t x_8; 
x_8 = l_System_Platform_isWindows;
if (x_8 == 0)
{
goto block_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = ((lean_object*)(l_Lake_nameToStaticLib___closed__1));
x_10 = lean_string_append(x_1, x_9);
return x_10;
}
}
else
{
goto block_7;
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = ((lean_object*)(l_Lake_nameToStaticLib___closed__0));
x_4 = lean_string_append(x_3, x_1);
lean_dec_ref(x_1);
x_5 = ((lean_object*)(l_Lake_nameToStaticLib___closed__1));
x_6 = lean_string_append(x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nameToStaticLib___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lake_nameToStaticLib(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_nameToSharedLib(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
if (x_2 == 0)
{
uint8_t x_12; 
x_12 = l_System_Platform_isWindows;
if (x_12 == 0)
{
goto block_11;
}
else
{
lean_object* x_13; 
x_13 = ((lean_object*)(l_Lake_nameToSharedLib___closed__1));
x_3 = x_13;
goto block_9;
}
}
else
{
goto block_11;
}
block_9:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_string_append(x_3, x_1);
x_5 = ((lean_object*)(l_Lake_nameToSharedLib___closed__0));
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Lake_sharedLibExt;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
block_11:
{
lean_object* x_10; 
x_10 = ((lean_object*)(l_Lake_nameToStaticLib___closed__0));
x_3 = x_10;
goto block_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_nameToSharedLib___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lake_nameToSharedLib(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_sharedLibPathEnvVar(void) {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = l_System_Platform_isOSX;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lake_sharedLibPathEnvVar___closed__0));
return x_3;
}
else
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_Lake_sharedLibPathEnvVar___closed__1));
return x_4;
}
}
else
{
lean_object* x_5; 
x_5 = ((lean_object*)(l_Lake_sharedLibPathEnvVar___closed__2));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_System_SearchPath_parse(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_getSearchPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getSearchPath(x_1);
lean_dec_ref(x_1);
return x_3;
}
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
l_Lake_sharedLibExt = _init_l_Lake_sharedLibExt();
lean_mark_persistent(l_Lake_sharedLibExt);
l_Lake_sharedLibPathEnvVar = _init_l_Lake_sharedLibPathEnvVar();
lean_mark_persistent(l_Lake_sharedLibPathEnvVar);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

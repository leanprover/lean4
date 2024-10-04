// Lean compiler output
// Module: Lake.Load.Config
// Imports: Init Lean.Data.Name Lean.Data.Options Lake.Config.Defaults Lake.Config.Env Lake.Util.Log
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
LEAN_EXPORT lean_object* l_Lake_LoadConfig_relConfigFile___default;
static lean_object* l_Lake_LoadConfig_scope___default___closed__1;
LEAN_EXPORT lean_object* l_Lake_LoadConfig_lakeDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoadConfig_pkgDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoadConfig_relPkgDir___default;
LEAN_EXPORT lean_object* l_Lake_LoadConfig_scope___default;
LEAN_EXPORT lean_object* l_Lake_LoadConfig_leanOpts___default;
LEAN_EXPORT lean_object* l_Lake_LoadConfig_remoteUrl___default;
static lean_object* l_Lake_LoadConfig_relPkgDir___default___closed__1;
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT uint8_t l_Lake_LoadConfig_reconfigure___default;
LEAN_EXPORT lean_object* l_Lake_LoadConfig_lakeOpts___default;
LEAN_EXPORT lean_object* l_Lake_LoadConfig_configFile(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
static lean_object* _init_l_Lake_LoadConfig_relPkgDir___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LoadConfig_relPkgDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LoadConfig_relPkgDir___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_LoadConfig_relConfigFile___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultConfigFile;
return x_1;
}
}
static lean_object* _init_l_Lake_LoadConfig_lakeOpts___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_LoadConfig_leanOpts___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lake_LoadConfig_reconfigure___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lake_LoadConfig_scope___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LoadConfig_scope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LoadConfig_scope___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_LoadConfig_remoteUrl___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LoadConfig_scope___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LoadConfig_pkgDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_join(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_LoadConfig_configFile(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = l_System_FilePath_join(x_2, x_3);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_System_FilePath_join(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_LoadConfig_lakeDir(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_join(x_2, x_3);
lean_dec(x_3);
x_5 = l_Lake_defaultLakeDir;
x_6 = l_System_FilePath_join(x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Defaults(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Env(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Defaults(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Env(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LoadConfig_relPkgDir___default___closed__1 = _init_l_Lake_LoadConfig_relPkgDir___default___closed__1();
lean_mark_persistent(l_Lake_LoadConfig_relPkgDir___default___closed__1);
l_Lake_LoadConfig_relPkgDir___default = _init_l_Lake_LoadConfig_relPkgDir___default();
lean_mark_persistent(l_Lake_LoadConfig_relPkgDir___default);
l_Lake_LoadConfig_relConfigFile___default = _init_l_Lake_LoadConfig_relConfigFile___default();
lean_mark_persistent(l_Lake_LoadConfig_relConfigFile___default);
l_Lake_LoadConfig_lakeOpts___default = _init_l_Lake_LoadConfig_lakeOpts___default();
lean_mark_persistent(l_Lake_LoadConfig_lakeOpts___default);
l_Lake_LoadConfig_leanOpts___default = _init_l_Lake_LoadConfig_leanOpts___default();
lean_mark_persistent(l_Lake_LoadConfig_leanOpts___default);
l_Lake_LoadConfig_reconfigure___default = _init_l_Lake_LoadConfig_reconfigure___default();
l_Lake_LoadConfig_scope___default___closed__1 = _init_l_Lake_LoadConfig_scope___default___closed__1();
lean_mark_persistent(l_Lake_LoadConfig_scope___default___closed__1);
l_Lake_LoadConfig_scope___default = _init_l_Lake_LoadConfig_scope___default();
lean_mark_persistent(l_Lake_LoadConfig_scope___default);
l_Lake_LoadConfig_remoteUrl___default = _init_l_Lake_LoadConfig_remoteUrl___default();
lean_mark_persistent(l_Lake_LoadConfig_remoteUrl___default);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

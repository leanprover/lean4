// Lean compiler output
// Module: Lake.Load.Config
// Imports: public import Lake.Config.Env public import Lake.Config.Lang public import Lake.Config.LakeConfig public import Lake.Load.Manifest
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
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoadConfig_lakeDir(lean_object*);
static const lean_string_object l_Lake_LoadConfig_configDir___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "config"};
static const lean_object* l_Lake_LoadConfig_configDir___closed__0 = (const lean_object*)&l_Lake_LoadConfig_configDir___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LoadConfig_configDir(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LoadConfig_lakeDir(lean_object* v_cfg_1_){
_start:
{
lean_object* v_pkgDir_2_; lean_object* v___x_3_; lean_object* v___x_4_; 
v_pkgDir_2_ = lean_ctor_get(v_cfg_1_, 6);
lean_inc_ref(v_pkgDir_2_);
lean_dec_ref(v_cfg_1_);
v___x_3_ = l_Lake_defaultLakeDir;
v___x_4_ = l_Lake_joinRelative(v_pkgDir_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_LoadConfig_configDir(lean_object* v_cfg_6_){
_start:
{
lean_object* v_wsDir_7_; lean_object* v_pkgIdx_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_wsDir_7_ = lean_ctor_get(v_cfg_6_, 2);
lean_inc_ref(v_wsDir_7_);
v_pkgIdx_8_ = lean_ctor_get(v_cfg_6_, 3);
lean_inc(v_pkgIdx_8_);
lean_dec_ref(v_cfg_6_);
v___x_9_ = l_Lake_defaultLakeDir;
v___x_10_ = l_Lake_joinRelative(v_wsDir_7_, v___x_9_);
v___x_11_ = ((lean_object*)(l_Lake_LoadConfig_configDir___closed__0));
v___x_12_ = l_Lake_joinRelative(v___x_10_, v___x_11_);
v___x_13_ = l_Nat_reprFast(v_pkgIdx_8_);
v___x_14_ = l_Lake_joinRelative(v___x_12_, v___x_13_);
return v___x_14_;
}
}
lean_object* runtime_initialize_Lake_Config_Env(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LakeConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Manifest(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Load_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LakeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Load_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* initialize_Lake_Config_LakeConfig(uint8_t builtin);
lean_object* initialize_Lake_Load_Manifest(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LakeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Manifest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Load_Config(builtin);
}
#ifdef __cplusplus
}
#endif

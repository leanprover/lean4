// Lean compiler output
// Module: Lake.Config.InputFile
// Imports: public import Lake.Config.ConfigTarget
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
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_path(lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputFile_text(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_text___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_path(lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputDir_text(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_text___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_InputDir_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputDir_filter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputFile_path(lean_object* v_self_1_){
_start:
{
lean_object* v_pkg_2_; lean_object* v_config_3_; lean_object* v_dir_4_; lean_object* v_path_5_; lean_object* v___x_6_; 
v_pkg_2_ = lean_ctor_get(v_self_1_, 0);
lean_inc_ref(v_pkg_2_);
v_config_3_ = lean_ctor_get(v_self_1_, 2);
lean_inc(v_config_3_);
lean_dec_ref(v_self_1_);
v_dir_4_ = lean_ctor_get(v_pkg_2_, 4);
lean_inc_ref(v_dir_4_);
lean_dec_ref(v_pkg_2_);
v_path_5_ = lean_ctor_get(v_config_3_, 0);
lean_inc_ref(v_path_5_);
lean_dec(v_config_3_);
v___x_6_ = l_Lake_joinRelative(v_dir_4_, v_path_5_);
return v___x_6_;
}
}
uint8_t l_Lake_InputFile_text(lean_object* v_self_7_){
_start:
{
lean_object* v_config_8_; uint8_t v_text_9_; 
v_config_8_ = lean_ctor_get(v_self_7_, 2);
v_text_9_ = lean_ctor_get_uint8(v_config_8_, sizeof(void*)*1);
return v_text_9_;
}
}
LEAN_EXPORT void l_Lake_InputFile_text_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_7_ = stack[0].m_obj;
uint8_t v_res_10_;
v_res_10_ = l_Lake_InputFile_text(v_self_7_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lake_InputFile_text___boxed(lean_object* v_self_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Lake_InputFile_text(v_self_11_);
lean_dec_ref(v_self_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputDir_path(lean_object* v_self_14_){
_start:
{
lean_object* v_pkg_15_; lean_object* v_config_16_; lean_object* v_dir_17_; lean_object* v_path_18_; lean_object* v___x_19_; 
v_pkg_15_ = lean_ctor_get(v_self_14_, 0);
lean_inc_ref(v_pkg_15_);
v_config_16_ = lean_ctor_get(v_self_14_, 2);
lean_inc(v_config_16_);
lean_dec_ref(v_self_14_);
v_dir_17_ = lean_ctor_get(v_pkg_15_, 4);
lean_inc_ref(v_dir_17_);
lean_dec_ref(v_pkg_15_);
v_path_18_ = lean_ctor_get(v_config_16_, 0);
lean_inc_ref(v_path_18_);
lean_dec(v_config_16_);
v___x_19_ = l_Lake_joinRelative(v_dir_17_, v_path_18_);
return v___x_19_;
}
}
uint8_t l_Lake_InputDir_text(lean_object* v_self_20_){
_start:
{
lean_object* v_config_21_; uint8_t v_text_22_; 
v_config_21_ = lean_ctor_get(v_self_20_, 2);
v_text_22_ = lean_ctor_get_uint8(v_config_21_, sizeof(void*)*2);
return v_text_22_;
}
}
LEAN_EXPORT void l_Lake_InputDir_text_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_20_ = stack[0].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_Lake_InputDir_text(v_self_20_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lake_InputDir_text___boxed(lean_object* v_self_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lake_InputDir_text(v_self_24_);
lean_dec_ref(v_self_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
uint8_t l_Lake_InputDir_filter(lean_object* v_self_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_config_29_; lean_object* v_filter_30_; lean_object* v_filter_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_config_29_ = lean_ctor_get(v_self_27_, 2);
lean_inc(v_config_29_);
lean_dec_ref(v_self_27_);
v_filter_30_ = lean_ctor_get(v_config_29_, 1);
lean_inc_ref(v_filter_30_);
lean_dec(v_config_29_);
v_filter_31_ = lean_ctor_get(v_filter_30_, 0);
lean_inc_ref(v_filter_31_);
lean_dec_ref(v_filter_30_);
v___x_32_ = lean_apply_1(v_filter_31_, v_a_28_);
v___x_33_ = lean_unbox(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_Lake_InputDir_filter_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_27_ = stack[0].m_obj;
lean_object* v_a_28_ = stack[1].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_Lake_InputDir_filter(v_self_27_, v_a_28_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lake_InputDir_filter___boxed(lean_object* v_self_35_, lean_object* v_a_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Lake_InputDir_filter(v_self_35_, v_a_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
lean_object* runtime_initialize_Lake_Config_ConfigTarget(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_InputFile(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_ConfigTarget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_InputFile(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_ConfigTarget(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_InputFile(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_ConfigTarget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_InputFile(builtin);
}
#ifdef __cplusplus
}
#endif

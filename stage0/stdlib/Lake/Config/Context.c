// Lean compiler output
// Module: Lake.Config.Context
// Imports: public import Init.Control.Id public import Lake.Config.Opaque
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
LEAN_EXPORT lean_object* l_Lake_LakeT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LakeT_run___redArg(lean_object* v_ctx_1_, lean_object* v_self_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_self_2_, v_ctx_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeT_run(lean_object* v_m_4_, lean_object* v_00_u03b1_5_, lean_object* v_ctx_6_, lean_object* v_self_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_apply_1(v_self_7_, v_ctx_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeM_run___redArg(lean_object* v_ctx_9_, lean_object* v_self_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_apply_1(v_self_10_, v_ctx_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_LakeM_run(lean_object* v_00_u03b1_12_, lean_object* v_ctx_13_, lean_object* v_self_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_apply_1(v_self_14_, v_ctx_13_);
return v___x_15_;
}
}
lean_object* runtime_initialize_Init_Control_Id(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Opaque(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Context(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Context(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Id(uint8_t builtin);
lean_object* initialize_Lake_Config_Opaque(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Context(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Context(builtin);
}
#ifdef __cplusplus
}
#endif

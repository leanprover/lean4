// Lean compiler output
// Module: Lake.Config.Opaque
// Imports: public import Init.Prelude meta import all Lake.Util.OpaqueType import Lake.Util.OpaqueType
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType;
LEAN_EXPORT lean_object* l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType(lean_object* v_pkgName_2_, lean_object* v_name_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType___boxed(lean_object* v_pkgName_5_, lean_object* v_name_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Lake_Config_Opaque_0__Lake_OpaqueTargetConfig_nonemptyType(v_pkgName_5_, v_name_6_);
lean_dec(v_name_6_);
lean_dec(v_pkgName_5_);
return v_res_7_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_OpaqueType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Opaque(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType = _init_l___private_Lake_Config_Opaque_0__Lake_OpaqueWorkspace_nonemptyType();
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Util_OpaqueType(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Opaque(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin);
lean_object* initialize_Lake_Util_OpaqueType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Opaque(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_OpaqueType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Opaque(builtin);
}
#ifdef __cplusplus
}
#endif

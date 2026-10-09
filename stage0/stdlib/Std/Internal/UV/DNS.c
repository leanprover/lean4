// Lean compiler output
// Module: Std.Internal.UV.DNS
// Imports: public import Init.System.Promise public import Init.Data.SInt public import Std.Net
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
lean_object* lean_uv_dns_get_info(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_DNS_getAddrInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_dns_get_name(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_DNS_getNameInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT void l_Std_Internal_UV_DNS_getAddrInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_host_1_ = stack[0].m_obj;
lean_object* v_service_2_ = stack[1].m_obj;
uint8_t v_family_3_ = stack[2].m_num;
lean_object* v_res_5_;
v_res_5_ = lean_uv_dns_get_info(v_host_1_, v_service_2_, v_family_3_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_DNS_getAddrInfo___boxed(lean_object* v_host_6_, lean_object* v_service_7_, lean_object* v_family_8_, lean_object* v_a_00___x40___internal___hyg_9_){
_start:
{
uint8_t v_family_boxed_10_; lean_object* v_res_11_; 
v_family_boxed_10_ = lean_unbox(v_family_8_);
v_res_11_ = lean_uv_dns_get_info(v_host_6_, v_service_7_, v_family_boxed_10_);
lean_dec_ref(v_service_7_);
lean_dec_ref(v_host_6_);
return v_res_11_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_DNS_getNameInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_host_12_ = stack[0].m_obj;
lean_object* v_res_14_;
v_res_14_ = lean_uv_dns_get_name(v_host_12_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_DNS_getNameInfo___boxed(lean_object* v_host_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lean_uv_dns_get_name(v_host_15_);
lean_dec_ref(v_host_15_);
return v_res_17_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_DNS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_UV_DNS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Init_Data_SInt(uint8_t builtin);
lean_object* initialize_Std_Net(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_DNS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_DNS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_UV_DNS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_UV_DNS(builtin);
}
#ifdef __cplusplus
}
#endif

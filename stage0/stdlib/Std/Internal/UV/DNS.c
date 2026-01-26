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
LEAN_EXPORT lean_object* l_Std_Internal_UV_DNS_getAddrInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = lean_uv_dns_get_info(x_1, x_2, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_DNS_getNameInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_dns_get_name(x_1);
lean_dec_ref(x_1);
return x_3;
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

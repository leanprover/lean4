// Lean compiler output
// Module: Std.Internal.UV.UDP
// Imports: Init.System.IO Init.System.Promise Std.Net
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
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_bind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_connect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_connect___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setBroadcast___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_bind(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_getsockname(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_loop(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastInterface___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getPeerName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_new(lean_object*);
lean_object* lean_uv_udp_set_membership(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_recv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_recv(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl;
lean_object* lean_uv_udp_set_multicast_ttl(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getSockName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_send(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_getpeername(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_ttl(lean_object*, uint32_t, lean_object*);
lean_object* lean_uv_udp_set_multicast_interface(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_broadcast(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastLoop___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_udp_new(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_bind(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_connect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_connect(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_send___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_uv_udp_send(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_recv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_uv_udp_recv(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getPeerName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_udp_getpeername(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_udp_getsockname(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setBroadcast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_uv_udp_set_broadcast(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_uv_udp_set_multicast_loop(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastTTL___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uv_udp_set_multicast_ttl(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMembership___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = lean_uv_udp_set_membership(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastInterface___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_multicast_interface(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setTTL___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uv_udp_set_ttl(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Net(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_UDP(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl = _init_l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.Internal.UV.TCP
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
LEAN_EXPORT lean_object* l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl;
lean_object* lean_uv_tcp_new();
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_new___boxed(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_connect___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_send___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_wait_readable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_waitReadable___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_cancel_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_bind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_listen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_accept___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_try_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_tryAccept___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_cancel_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelAccept___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_shutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_shutdown___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getPeerName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_getsockname(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getSockName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_noDelay___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_tcp_new();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_connect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_connect(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_send___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_send(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_recv_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uv_tcp_recv(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_waitReadable___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_wait_readable(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_cancel_recv(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_bind(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_listen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uv_tcp_listen(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_accept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_accept(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_tryAccept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_try_accept(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelAccept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_cancel_accept(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_shutdown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_shutdown(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getPeerName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getpeername(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getsockname(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_noDelay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_nodelay(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_keepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint32_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_7 = lean_uv_tcp_keepalive(x_1, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Init_Data_SInt(uint8_t builtin);
lean_object* initialize_Std_Net(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_TCP(uint8_t builtin) {
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
l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl = _init_l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

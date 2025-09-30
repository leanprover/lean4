// Lean compiler output
// Module: Std.Internal.Async.TCP
// Imports: public import Std.Time public import Std.Internal.UV.TCP public import Std.Internal.Async.Select public import Std.Net.Addr
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(lean_object*, lean_object*);
static lean_object* l___auto___closed__19____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__4____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_uv_tcp_getsockname(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_cancel_recv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object*, uint64_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__1;
static lean_object* l___auto___closed__14____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__22____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__12____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__25____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen(lean_object*, uint32_t, lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__15____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__6____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__18____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__1;
static lean_object* l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__21____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_isResolved___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk(lean_object*);
static lean_object* l___auto___closed__20____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0;
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t, lean_object*);
lean_object* l_Array_empty(lean_object*);
uint8_t lean_bool_to_int8(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(lean_object*, lean_object*);
static lean_object* l___auto___closed__11____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_uv_tcp_wait_readable(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__7____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object*, lean_object*);
static lean_object* l___auto___closed__13____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t, lean_object*);
static lean_object* l___auto___closed__17____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__24____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___auto___closed__3____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__16____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__8____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__2(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___closed__0;
lean_object* lean_uv_tcp_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_ctorIdx___boxed(lean_object*);
static lean_object* l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__23____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_TCP_Socket_Server_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_TCP_Socket_Client_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_tcp_new(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_bind(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_bind(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_listen(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Server_listen(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec_ref(x_10);
x_19 = l_IO_Promise_result_x21___redArg(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_45; 
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0___boxed), 1, 0);
x_9 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1), 2, 0);
x_45 = lean_uv_tcp_accept(x_1, x_2);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_10 = x_48;
x_11 = x_47;
goto block_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec_ref(x_45);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_10 = x_51;
x_11 = x_50;
goto block_44;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
block_44:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_13, x_9, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
x_3 = x_19;
x_4 = x_18;
goto block_7;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_3 = x_19;
x_4 = x_22;
goto block_7;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec_ref(x_16);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
x_3 = x_23;
x_4 = x_18;
goto block_7;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_3 = x_23;
x_4 = x_26;
goto block_7;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, lean_box(0));
lean_closure_set(x_31, 2, lean_box(0));
lean_closure_set(x_31, 3, x_8);
x_32 = lean_task_map(x_31, x_30, x_14, x_15);
lean_ctor_set(x_17, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, lean_box(0));
lean_closure_set(x_34, 3, x_8);
x_35 = lean_task_map(x_34, x_33, x_14, x_15);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_16, 0, x_36);
return x_16;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_38);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_39 = x_17;
} else {
 lean_dec_ref(x_17);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, lean_box(0));
lean_closure_set(x_40, 2, lean_box(0));
lean_closure_set(x_40, 3, x_8);
x_41 = lean_task_map(x_40, x_38, x_14, x_15);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getsockname(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_nodelay(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__3____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__4____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__3____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__6____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__6____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__8____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__11____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__12____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__13____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__12____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__14____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__15____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__14____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__16____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__17____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__18____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__17____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__15____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__19____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__18____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__13____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__20____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__19____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__11____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__21____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__20____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__22____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__21____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__23____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__22____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__24____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__23____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__7____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__25____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__24____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__25____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__4____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_5 = lean_bool_to_int8(x_2);
x_6 = l_Int_toNat(x_3);
x_7 = lean_uint32_of_nat(x_6);
lean_dec(x_6);
x_8 = lean_uv_tcp_keepalive(x_1, x_5, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_6 = lean_bool_to_int8(x_2);
x_7 = l_Int_toNat(x_3);
x_8 = lean_uint32_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_uv_tcp_keepalive(x_1, x_6, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_tcp_new(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_bind(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_bind(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec_ref(x_10);
x_19 = l_IO_Promise_result_x21___redArg(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0), 2, 0);
x_13 = lean_uv_tcp_connect(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_5 = x_16;
x_6 = x_15;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec_ref(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_5 = x_19;
x_6 = x_18;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_4, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_connect(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0;
x_13 = lean_uv_tcp_send(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_5 = x_16;
x_6 = x_15;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec_ref(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_5 = x_19;
x_6 = x_18;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_4, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0;
x_13 = l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0;
x_14 = lean_array_push(x_13, x_2);
x_15 = lean_uv_tcp_send(x_1, x_14, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_5 = x_18;
x_6 = x_17;
goto block_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_5 = x_21;
x_6 = x_20;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_4, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_send(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec_ref(x_10);
x_19 = l_IO_Promise_result_x21___redArg(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0), 2, 0);
x_13 = lean_uv_tcp_recv(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_5 = x_16;
x_6 = x_15;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec_ref(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_5 = x_19;
x_6 = x_18;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_4, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_io_error_to_string(x_3);
x_5 = lean_mk_io_user_error(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_task_pure(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_13; 
x_13 = lean_uv_tcp_recv(x_3, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_6 = x_16;
x_7 = x_15;
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec_ref(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_6 = x_19;
x_7 = x_18;
goto block_12;
}
block_12:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_1, x_10, x_9, x_2, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_49; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_18 = lean_st_ref_take(x_7, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__0), 1, 0);
x_22 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___closed__0;
x_49 = lean_unbox(x_19);
lean_dec(x_19);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = 1;
x_23 = x_50;
goto block_48;
}
else
{
uint8_t x_51; 
x_51 = 0;
x_23 = x_51;
goto block_48;
}
block_17:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_io_promise_resolve(x_11, x_8, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
block_48:
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_st_ref_set(x_7, x_25, x_20);
if (x_23 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_21);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_apply_1(x_5, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_5);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___redArg(x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_box_uint64(x_3);
x_34 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__2___boxed), 5, 4);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_22);
lean_closure_set(x_34, 2, x_2);
lean_closure_set(x_34, 3, x_33);
x_35 = lean_io_as_task(x_34, x_32, x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_task_bind(x_36, x_21, x_32, x_23);
x_39 = lean_task_get_own(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_9 = x_40;
x_10 = x_37;
goto block_17;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_io_promise_resolve(x_39, x_8, x_37);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_21);
lean_dec(x_2);
x_46 = lean_ctor_get(x_30, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_dec_ref(x_30);
x_9 = x_46;
x_10 = x_47;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_1, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; 
x_8 = lean_uv_tcp_cancel_recv(x_1, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_3 = x_11;
x_4 = x_10;
goto block_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_3 = x_14;
x_4 = x_13;
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec_ref(x_6);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box_uint64(x_3);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__2___boxed), 5, 4);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_20);
x_22 = lean_io_as_task(x_21, x_19, x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_unbox(x_15);
lean_dec(x_15);
x_26 = lean_task_bind(x_23, x_4, x_19, x_25);
x_27 = lean_task_get_own(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = 0;
x_30 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_19, x_29, x_28, x_5, x_24);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = l_IO_Promise_isResolved___redArg(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_2, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
x_6 = x_11;
x_7 = x_5;
goto block_10;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(x_13, x_1, x_2, x_3, x_15, x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_6 = x_17;
x_7 = x_18;
goto block_10;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_20);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(x_24, x_1, x_2, x_3, x_26, x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_6 = x_28;
x_7 = x_29;
goto block_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_32 = x_27;
} else {
 lean_dec_ref(x_27);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
 lean_ctor_set_tag(x_34, 0);
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_box_uint64(x_2);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5___boxed), 5, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_io_promise_result_opt(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = lean_io_map_task(x_7, x_8, x_9, x_10, x_5);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__1;
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1___boxed), 3, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
x_17 = lean_box_uint64(x_3);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___boxed), 5, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_15);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_5, 0, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1___boxed), 3, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_1);
x_24 = lean_box_uint64(x_3);
x_25 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___boxed), 5, 3);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_22);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__0), 1, 0);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___closed__0;
x_8 = lean_box_uint64(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___boxed), 7, 5);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_4);
x_10 = lean_box_uint64(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7___boxed), 6, 4);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_6);
x_19 = lean_uv_tcp_wait_readable(x_1, x_3);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_12 = x_22;
x_13 = x_21;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec_ref(x_19);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_12 = x_25;
x_13 = x_24;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_16, x_14, x_11, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_7 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___lam__2(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_9 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0;
x_12 = lean_uv_tcp_shutdown(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_4 = x_15;
x_5 = x_14;
goto block_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec_ref(x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_4 = x_18;
x_5 = x_17;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_7, x_3, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getpeername(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getsockname(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_nodelay(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_5 = lean_bool_to_int8(x_2);
x_6 = l_Int_toNat(x_3);
x_7 = lean_uint32_of_nat(x_6);
lean_dec(x_6);
x_8 = lean_uv_tcp_keepalive(x_1, x_5, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_6 = lean_bool_to_int8(x_2);
x_7 = l_Int_toNat(x_3);
x_8 = lean_uint32_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_uv_tcp_keepalive(x_1, x_6, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Std_Time(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_UV_TCP(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Net_Addr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_TCP(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_TCP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net_Addr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__3____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__3____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__3____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__4____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__4____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__4____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__6____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__6____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__6____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__7____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__7____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__7____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__8____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__8____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__8____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__11____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__11____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__11____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__12____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__12____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__12____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__13____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__13____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__13____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__14____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__14____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__14____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__15____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__15____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__15____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__16____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__16____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__16____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__17____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__17____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__17____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__18____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__18____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__18____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__19____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__19____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__19____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__20____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__20____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__20____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__21____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__21____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__21____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__22____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__22____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__22____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__23____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__23____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__23____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__24____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__24____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__24____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__25____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__25____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__25____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0);
l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___closed__0 = _init_l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__1 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__1);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__1 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___closed__1);
l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_ = _init_l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

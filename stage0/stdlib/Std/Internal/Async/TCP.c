// Lean compiler output
// Module: Std.Internal.Async.TCP
// Imports: public import Std.Time public import Std.Internal.UV.TCP public import Std.Internal.Async.Select
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(lean_object*);
static lean_object* l___auto___closed__19_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___closed__0;
static lean_object* l___auto___closed__4_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_uv_tcp_getsockname(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_cancel_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__2(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__0(lean_object*);
static lean_object* l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg(lean_object*, uint8_t, lean_object*);
lean_object* lean_uv_tcp_cancel_accept(lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*);
static lean_object* l___auto___closed__14_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
static lean_object* l___auto___closed__22_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__12_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0;
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
static lean_object* l___auto___closed__25_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen(lean_object*, uint32_t);
lean_object* lean_uv_tcp_nodelay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_new();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__15_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__6_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__18_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__21_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___boxed(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk();
static lean_object* l___auto___closed__20_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0;
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
lean_object* l_Array_empty(lean_object*);
uint8_t lean_bool_to_int8(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__26_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(lean_object*);
static lean_object* l___auto___closed__11_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__9_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_wait_readable(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1;
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object*, uint64_t, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__7_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object*);
static lean_object* l___auto___closed__13_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t);
static lean_object* l___auto___closed__17_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l___auto___closed__24_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l___auto_00___x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg(lean_object*, uint8_t, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___boxed(lean_object*, lean_object*);
static lean_object* l___auto___closed__3_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__16_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1;
static lean_object* l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___auto___closed__8_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___closed__0;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_try_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk___boxed(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_uv_tcp_shutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_ctorIdx___boxed(lean_object*);
static lean_object* l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___auto___closed__23_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__4(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___auto___closed__10_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_tcp_new();
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_TCP_Socket_Server_mk();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_bind(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_bind(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_listen(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Server_listen(x_1, x_4);
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
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec_ref(x_9);
x_16 = lean_io_promise_result_opt(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_task_map(x_1, x_16, x_17, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the promise linked to the Async was dropped", 43, 43);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_34; 
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0___boxed), 1, 0);
x_8 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0;
x_9 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__2___boxed), 3, 1);
lean_closure_set(x_10, 0, x_9);
x_34 = lean_uv_tcp_accept(x_1);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 1);
x_11 = x_34;
x_12 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_11 = x_37;
x_12 = lean_box(0);
goto block_33;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_ctor_set_tag(x_34, 0);
x_11 = x_34;
x_12 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_11 = x_40;
x_12 = lean_box(0);
goto block_33;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
block_33:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_16, x_14, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
x_3 = lean_box(0);
x_4 = x_18;
goto block_6;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_3 = lean_box(0);
x_4 = x_21;
goto block_6;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
x_3 = lean_box(0);
x_4 = x_18;
goto block_6;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_3 = lean_box(0);
x_4 = x_24;
goto block_6;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, lean_box(0));
lean_closure_set(x_27, 2, lean_box(0));
lean_closure_set(x_27, 3, x_7);
x_28 = lean_task_map(x_27, x_26, x_15, x_16);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, lean_box(0));
lean_closure_set(x_30, 3, x_7);
x_31 = lean_task_map(x_30, x_29, x_15, x_16);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__2(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_io_error_to_string), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_try_accept(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___closed__0;
x_6 = l_IO_ofExcept___redArg(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(1, 1, 0);
} else {
 x_18 = x_17;
}
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_io_error_to_string(x_4);
x_6 = lean_mk_io_user_error(x_5);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_io_error_to_string(x_7);
x_9 = lean_mk_io_user_error(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_st_ref_take(x_5);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
uint8_t x_32; 
x_32 = 1;
x_9 = x_32;
goto block_31;
}
else
{
uint8_t x_33; 
x_33 = 0;
x_9 = x_33;
goto block_31;
}
block_31:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_st_ref_set(x_5, x_11);
if (x_9 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_1);
x_13 = lean_apply_1(x_3, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; 
lean_dec_ref(x_3);
x_14 = l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(x_1);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_io_promise_resolve(x_17, x_6);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_io_promise_resolve(x_20, x_6);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_io_promise_resolve(x_25, x_6);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_io_promise_resolve(x_28, x_6);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; lean_object* x_8; lean_object* x_11; 
x_11 = lean_uv_tcp_try_accept(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_16 = x_19;
goto block_18;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
x_16 = x_14;
goto block_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_16 = x_22;
goto block_18;
}
}
block_18:
{
lean_object* x_17; 
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(1, 1, 0);
} else {
 x_17 = x_15;
 lean_ctor_set_tag(x_17, 1);
}
lean_ctor_set(x_17, 0, x_16);
x_3 = x_17;
x_4 = lean_box(0);
goto block_6;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec_ref(x_13);
x_7 = x_23;
x_8 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec_ref(x_11);
x_7 = x_24;
x_8 = lean_box(0);
goto block_10;
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
block_10:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_3 = x_9;
x_4 = lean_box(0);
goto block_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__1(x_6, x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_1);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_io_promise_result_opt(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = l_EIO_chainTask___redArg(x_15, x_1, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_ctor_set(x_2, 0, x_19);
x_4 = x_2;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_20);
x_4 = x_2;
x_5 = lean_box(0);
goto block_7;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_io_promise_result_opt(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 0;
x_25 = l_EIO_chainTask___redArg(x_22, x_1, x_23, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_4 = x_27;
x_5 = lean_box(0);
goto block_7;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_4 = x_29;
x_5 = lean_box(0);
goto block_7;
}
}
}
block_7:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_13 = lean_uv_tcp_accept(x_1);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
x_6 = x_13;
x_7 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_6 = x_16;
x_7 = lean_box(0);
goto block_12;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_6 = x_13;
x_7 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_6 = x_19;
x_7 = lean_box(0);
goto block_12;
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__5(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; 
x_7 = lean_uv_tcp_cancel_accept(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_3 = x_10;
x_4 = lean_box(0);
goto block_6;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_ctor_set_tag(x_7, 0);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = lean_box(0);
goto block_6;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__0(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__2(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__3(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__4(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__5(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getsockname(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_nodelay(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__3_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__4_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__3_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___auto___closed__6_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto___closed__7_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__6_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__8_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto___closed__9_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__8_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__10_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto___closed__11_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__10_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__12_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto___closed__10_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l___auto___closed__13_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__12_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__14_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto___closed__15_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto___closed__14_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_4 = l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___auto___closed__16_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__9_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__17_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__16_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__18_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__17_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__15_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__19_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__18_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__13_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__20_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__19_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__11_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__21_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__20_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__22_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__21_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__9_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__23_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__22_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__24_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__23_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__7_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto___closed__25_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto___closed__24_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___auto___closed__26_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto___closed__25_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_2 = l___auto___closed__4_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___auto_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__26_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_5 = lean_bool_to_int8(x_2);
x_6 = l_Int_toNat(x_3);
x_7 = lean_uint32_of_nat(x_6);
lean_dec(x_6);
x_8 = lean_uv_tcp_keepalive(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_6 = lean_bool_to_int8(x_2);
x_7 = l_Int_toNat(x_3);
x_8 = lean_uint32_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_uv_tcp_keepalive(x_1, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg(x_1, x_5, x_3);
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
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(x_1, x_6, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_tcp_new();
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_TCP_Socket_Client_mk();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_bind(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_bind(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec_ref(x_9);
x_16 = lean_io_promise_result_opt(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_task_map(x_1, x_16, x_17, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0;
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_15 = lean_uv_tcp_connect(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
x_7 = x_15;
x_8 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_7 = x_18;
x_8 = lean_box(0);
goto block_14;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_7 = x_15;
x_8 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_7 = x_21;
x_8 = lean_box(0);
goto block_14;
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_11, x_12, x_10, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_connect(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_connect___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1;
x_13 = lean_uv_tcp_send(x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
x_5 = x_13;
x_6 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_5 = x_13;
x_6 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_5 = x_19;
x_6 = lean_box(0);
goto block_12;
}
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
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0;
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1;
x_15 = lean_uv_tcp_send(x_1, x_5);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
x_7 = x_15;
x_8 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_7 = x_18;
x_8 = lean_box(0);
goto block_14;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_7 = x_15;
x_8 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_7 = x_21;
x_8 = lean_box(0);
goto block_14;
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_11, x_12, x_10, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_send(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec_ref(x_9);
x_16 = lean_io_promise_result_opt(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_task_map(x_1, x_16, x_17, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0;
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_15 = lean_uv_tcp_recv(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
x_7 = x_15;
x_8 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_7 = x_18;
x_8 = lean_box(0);
goto block_14;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_7 = x_15;
x_8 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_7 = x_21;
x_8 = lean_box(0);
goto block_14;
}
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_11, x_12, x_10, x_6);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec_ref(x_10);
x_17 = lean_io_promise_result_opt(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_task_map(x_1, x_17, x_2, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; 
x_5 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___closed__0;
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_14 = lean_uv_tcp_recv(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
x_7 = x_14;
x_8 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_7 = x_17;
x_8 = lean_box(0);
goto block_13;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_ctor_set_tag(x_14, 0);
x_7 = x_14;
x_8 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_7 = x_20;
x_8 = lean_box(0);
goto block_13;
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_1, x_11, x_10, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_15 = lean_st_ref_take(x_7);
x_16 = lean_unbox(x_15);
x_17 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0), 1, 0);
if (x_16 == 0)
{
uint8_t x_45; 
x_45 = 1;
x_18 = x_45;
goto block_44;
}
else
{
uint8_t x_46; 
x_46 = 0;
x_18 = x_46;
goto block_44;
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_io_promise_resolve(x_11, x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_44:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_st_ref_set(x_7, x_20);
if (x_18 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_22 = lean_apply_1(x_5, lean_box(0));
return x_22;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_5);
x_23 = l_IO_ofExcept___at___00Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(x_1);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_box_uint64(x_3);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_27);
x_29 = lean_io_as_task(x_28, x_26);
x_30 = lean_task_bind(x_29, x_17, x_26, x_18);
x_31 = lean_task_get_own(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_free_object(x_23);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_9 = x_32;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_33; 
x_33 = lean_io_promise_resolve(x_31, x_8);
lean_ctor_set(x_23, 0, x_33);
return x_23;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_box_uint64(x_3);
x_36 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_35);
x_37 = lean_io_as_task(x_36, x_34);
x_38 = lean_task_bind(x_37, x_17, x_34, x_18);
x_39 = lean_task_get_own(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_9 = x_40;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_io_promise_resolve(x_39, x_8);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_17);
lean_dec(x_2);
x_43 = lean_ctor_get(x_23, 0);
lean_inc(x_43);
lean_dec_ref(x_23);
x_9 = x_43;
x_10 = lean_box(0);
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_1, 0, x_10);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; 
x_7 = lean_uv_tcp_cancel_recv(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_3 = x_10;
x_4 = lean_box(0);
goto block_6;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_ctor_set_tag(x_7, 0);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = lean_box(0);
goto block_6;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
x_6 = x_10;
x_7 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0;
x_13 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0(x_11, x_1, x_2, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_6 = x_14;
x_7 = lean_box(0);
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_ctor_set_tag(x_13, 0);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_io_promise_result_opt(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = lean_io_map_task(x_1, x_10, x_11, x_12);
lean_dec_ref(x_13);
x_14 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; 
x_5 = lean_box_uint64(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___boxed), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_15 = lean_uv_tcp_wait_readable(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
x_8 = x_15;
x_9 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_8 = x_18;
x_9 = lean_box(0);
goto block_14;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_8 = x_15;
x_9 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_8 = x_21;
x_9 = lean_box(0);
goto block_14;
}
}
block_14:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
x_13 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_11, x_12, x_10, x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_14 = lean_ctor_get(x_6, 0);
x_22 = lean_unbox(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_23 = lean_uv_tcp_cancel_recv(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_ctor_set(x_6, 0, x_24);
x_15 = x_6;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_25);
x_15 = x_6;
x_16 = lean_box(0);
goto block_21;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
lean_free_object(x_6);
lean_dec_ref(x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_box_uint64(x_3);
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_27);
x_29 = lean_io_as_task(x_28, x_26);
x_30 = lean_unbox(x_14);
lean_dec(x_14);
x_31 = lean_task_bind(x_29, x_4, x_26, x_30);
x_32 = lean_task_get_own(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = 0;
x_35 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_26, x_34, x_33, x_5);
return x_35;
}
block_21:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_unbox(x_14);
lean_dec(x_14);
x_20 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_18, x_19, x_17, x_1);
return x_20;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_44; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_44 = lean_unbox(x_36);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_45 = lean_uv_tcp_cancel_recv(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_37 = x_47;
x_38 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_37 = x_49;
x_38 = lean_box(0);
goto block_43;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
lean_dec_ref(x_1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_box_uint64(x_3);
x_52 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed), 4, 3);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_2);
lean_closure_set(x_52, 2, x_51);
x_53 = lean_io_as_task(x_52, x_50);
x_54 = lean_unbox(x_36);
lean_dec(x_36);
x_55 = lean_task_bind(x_53, x_4, x_50, x_54);
x_56 = lean_task_get_own(x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = 0;
x_59 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_50, x_58, x_57, x_5);
return x_59;
}
block_43:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_unbox(x_36);
lean_dec(x_36);
x_42 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_40, x_41, x_39, x_1);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_IO_Promise_isResolved___redArg(x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
lean_ctor_set(x_2, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_13, x_1);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_IO_Promise_isResolved___redArg(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_23, x_21, x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_11; 
x_11 = lean_uv_tcp_wait_readable(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 1);
x_4 = x_11;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_4 = x_14;
x_5 = lean_box(0);
goto block_10;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_ctor_set_tag(x_11, 0);
x_4 = x_11;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_4 = x_17;
x_5 = lean_box(0);
goto block_10;
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___boxed), 2, 0);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_box_uint64(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_box_uint64(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__9___boxed), 7, 5);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(x_1, x_2, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0(x_1, x_2, x_7, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4(x_1, x_6, x_3, x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__5(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_9 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__9(x_1, x_2, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__6(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__7(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1;
x_12 = lean_uv_tcp_shutdown(x_1);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
x_4 = x_12;
x_5 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_4 = x_15;
x_5 = lean_box(0);
goto block_11;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_4 = x_12;
x_5 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_4 = x_18;
x_5 = lean_box(0);
goto block_11;
}
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
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_7, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getpeername(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getsockname(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_nodelay(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto_00___x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto___closed__26_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_5 = lean_bool_to_int8(x_2);
x_6 = l_Int_toNat(x_3);
x_7 = lean_uint32_of_nat(x_6);
lean_dec(x_6);
x_8 = lean_uv_tcp_keepalive(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_6 = lean_bool_to_int8(x_2);
x_7 = l_Int_toNat(x_3);
x_8 = lean_uint32_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_uv_tcp_keepalive(x_1, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg(x_1, x_5, x_3);
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
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(x_1, x_6, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_TCP(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_TCP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Server_tryAccept___closed__0);
l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__0_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__1_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__2_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__3_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__3_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__3_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__4_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__4_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__4_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__5_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__6_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__6_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__6_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__7_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__7_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__7_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__8_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__8_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__8_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__9_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__9_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__9_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__10_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__10_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__10_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__11_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__11_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__11_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__12_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__12_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__12_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__13_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__13_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__13_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__14_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__14_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__14_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__15_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__15_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__15_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__16_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__16_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__16_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__17_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__17_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__17_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__18_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__18_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__18_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__19_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__19_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__19_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__20_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__20_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__20_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__21_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__21_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__21_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__22_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__22_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__22_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__23_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__23_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__23_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__24_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__24_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__24_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__25_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__25_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__25_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto___closed__26_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto___closed__26_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto___closed__26_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l___auto_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_ = _init_l___auto_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_();
lean_mark_persistent(l___auto_00___x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_);
l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_sendAll___closed__1);
l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_send___closed__0);
l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___closed__0 = _init_l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__4___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0);
l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1 = _init_l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1);
l___auto_00___x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_ = _init_l___auto_00___x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_();
lean_mark_persistent(l___auto_00___x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

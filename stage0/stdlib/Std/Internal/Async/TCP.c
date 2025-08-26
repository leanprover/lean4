// Lean compiler output
// Module: Std.Internal.Async.TCP
// Imports: Std.Time Std.Internal.UV.TCP Std.Internal.Async.Select Std.Net.Addr
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
lean_object* lean_uv_tcp_getsockname(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object*, uint64_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___auto___closed__0____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*, lean_object*);
static lean_object* l___auto___closed__14____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__22____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__12____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l___auto____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__25____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen(lean_object*, uint32_t, lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object*, lean_object*);
lean_object* lean_uv_tcp_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__15____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__6____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__18____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__1____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__21____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_isResolved___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk(lean_object*);
static lean_object* l___auto___closed__20____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t, lean_object*);
lean_object* l_Array_empty(lean_object*);
uint8_t lean_bool_to_int8(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__26____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(lean_object*, lean_object*);
static lean_object* l___auto___closed__11____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__9____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_uv_tcp_wait_readable(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_AsyncTask_block___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__7____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object*, lean_object*, uint64_t, lean_object*);
static lean_object* l___auto___closed__13____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t, lean_object*);
static lean_object* l___auto___closed__17____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__24____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___auto___closed__3____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__16____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
static lean_object* l___auto___closed__2____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__8____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_uv_tcp_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__5____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__23____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto___closed__10____x40_Std_Internal_Async_TCP_2897352522____hygCtx___hyg_6_;
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
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_accept(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0), 1, 0);
x_7 = l_IO_Promise_result_x21___redArg(x_5);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = lean_task_map(x_6, x_7, x_8, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lam__0), 1, 0);
x_14 = l_IO_Promise_result_x21___redArg(x_11);
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = lean_task_map(x_13, x_14, x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_connect(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_IO_Promise_result_x21___redArg(x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_IO_Promise_result_x21___redArg(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_send(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_IO_Promise_result_x21___redArg(x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_IO_Promise_result_x21___redArg(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_recv(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_IO_Promise_result_x21___redArg(x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_IO_Promise_result_x21___redArg(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_50; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_18 = lean_st_ref_take(x_7, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_50 = lean_unbox(x_19);
lean_dec(x_19);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = 1;
x_21 = x_51;
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = 0;
x_21 = x_52;
goto block_49;
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
block_49:
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_st_ref_set(x_7, x_23, x_20);
if (x_21 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_apply_1(x_5, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_5);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec_ref(x_24);
x_28 = l_IO_ofExcept___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__0___redArg(x_1, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_uv_tcp_recv(x_2, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_IO_Promise_result_x21___redArg(x_31);
lean_dec(x_31);
x_34 = l_Std_Internal_IO_Async_AsyncTask_block___redArg(x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_io_promise_resolve(x_37, x_8, x_36);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec_ref(x_34);
x_9 = x_43;
x_10 = x_44;
goto block_17;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_30, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec_ref(x_30);
x_9 = x_45;
x_10 = x_46;
goto block_17;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_dec_ref(x_28);
x_9 = x_47;
x_10 = x_48;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_IO_Promise_isResolved___redArg(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec_ref(x_5);
x_15 = lean_uv_tcp_recv(x_2, x_3, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_IO_Promise_result_x21___redArg(x_16);
lean_dec(x_16);
x_19 = l_Std_Internal_IO_Async_AsyncTask_block___redArg(x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
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
x_15 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg(x_13, x_1, x_2, x_3, x_15, x_5);
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
x_26 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__1), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg(x_24, x_1, x_2, x_3, x_26, x_5);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_box_uint64(x_2);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed), 5, 3);
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
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_wait_readable(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box_uint64(x_2);
lean_inc(x_1);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___boxed), 4, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_7);
x_9 = lean_box_uint64(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_6);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_box_uint64(x_2);
lean_inc(x_1);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___boxed), 4, 3);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_box_uint64(x_2);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___boxed), 5, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_13);
x_19 = lean_alloc_closure((void*)(l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed), 2, 1);
lean_closure_set(x_19, 0, x_1);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_8 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___redArg(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_9 = l_Std_Internal_IO_Async_Waiter_race___at___Std_Internal_IO_Async_TCP_Socket_Client_recvSelector_spec__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__0(x_1, x_2, x_5, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__2(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_recvSelector___lam__3(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
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
lean_object* x_3; 
x_3 = lean_uv_tcp_shutdown(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_IO_Promise_result_x21___redArg(x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_IO_Promise_result_x21___redArg(x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
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
l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_ = _init_l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP_2897352523____hygCtx___hyg_6_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

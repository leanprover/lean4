// Lean compiler output
// Module: Std.Internal.Async.UDP
// Imports: public import Std.Time public import Std.Internal.UV.UDP public import Std.Internal.Async.Select
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_udp_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorIdx(uint8_t);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_bind(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_udp_wait_readable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__6(lean_object*, uint64_t, lean_object*);
lean_object* lean_uv_udp_getsockname(lean_object*);
lean_object* lean_uv_udp_set_multicast_loop(lean_object*, uint8_t);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__1;
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_send___closed__0;
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface(lean_object*, lean_object*);
lean_object* lean_uv_udp_new();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_membership(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__10(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_mk();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___redArg(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_udp_recv(lean_object*, uint64_t);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___closed__1;
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop(lean_object*, uint8_t);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0(lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL(lean_object*, uint32_t);
lean_object* lean_task_get_own(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_ttl(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__1;
static lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorIdx___boxed(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__1(lean_object*);
lean_object* lean_uv_udp_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_cancel_recv(lean_object*);
lean_object* lean_uv_udp_getpeername(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName___boxed(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_ttl(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_interface(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_broadcast(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Internal_IO_Async_UDP_Membership_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_UDP_Membership_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_UDP_Membership_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Std_Internal_IO_Async_UDP_Membership_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_UDP_Membership_leaveGroup_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Internal_IO_Async_UDP_Membership_enterGroup_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_mk() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_udp_new();
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_UDP_Socket_mk();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_bind(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_bind(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_connect(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_connect(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__1(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the promise linked to the Async was dropped", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__1;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_sendAll___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; 
x_5 = l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__2;
x_14 = lean_uv_udp_send(x_1, x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
x_6 = x_14;
x_7 = lean_box(0);
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
x_6 = x_17;
x_7 = lean_box(0);
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
x_6 = x_14;
x_7 = lean_box(0);
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
x_6 = x_20;
x_7 = lean_box(0);
goto block_13;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_sendAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_UDP_Socket_sendAll(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_send___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; 
x_5 = l_Std_Internal_IO_Async_UDP_Socket_send___closed__0;
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__2;
x_16 = lean_uv_udp_send(x_1, x_6, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
x_8 = x_16;
x_9 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_8 = x_19;
x_9 = lean_box(0);
goto block_15;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_8 = x_16;
x_9 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_8 = x_22;
x_9 = lean_box(0);
goto block_15;
}
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_UDP_Socket_send(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_recv___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_recv___lam__1(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recv___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recv___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recv___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_UDP_Socket_recv___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recv___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_recv___closed__1;
x_13 = lean_uv_udp_recv(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_recv(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__2(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1(lean_object* x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; 
x_5 = l_Std_Internal_IO_Async_UDP_Socket_recv___closed__0;
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_14 = lean_uv_udp_recv(x_2, x_3);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1(x_1, x_2, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_29; uint8_t x_37; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_15 = lean_st_ref_take(x_7);
x_16 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___closed__0;
x_37 = lean_unbox(x_15);
lean_dec(x_15);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = 1;
x_29 = x_38;
goto block_36;
}
else
{
uint8_t x_39; 
x_39 = 0;
x_29 = x_39;
goto block_36;
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
block_28:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_box_uint64(x_2);
x_21 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed), 4, 3);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_20);
x_22 = lean_io_as_task(x_21, x_19);
x_23 = lean_task_bind(x_22, x_16, x_19, x_17);
x_24 = lean_task_get_own(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_9 = x_25;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_io_promise_resolve(x_24, x_8);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
block_36:
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_st_ref_set(x_7, x_31);
if (x_29 == 0)
{
lean_object* x_33; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_33 = lean_apply_1(x_5, lean_box(0));
return x_33;
}
else
{
lean_object* x_34; 
lean_dec_ref(x_5);
x_34 = l_IO_ofExcept___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__0___redArg(x_3);
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
x_17 = x_29;
x_18 = lean_box(0);
goto block_28;
}
else
{
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
x_17 = x_29;
x_18 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_9 = x_35;
x_10 = lean_box(0);
goto block_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_8 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1(x_1, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__1(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0(lean_object* x_1) {
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
x_8 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; 
x_7 = lean_uv_udp_cancel_recv(x_1);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__2(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__3(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__3___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___closed__0;
x_13 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1(x_1, x_2, x_11, x_3, x_12);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4(x_1, x_6, x_3, x_4);
lean_dec_ref(x_3);
return x_7;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5(lean_object* x_1, lean_object* x_2) {
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
x_14 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__1;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__6(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; 
x_5 = lean_box_uint64(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___boxed), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_15 = lean_uv_udp_wait_readable(x_1);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__6(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__10(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_23 = lean_uv_udp_cancel_recv(x_2);
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
x_28 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed), 4, 3);
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
x_45 = lean_uv_udp_cancel_recv(x_2);
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
x_52 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed), 4, 3);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_9 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__10(x_1, x_2, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__7(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_11; 
x_11 = lean_uv_udp_wait_readable(x_2);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__8(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___closed__0;
x_4 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__0;
x_5 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__1;
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_box_uint64(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__6___boxed), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_box_uint64(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__10___boxed), 7, 5);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
x_11 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__8___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recvSelector___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_Internal_IO_Async_UDP_Socket_recvSelector(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_udp_getsockname(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_getSockName(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_udp_getpeername(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_getPeerName(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_broadcast(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setBroadcast(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_multicast_loop(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_multicast_ttl(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = lean_uv_udp_set_membership(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = lean_uv_udp_set_membership(x_1, x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_Std_Internal_IO_Async_UDP_Socket_setMembership(x_1, x_2, x_3, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_multicast_interface(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_ttl(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setTTL(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_UDP(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_UDP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__0 = _init_l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__1 = _init_l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__1);
l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__2 = _init_l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_sendAll___closed__2);
l_Std_Internal_IO_Async_UDP_Socket_send___closed__0 = _init_l_Std_Internal_IO_Async_UDP_Socket_send___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_send___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_recv___closed__0 = _init_l_Std_Internal_IO_Async_UDP_Socket_recv___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recv___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_recv___closed__1 = _init_l_Std_Internal_IO_Async_UDP_Socket_recv___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recv___closed__1);
l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___closed__0 = _init_l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_UDP_Socket_recvSelector_spec__1___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__0 = _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__1 = _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__0___closed__1);
l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___closed__0 = _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__4___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__0 = _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__1 = _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___lam__5___closed__1);
l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__0 = _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__0);
l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__1 = _init_l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Socket_recvSelector___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

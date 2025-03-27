// Lean compiler output
// Module: Std.Internal.Async.UDP
// Imports: Std.Time Std.Internal.UV Std.Internal.Async.Basic Std.Net.Addr
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion(lean_object*);
lean_object* lean_uv_udp_connect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___closed__1;
lean_object* lean_uv_udp_getsockname(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_loop(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_new(lean_object*);
lean_object* lean_uv_udp_set_membership(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx(uint8_t);
lean_object* lean_uv_udp_recv(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL(lean_object*, uint32_t, lean_object*);
lean_object* lean_uv_udp_set_multicast_ttl(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_send(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_getpeername(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_ttl(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_interface(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_broadcast(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Internal_IO_Async_UDP_Membership_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_udp_new(x_1);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_bind(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_bind(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_connect(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_connect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_connect(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_uv_udp_send(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_IO_Promise_result_x21___rarg(x_7);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_IO_Promise_result_x21___rarg(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_send___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_UDP_Socket_send(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_recv(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_IO_Promise_result_x21___rarg(x_6);
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
x_10 = l_IO_Promise_result_x21___rarg(x_8);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_recv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_recv(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_udp_getsockname(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_getSockName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_udp_getpeername(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_getPeerName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_UDP_Socket_getPeerName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_broadcast(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setBroadcast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setBroadcast(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_multicast_loop(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setMulticastLoop(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_multicast_ttl(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setMulticastTTL(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = lean_uv_udp_set_membership(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = lean_uv_udp_set_membership(x_1, x_2, x_3, x_8, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMembership___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Std_Internal_IO_Async_UDP_Socket_setMembership(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_multicast_interface(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_UDP_Socket_setMulticastInterface(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_udp_set_ttl(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_UDP_Socket_setTTL___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_UDP_Socket_setTTL(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Std_Time(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_UV(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Net_Addr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_UDP(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net_Addr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___closed__1 = _init_l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_UDP_Membership_noConfusion___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

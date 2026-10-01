// Lean compiler output
// Module: Std.Async.UDP
// Imports: public import Std.Time public import Std.Internal.UV.UDP public import Std.Async.Select
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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_udp_recv(lean_object*, uint64_t);
lean_object* lean_uv_udp_set_ttl(lean_object*, uint32_t);
lean_object* lean_uv_udp_send(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_getsockname(lean_object*);
lean_object* lean_uv_udp_set_broadcast(lean_object*, uint8_t);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_uv_udp_wait_readable(lean_object*);
lean_object* lean_uv_udp_cancel_recv(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_uv_udp_new();
lean_object* lean_uv_udp_connect(lean_object*, lean_object*);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* lean_uv_udp_set_multicast_loop(lean_object*, uint8_t);
lean_object* lean_uv_udp_set_multicast_interface(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_ttl(lean_object*, uint32_t);
lean_object* lean_uv_udp_getpeername(lean_object*);
lean_object* lean_uv_udp_set_membership(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_udp_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_mk();
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_connect___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_UDP_Socket_sendAll___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Async_UDP_Socket_sendAll___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_sendAll___closed__0_value;
static const lean_closure_object l_Std_Async_UDP_Socket_sendAll___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_sendAll___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_sendAll___closed__0_value)} };
static const lean_object* l_Std_Async_UDP_Socket_sendAll___closed__1 = (const lean_object*)&l_Std_Async_UDP_Socket_sendAll___closed__1_value;
static const lean_closure_object l_Std_Async_UDP_Socket_sendAll___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_sendAll___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_sendAll___closed__1_value)} };
static const lean_object* l_Std_Async_UDP_Socket_sendAll___closed__2 = (const lean_object*)&l_Std_Async_UDP_Socket_sendAll___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_UDP_Socket_recv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recv___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_sendAll___closed__0_value)} };
static const lean_object* l_Std_Async_UDP_Socket_recv___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recv___closed__0_value;
static const lean_closure_object l_Std_Async_UDP_Socket_recv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recv___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_recv___closed__0_value)} };
static const lean_object* l_Std_Async_UDP_Socket_recv___closed__1 = (const lean_object*)&l_Std_Async_UDP_Socket_recv___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "the promise linked to the Async Task was dropped"};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0_value;
static const lean_closure_object l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recv___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0_value)} };
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__1 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__0_value)}};
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__1 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0_value;
static const lean_ctor_object l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0_value)}};
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_UDP_Socket_recvSelector___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_recv___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_UDP_Socket_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___closed__0_value;
static const lean_closure_object l_Std_Async_UDP_Socket_recvSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___closed__1 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getSockName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getPeerName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getPeerName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setBroadcast(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setBroadcast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastLoop(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastLoop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastTTL(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMembership(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastInterface(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastInterface___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setTTL(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setTTL___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Async_UDP_Membership_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Async_UDP_Membership_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Async_UDP_Membership_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(lean_object* v_leaveGroup_22_){
_start:
{
lean_inc(v_leaveGroup_22_);
return v_leaveGroup_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg___boxed(lean_object* v_leaveGroup_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(v_leaveGroup_23_);
lean_dec(v_leaveGroup_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_leaveGroup_28_){
_start:
{
lean_inc(v_leaveGroup_28_);
return v_leaveGroup_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_leaveGroup_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Async_UDP_Membership_leaveGroup_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_leaveGroup_32_);
lean_dec(v_leaveGroup_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg(lean_object* v_enterGroup_35_){
_start:
{
lean_inc(v_enterGroup_35_);
return v_enterGroup_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg___boxed(lean_object* v_enterGroup_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Async_UDP_Membership_enterGroup_elim___redArg(v_enterGroup_36_);
lean_dec(v_enterGroup_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_enterGroup_41_){
_start:
{
lean_inc(v_enterGroup_41_);
return v_enterGroup_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_enterGroup_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Async_UDP_Membership_enterGroup_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_enterGroup_45_);
lean_dec(v_enterGroup_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_mk(){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_uv_udp_new();
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
v_a_58_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_49_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_49_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_mk___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Async_UDP_Socket_mk();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_bind(lean_object* v_s_68_, lean_object* v_addr_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_uv_udp_bind(v_s_68_, v_addr_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_bind___boxed(lean_object* v_s_72_, lean_object* v_addr_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Async_UDP_Socket_bind(v_s_72_, v_addr_73_);
lean_dec_ref(v_addr_73_);
lean_dec(v_s_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_connect(lean_object* v_s_76_, lean_object* v_addr_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_uv_udp_connect(v_s_76_, v_addr_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_connect___boxed(lean_object* v_s_80_, lean_object* v_addr_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Async_UDP_Socket_connect(v_s_80_, v_addr_81_);
lean_dec_ref(v_addr_81_);
lean_dec(v_s_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0(lean_object* v___x_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_mk_io_user_error(v___x_84_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v_val_88_; 
lean_dec_ref(v___x_84_);
v_val_88_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_val_88_);
return v_val_88_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0___boxed(lean_object* v___x_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_Async_UDP_Socket_sendAll___lam__0(v___x_89_, v_x_90_);
lean_dec(v_x_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1(lean_object* v___f_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v___f_92_);
v_a_95_ = lean_ctor_get(v_x_93_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_103_ == 0)
{
v___x_97_ = v_x_93_;
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v_x_93_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_103_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_102_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
else
{
lean_object* v_a_104_; 
v_a_104_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v_x_93_, 1);
if (lean_obj_tag(v_a_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
lean_dec_ref(v___f_92_);
v_a_105_ = lean_ctor_get(v_a_104_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v_a_104_);
if (v_isSharedCheck_113_ == 0)
{
v___x_107_ = v_a_104_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v_a_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_112_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; 
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_114_ = lean_ctor_get(v_a_104_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v_a_104_, 1);
v___x_115_ = lean_io_promise_result_opt(v_a_114_);
lean_dec(v_a_114_);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = 0;
v___x_118_ = lean_task_map(v___f_92_, v___x_115_, v___x_116_, v___x_117_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1___boxed(lean_object* v___f_120_, lean_object* v_x_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Async_UDP_Socket_sendAll___lam__1(v___f_120_, v_x_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll(lean_object* v_s_129_, lean_object* v_data_130_, lean_object* v_addr_131_){
_start:
{
lean_object* v___f_133_; lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v_val_137_; lean_object* v___x_141_; 
v___f_133_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = 0;
v___x_141_ = lean_uv_udp_send(v_s_129_, v_data_130_, v_addr_131_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 1);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
v_val_137_ = v___x_147_;
goto v___jp_136_;
}
}
}
else
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_141_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_141_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 0);
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
v_val_137_ = v___x_155_;
goto v___jp_136_;
}
}
}
v___jp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v_val_137_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
v___x_140_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_134_, v___x_135_, v___x_139_, v___f_133_);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___boxed(lean_object* v_s_158_, lean_object* v_data_159_, lean_object* v_addr_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Async_UDP_Socket_sendAll(v_s_158_, v_data_159_, v_addr_160_);
lean_dec(v_addr_160_);
lean_dec(v_s_158_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_send(lean_object* v_s_163_, lean_object* v_data_164_, lean_object* v_addr_165_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v_val_174_; lean_object* v___x_178_; 
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_array_push(v___x_168_, v_data_164_);
v___f_170_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = 0;
v___x_178_ = lean_uv_udp_send(v_s_163_, v___x_169_, v_addr_165_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 1);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
v_val_174_ = v___x_184_;
goto v___jp_173_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_178_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_178_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 0);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
v_val_174_ = v___x_192_;
goto v___jp_173_;
}
}
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v_val_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_171_, v___x_172_, v___x_176_, v___f_170_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_send___boxed(lean_object* v_s_195_, lean_object* v_data_196_, lean_object* v_addr_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Async_UDP_Socket_send(v_s_195_, v_data_196_, v_addr_197_);
lean_dec(v_addr_197_);
lean_dec(v_s_195_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0(lean_object* v___x_200_, lean_object* v_x_201_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_mk_io_user_error(v___x_200_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
else
{
lean_object* v_val_204_; 
lean_dec_ref(v___x_200_);
v_val_204_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_val_204_);
return v_val_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0___boxed(lean_object* v___x_205_, lean_object* v_x_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Async_UDP_Socket_recv___lam__0(v___x_205_, v_x_206_);
lean_dec(v_x_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__1(lean_object* v___f_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
lean_dec_ref(v___f_208_);
v_a_211_ = lean_ctor_get(v_x_209_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_209_);
if (v_isSharedCheck_219_ == 0)
{
v___x_213_ = v_x_209_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v_x_209_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_218_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
return v___x_217_;
}
}
}
else
{
lean_object* v_a_220_; 
v_a_220_ = lean_ctor_get(v_x_209_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v_x_209_, 1);
if (lean_obj_tag(v_a_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v___f_208_);
v_a_221_ = lean_ctor_get(v_a_220_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v_a_220_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v_a_220_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v_a_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_a_230_ = lean_ctor_get(v_a_220_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v_a_220_, 1);
v___x_231_ = lean_io_promise_result_opt(v_a_230_);
lean_dec(v_a_230_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = 0;
v___x_234_ = lean_task_map(v___f_208_, v___x_231_, v___x_232_, v___x_233_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__1___boxed(lean_object* v___f_236_, lean_object* v_x_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_Async_UDP_Socket_recv___lam__1(v___f_236_, v_x_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv(lean_object* v_s_244_, uint64_t v_size_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v_val_251_; lean_object* v___x_255_; 
v___f_247_ = ((lean_object*)(l_Std_Async_UDP_Socket_recv___closed__1));
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = 0;
v___x_255_ = lean_uv_udp_recv(v_s_244_, v_size_245_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 1);
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
v_val_251_ = v___x_261_;
goto v___jp_250_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_264_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_255_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 0);
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
v_val_251_ = v___x_269_;
goto v___jp_250_;
}
}
}
v___jp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_val_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
v___x_254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_248_, v___x_249_, v___x_253_, v___f_247_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___boxed(lean_object* v_s_272_, lean_object* v_size_273_, lean_object* v_a_274_){
_start:
{
uint64_t v_size_boxed_275_; lean_object* v_res_276_; 
v_size_boxed_275_ = lean_unbox_uint64(v_size_273_);
lean_dec_ref(v_size_273_);
v_res_276_ = l_Std_Async_UDP_Socket_recv(v_s_272_, v_size_boxed_275_);
lean_dec(v_s_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(lean_object* v_e_277_){
_start:
{
if (lean_obj_tag(v_e_277_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_288_; 
v_a_279_ = lean_ctor_get(v_e_277_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v_e_277_);
if (v_isSharedCheck_288_ == 0)
{
v___x_281_ = v_e_277_;
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v_e_277_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = lean_io_error_to_string(v_a_279_);
v___x_284_ = lean_mk_io_user_error(v___x_283_);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 1);
lean_ctor_set(v___x_281_, 0, v___x_284_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v_e_277_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_e_277_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v_e_277_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v_e_277_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 0);
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg___boxed(lean_object* v_e_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(lean_object* v_00_u03b1_300_, lean_object* v_e_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_304_, lean_object* v_e_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(v_00_u03b1_304_, v_e_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object* v_promise_308_, lean_object* v_value_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_io_promise_resolve(v_value_309_, v_promise_308_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_312_, lean_object* v_value_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(v_promise_312_, v_value_313_);
lean_dec(v_promise_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(lean_object* v___x_319_, uint64_t v_size_320_, lean_object* v_val_321_, lean_object* v_w_322_, lean_object* v_lose_323_){
_start:
{
lean_object* v_finished_325_; lean_object* v_promise_326_; lean_object* v_a_328_; lean_object* v___f_332_; lean_object* v___x_351_; uint8_t v___y_353_; uint8_t v___x_360_; 
v_finished_325_ = lean_ctor_get(v_w_322_, 0);
lean_inc(v_finished_325_);
v_promise_326_ = lean_ctor_get(v_w_322_, 1);
lean_inc_n(v_promise_326_, 2);
lean_dec_ref(v_w_322_);
v___f_332_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_332_, 0, v_promise_326_);
v___x_351_ = lean_st_ref_take(v_finished_325_);
v___x_360_ = lean_unbox(v___x_351_);
lean_dec(v___x_351_);
if (v___x_360_ == 0)
{
uint8_t v___x_361_; 
v___x_361_ = 1;
v___y_353_ = v___x_361_;
goto v___jp_352_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = 0;
v___y_353_ = v___x_362_;
goto v___jp_352_;
}
v___jp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_a_328_);
v___x_330_ = lean_io_promise_resolve(v___x_329_, v_promise_326_);
lean_dec(v_promise_326_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
v___jp_333_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_uv_udp_recv(v___x_319_, v_size_320_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_promise_326_);
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_349_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_349_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_349_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___f_339_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__1));
v___x_340_ = lean_io_promise_result_opt(v_a_335_);
lean_dec(v_a_335_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = 0;
v___x_343_ = lean_task_map(v___f_339_, v___x_340_, v___x_341_, v___x_342_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_io_map_task(v___f_332_, v___x_343_, v___x_341_, v___x_342_);
lean_dec_ref(v___x_345_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_344_);
v___x_347_ = v___x_337_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_344_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v_a_350_; 
lean_dec_ref(v___f_332_);
v_a_350_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_334_, 1);
v_a_328_ = v_a_350_;
goto v___jp_327_;
}
}
v___jp_352_:
{
uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = 1;
v___x_355_ = lean_box(v___x_354_);
v___x_356_ = lean_st_ref_put(v_finished_325_, v___x_355_);
lean_dec(v_finished_325_);
if (v___y_353_ == 0)
{
lean_object* v___x_357_; 
lean_dec_ref(v___f_332_);
lean_dec(v_promise_326_);
lean_dec_ref(v_val_321_);
v___x_357_ = lean_apply_1(v_lose_323_, lean_box(0));
return v___x_357_;
}
else
{
lean_object* v___x_358_; 
lean_dec_ref(v_lose_323_);
v___x_358_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_val_321_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_dec_ref_known(v___x_358_, 1);
goto v___jp_333_;
}
else
{
if (lean_obj_tag(v___x_358_) == 0)
{
lean_dec_ref_known(v___x_358_, 1);
goto v___jp_333_;
}
else
{
lean_object* v_a_359_; 
lean_dec_ref(v___f_332_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v_a_328_ = v_a_359_;
goto v___jp_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object* v___x_363_, lean_object* v_size_364_, lean_object* v_val_365_, lean_object* v_w_366_, lean_object* v_lose_367_, lean_object* v___y_368_){
_start:
{
uint64_t v_size_boxed_369_; lean_object* v_res_370_; 
v_size_boxed_369_ = lean_unbox_uint64(v_size_364_);
lean_dec_ref(v_size_364_);
v_res_370_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v___x_363_, v_size_boxed_369_, v_val_365_, v_w_366_, v_lose_367_);
lean_dec(v___x_363_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0(lean_object* v_x_371_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
v_a_373_ = lean_ctor_get(v_x_371_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v_x_371_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v_x_371_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_391_; 
v_a_382_ = lean_ctor_get(v_x_371_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_391_ == 0)
{
v___x_384_ = v_x_371_;
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v_x_371_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_391_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_386_);
v___x_388_ = v___x_384_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_390_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object* v_x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Async_UDP_Socket_recvSelector___lam__0(v_x_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1(lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_a_401_ = lean_ctor_get(v_x_399_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_399_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v_x_399_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v_x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
}
else
{
lean_object* v___x_410_; 
lean_dec_ref_known(v_x_399_, 1);
v___x_410_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__1));
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object* v_x_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Async_UDP_Socket_recvSelector___lam__1(v_x_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2(lean_object* v_s_414_){
_start:
{
lean_object* v_val_417_; lean_object* v___x_419_; 
v___x_419_ = lean_uv_udp_cancel_recv(v_s_414_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 1);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
v_val_417_ = v___x_425_;
goto v___jp_416_;
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_419_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_419_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v_val_417_ = v___x_433_;
goto v___jp_416_;
}
}
}
v___jp_416_:
{
lean_object* v___x_418_; 
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v_val_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed(lean_object* v_s_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_Async_UDP_Socket_recvSelector___lam__2(v_s_436_);
lean_dec(v_s_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3(lean_object* v___x_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed(lean_object* v___x_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_Async_UDP_Socket_recvSelector___lam__3(v___x_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4(lean_object* v_s_447_, uint64_t v_size_448_, lean_object* v_waiter_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_a_453_; 
if (lean_obj_tag(v_a_450_) == 0)
{
lean_object* v___x_455_; 
lean_dec_ref(v_waiter_449_);
v___x_455_ = lean_box(0);
v_a_453_ = v___x_455_;
goto v___jp_452_;
}
else
{
lean_object* v_val_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_val_456_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_val_456_);
lean_dec_ref_known(v_a_450_, 1);
v___f_457_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0));
v___x_458_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v_s_447_, v_size_448_, v_val_456_, v_waiter_449_, v___f_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v_a_453_ = v_a_459_;
goto v___jp_452_;
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_a_460_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_458_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_458_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set_tag(v___x_462_, 0);
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
v___jp_452_:
{
lean_object* v___x_454_; 
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v_a_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed(lean_object* v_s_468_, lean_object* v_size_469_, lean_object* v_waiter_470_, lean_object* v_a_471_, lean_object* v___y_472_){
_start:
{
uint64_t v_size_boxed_473_; lean_object* v_res_474_; 
v_size_boxed_473_ = lean_unbox_uint64(v_size_469_);
lean_dec_ref(v_size_469_);
v_res_474_ = l_Std_Async_UDP_Socket_recvSelector___lam__4(v_s_468_, v_size_boxed_473_, v_waiter_470_, v_a_471_);
lean_dec(v_s_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5(lean_object* v___f_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref(v___f_479_);
v_a_482_ = lean_ctor_get(v_x_480_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_490_ == 0)
{
v___x_484_ = v_x_480_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v_x_480_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_489_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; 
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_a_491_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v_x_480_, 1);
v___x_492_ = lean_io_promise_result_opt(v_a_491_);
lean_dec(v_a_491_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = 0;
v___x_495_ = lean_io_map_task(v___f_479_, v___x_492_, v___x_493_, v___x_494_);
lean_dec_ref(v___x_495_);
v___x_496_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1));
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed(lean_object* v___f_497_, lean_object* v_x_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Async_UDP_Socket_recvSelector___lam__5(v___f_497_, v_x_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6(lean_object* v_s_501_, uint64_t v_size_502_, lean_object* v_waiter_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; uint8_t v___x_509_; lean_object* v_val_511_; lean_object* v___x_514_; 
v___x_505_ = lean_box_uint64(v_size_502_);
lean_inc(v_s_501_);
v___f_506_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_506_, 0, v_s_501_);
lean_closure_set(v___f_506_, 1, v___x_505_);
lean_closure_set(v___f_506_, 2, v_waiter_503_);
v___f_507_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_507_, 0, v___f_506_);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = 0;
v___x_514_ = lean_uv_udp_wait_readable(v_s_501_);
lean_dec(v_s_501_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 1);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
v_val_511_ = v___x_520_;
goto v___jp_510_;
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_a_523_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_514_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 0);
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_val_511_ = v___x_528_;
goto v___jp_510_;
}
}
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v_val_511_);
v___x_513_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_508_, v___x_509_, v___x_512_, v___f_507_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed(lean_object* v_s_531_, lean_object* v_size_532_, lean_object* v_waiter_533_, lean_object* v___y_534_){
_start:
{
uint64_t v_size_boxed_535_; lean_object* v_res_536_; 
v_size_boxed_535_ = lean_unbox_uint64(v_size_532_);
lean_dec_ref(v_size_532_);
v_res_536_ = l_Std_Async_UDP_Socket_recvSelector___lam__6(v_s_531_, v_size_boxed_535_, v_waiter_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8(lean_object* v___f_537_, lean_object* v___x_538_, uint8_t v___x_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_550_; 
lean_dec(v___x_538_);
lean_dec_ref(v___f_537_);
v_a_542_ = lean_ctor_get(v_x_540_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_550_ == 0)
{
v___x_544_ = v_x_540_;
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v_x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_550_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_549_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
else
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v_x_540_, 1);
if (lean_obj_tag(v_a_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
lean_dec(v___x_538_);
lean_dec_ref(v___f_537_);
v_a_552_ = lean_ctor_get(v_a_551_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_a_551_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v_a_551_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v_a_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_558_; 
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_561_ = lean_ctor_get(v_a_551_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v_a_551_, 1);
v___x_562_ = lean_io_promise_result_opt(v_a_561_);
lean_dec(v_a_561_);
v___x_563_ = lean_task_map(v___f_537_, v___x_562_, v___x_538_, v___x_539_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object* v___f_565_, lean_object* v___x_566_, lean_object* v___x_567_, lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___x_2977__boxed_570_; lean_object* v_res_571_; 
v___x_2977__boxed_570_ = lean_unbox(v___x_567_);
v_res_571_ = l_Std_Async_UDP_Socket_recvSelector___lam__8(v___f_565_, v___x_566_, v___x_2977__boxed_570_, v_x_568_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7(lean_object* v___f_577_, lean_object* v_s_578_, lean_object* v___f_579_, uint64_t v_size_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref(v___f_579_);
lean_dec_ref(v___f_577_);
v_a_583_ = lean_ctor_get(v_x_581_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_591_ == 0)
{
v___x_585_ = v_x_581_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v_x_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_640_; 
v_a_592_ = lean_ctor_get(v_x_581_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_640_ == 0)
{
v___x_594_ = v_x_581_;
v_isShared_595_ = v_isSharedCheck_640_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v_x_581_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_640_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
uint8_t v___x_596_; 
v___x_596_ = lean_unbox(v_a_592_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v_val_599_; lean_object* v___x_603_; 
lean_dec_ref(v___f_579_);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_uv_udp_cancel_recv(v_s_578_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_a_604_);
v___x_606_ = v___x_594_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_val_599_ = v___x_606_;
goto v___jp_598_;
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; 
v_a_608_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_603_, 1);
if (v_isShared_595_ == 0)
{
lean_ctor_set_tag(v___x_594_, 0);
lean_ctor_set(v___x_594_, 0, v_a_608_);
v___x_610_ = v___x_594_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
v_val_599_ = v___x_610_;
goto v___jp_598_;
}
}
v___jp_598_:
{
lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_val_599_);
v___x_601_ = lean_unbox(v_a_592_);
lean_dec(v_a_592_);
v___x_602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_597_, v___x_601_, v___x_600_, v___f_577_);
return v___x_602_;
}
}
else
{
lean_object* v___x_612_; uint8_t v___x_613_; lean_object* v___f_614_; lean_object* v_val_616_; lean_object* v___x_623_; 
lean_dec(v_a_592_);
lean_dec_ref(v___f_577_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = 0;
v___f_614_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__7___closed__0));
v___x_623_ = lean_uv_udp_recv(v_s_578_, v_size_580_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 1);
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
v_val_616_ = v___x_629_;
goto v___jp_615_;
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_632_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_623_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_623_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 0);
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
v_val_616_ = v___x_637_;
goto v___jp_615_;
}
}
}
v___jp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_val_616_);
v___x_618_ = v___x_594_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_616_);
v___x_618_ = v_reuseFailAlloc_622_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_612_, v___x_613_, v___x_619_, v___f_614_);
v___x_621_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_612_, v___x_613_, v___x_620_, v___f_579_);
return v___x_621_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object* v___f_641_, lean_object* v_s_642_, lean_object* v___f_643_, lean_object* v_size_644_, lean_object* v_x_645_, lean_object* v___y_646_){
_start:
{
uint64_t v_size_boxed_647_; lean_object* v_res_648_; 
v_size_boxed_647_ = lean_unbox_uint64(v_size_644_);
lean_dec_ref(v_size_644_);
v_res_648_ = l_Std_Async_UDP_Socket_recvSelector___lam__7(v___f_641_, v_s_642_, v___f_643_, v_size_boxed_647_, v_x_645_);
lean_dec(v_s_642_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__9(lean_object* v___f_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
lean_dec_ref(v___f_649_);
v_a_652_ = lean_ctor_get(v_x_650_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v_x_650_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v_x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_659_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_674_; 
v_a_661_ = lean_ctor_get(v_x_650_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_674_ == 0)
{
v___x_663_ = v_x_650_;
v_isShared_664_ = v_isSharedCheck_674_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v_x_650_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_674_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; uint8_t v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = 0;
v___x_667_ = l_IO_Promise_isResolved___redArg(v_a_661_);
lean_dec(v_a_661_);
v___x_668_ = lean_box(v___x_667_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_668_);
v___x_670_ = v___x_663_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_673_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
v___x_672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_665_, v___x_666_, v___x_671_, v___f_649_);
return v___x_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__9___boxed(lean_object* v___f_675_, lean_object* v_x_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_Async_UDP_Socket_recvSelector___lam__9(v___f_675_, v_x_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10(lean_object* v___f_679_, lean_object* v_s_680_){
_start:
{
lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v_val_685_; lean_object* v___x_688_; 
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = 0;
v___x_688_ = lean_uv_udp_wait_readable(v_s_680_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 1);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
v_val_685_ = v___x_694_;
goto v___jp_684_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_697_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_688_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
v_val_685_ = v___x_702_;
goto v___jp_684_;
}
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_val_685_);
v___x_687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_682_, v___x_683_, v___x_686_, v___f_679_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object* v___f_705_, lean_object* v_s_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_Async_UDP_Socket_recvSelector___lam__10(v___f_705_, v_s_706_);
lean_dec(v_s_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector(lean_object* v_s_711_, uint64_t v_size_712_){
_start:
{
lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
v___f_713_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__0));
v___f_714_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__1));
lean_inc_n(v_s_711_, 3);
v___f_715_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_715_, 0, v_s_711_);
v___x_716_ = lean_box_uint64(v_size_712_);
v___f_717_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_717_, 0, v_s_711_);
lean_closure_set(v___f_717_, 1, v___x_716_);
v___x_718_ = lean_box_uint64(v_size_712_);
v___f_719_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed), 6, 4);
lean_closure_set(v___f_719_, 0, v___f_714_);
lean_closure_set(v___f_719_, 1, v_s_711_);
lean_closure_set(v___f_719_, 2, v___f_713_);
lean_closure_set(v___f_719_, 3, v___x_718_);
v___f_720_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__9___boxed), 3, 1);
lean_closure_set(v___f_720_, 0, v___f_719_);
v___f_721_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed), 3, 2);
lean_closure_set(v___f_721_, 0, v___f_720_);
lean_closure_set(v___f_721_, 1, v_s_711_);
v___x_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_722_, 0, v___f_721_);
lean_ctor_set(v___x_722_, 1, v___f_717_);
lean_ctor_set(v___x_722_, 2, v___f_715_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___boxed(lean_object* v_s_723_, lean_object* v_size_724_){
_start:
{
uint64_t v_size_boxed_725_; lean_object* v_res_726_; 
v_size_boxed_725_ = lean_unbox_uint64(v_size_724_);
lean_dec_ref(v_size_724_);
v_res_726_ = l_Std_Async_UDP_Socket_recvSelector(v_s_723_, v_size_boxed_725_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getSockName(lean_object* v_s_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_uv_udp_getsockname(v_s_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getSockName___boxed(lean_object* v_s_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_Async_UDP_Socket_getSockName(v_s_730_);
lean_dec(v_s_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getPeerName(lean_object* v_s_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_uv_udp_getpeername(v_s_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getPeerName___boxed(lean_object* v_s_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_Async_UDP_Socket_getPeerName(v_s_736_);
lean_dec(v_s_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setBroadcast(lean_object* v_s_739_, uint8_t v_enable_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_uv_udp_set_broadcast(v_s_739_, v_enable_740_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setBroadcast___boxed(lean_object* v_s_743_, lean_object* v_enable_744_, lean_object* v_a_745_){
_start:
{
uint8_t v_enable_boxed_746_; lean_object* v_res_747_; 
v_enable_boxed_746_ = lean_unbox(v_enable_744_);
v_res_747_ = l_Std_Async_UDP_Socket_setBroadcast(v_s_743_, v_enable_boxed_746_);
lean_dec(v_s_743_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastLoop(lean_object* v_s_748_, uint8_t v_enable_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_uv_udp_set_multicast_loop(v_s_748_, v_enable_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastLoop___boxed(lean_object* v_s_752_, lean_object* v_enable_753_, lean_object* v_a_754_){
_start:
{
uint8_t v_enable_boxed_755_; lean_object* v_res_756_; 
v_enable_boxed_755_ = lean_unbox(v_enable_753_);
v_res_756_ = l_Std_Async_UDP_Socket_setMulticastLoop(v_s_752_, v_enable_boxed_755_);
lean_dec(v_s_752_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastTTL(lean_object* v_s_757_, uint32_t v_ttl_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_uv_udp_set_multicast_ttl(v_s_757_, v_ttl_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastTTL___boxed(lean_object* v_s_761_, lean_object* v_ttl_762_, lean_object* v_a_763_){
_start:
{
uint32_t v_ttl_boxed_764_; lean_object* v_res_765_; 
v_ttl_boxed_764_ = lean_unbox_uint32(v_ttl_762_);
lean_dec(v_ttl_762_);
v_res_765_ = l_Std_Async_UDP_Socket_setMulticastTTL(v_s_761_, v_ttl_boxed_764_);
lean_dec(v_s_761_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMembership(lean_object* v_s_766_, lean_object* v_multicastAddr_767_, lean_object* v_interfaceAddr_768_, uint8_t v_membership_769_){
_start:
{
if (v_membership_769_ == 0)
{
uint8_t v___x_771_; lean_object* v___x_772_; 
v___x_771_ = 0;
v___x_772_ = lean_uv_udp_set_membership(v_s_766_, v_multicastAddr_767_, v_interfaceAddr_768_, v___x_771_);
return v___x_772_;
}
else
{
uint8_t v___x_773_; lean_object* v___x_774_; 
v___x_773_ = 1;
v___x_774_ = lean_uv_udp_set_membership(v_s_766_, v_multicastAddr_767_, v_interfaceAddr_768_, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMembership___boxed(lean_object* v_s_775_, lean_object* v_multicastAddr_776_, lean_object* v_interfaceAddr_777_, lean_object* v_membership_778_, lean_object* v_a_779_){
_start:
{
uint8_t v_membership_boxed_780_; lean_object* v_res_781_; 
v_membership_boxed_780_ = lean_unbox(v_membership_778_);
v_res_781_ = l_Std_Async_UDP_Socket_setMembership(v_s_775_, v_multicastAddr_776_, v_interfaceAddr_777_, v_membership_boxed_780_);
lean_dec(v_interfaceAddr_777_);
lean_dec_ref(v_multicastAddr_776_);
lean_dec(v_s_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastInterface(lean_object* v_s_782_, lean_object* v_interfaceAddr_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_uv_udp_set_multicast_interface(v_s_782_, v_interfaceAddr_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastInterface___boxed(lean_object* v_s_786_, lean_object* v_interfaceAddr_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Async_UDP_Socket_setMulticastInterface(v_s_786_, v_interfaceAddr_787_);
lean_dec_ref(v_interfaceAddr_787_);
lean_dec(v_s_786_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setTTL(lean_object* v_s_790_, uint32_t v_ttl_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_uv_udp_set_ttl(v_s_790_, v_ttl_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setTTL___boxed(lean_object* v_s_794_, lean_object* v_ttl_795_, lean_object* v_a_796_){
_start:
{
uint32_t v_ttl_boxed_797_; lean_object* v_res_798_; 
v_ttl_boxed_797_ = lean_unbox_uint32(v_ttl_795_);
lean_dec(v_ttl_795_);
v_res_798_ = l_Std_Async_UDP_Socket_setTTL(v_s_794_, v_ttl_boxed_797_);
lean_dec(v_s_794_);
return v_res_798_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_UDP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_UDP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_UDP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_UDP(uint8_t builtin);
lean_object* initialize_Std_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_UDP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_UDP(builtin);
}
#ifdef __cplusplus
}
#endif

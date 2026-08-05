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
lean_object* lean_uv_udp_wait_readable(lean_object*);
lean_object* lean_uv_udp_send(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_getsockname(lean_object*);
lean_object* lean_uv_udp_set_broadcast(lean_object*, uint8_t);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_uv_udp_new();
lean_object* lean_uv_udp_connect(lean_object*, lean_object*);
lean_object* lean_uv_udp_cancel_recv(lean_object*);
lean_object* lean_uv_udp_set_multicast_interface(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_loop(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1(lean_object*, lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_UDP_Socket_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_UDP_Socket_recvSelector___closed__0 = (const lean_object*)&l_Std_Async_UDP_Socket_recvSelector___closed__0_value;
static const lean_closure_object l_Std_Async_UDP_Socket_recvSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___f_133_; lean_object* v_val_135_; lean_object* v___x_141_; 
v___f_133_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
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
v_val_135_ = v___x_147_;
goto v___jp_134_;
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
v_val_135_ = v___x_155_;
goto v___jp_134_;
}
}
}
v___jp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; 
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v_val_135_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = 0;
v___x_140_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_138_, v___x_139_, v___x_137_, v___f_133_);
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
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v_val_172_; lean_object* v___x_178_; 
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_array_push(v___x_168_, v_data_164_);
v___f_170_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
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
v_val_172_ = v___x_184_;
goto v___jp_171_;
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
v_val_172_ = v___x_192_;
goto v___jp_171_;
}
}
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; 
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v_val_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = 0;
v___x_177_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_175_, v___x_176_, v___x_174_, v___f_170_);
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
lean_object* v___f_247_; lean_object* v_val_249_; lean_object* v___x_255_; 
v___f_247_ = ((lean_object*)(l_Std_Async_UDP_Socket_recv___closed__1));
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
v_val_249_ = v___x_261_;
goto v___jp_248_;
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
v_val_249_ = v___x_269_;
goto v___jp_248_;
}
}
}
v___jp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; 
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_val_249_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = 0;
v___x_254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_252_, v___x_253_, v___x_251_, v___f_247_);
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; 
v_a_309_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v_x_308_, 1);
v___x_310_ = lean_task_pure(v_a_309_);
return v___x_310_;
}
else
{
lean_object* v_a_311_; 
v_a_311_ = lean_ctor_get(v_x_308_, 0);
lean_inc_ref(v_a_311_);
lean_dec_ref_known(v_x_308_, 1);
return v_a_311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2(lean_object* v___f_312_, lean_object* v___x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
lean_dec(v___x_313_);
lean_dec_ref(v___f_312_);
v_a_316_ = lean_ctor_get(v_x_314_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_314_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v_x_314_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v_x_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_323_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; 
v_a_325_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v_x_314_, 1);
if (lean_obj_tag(v_a_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
lean_dec(v___x_313_);
lean_dec_ref(v___f_312_);
v_a_326_ = lean_ctor_get(v_a_325_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_a_325_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v_a_325_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v_a_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_333_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_335_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v_a_325_, 1);
v___x_336_ = lean_io_promise_result_opt(v_a_335_);
lean_dec(v_a_335_);
v___x_337_ = 0;
v___x_338_ = lean_task_map(v___f_312_, v___x_336_, v___x_313_, v___x_337_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed(lean_object* v___f_340_, lean_object* v___x_341_, lean_object* v_x_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2(v___f_340_, v___x_341_, v_x_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1(lean_object* v___x_345_, lean_object* v_s_346_, uint64_t v_size_347_){
_start:
{
lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v_val_352_; lean_object* v___x_357_; 
v___f_349_ = ((lean_object*)(l_Std_Async_UDP_Socket_recv___closed__0));
lean_inc(v___x_345_);
v___f_350_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed), 4, 2);
lean_closure_set(v___f_350_, 0, v___f_349_);
lean_closure_set(v___f_350_, 1, v___x_345_);
v___x_357_ = lean_uv_udp_recv(v_s_346_, v_size_347_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
v_val_352_ = v___x_363_;
goto v___jp_351_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_a_366_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_357_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_357_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 0);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
v_val_352_ = v___x_371_;
goto v___jp_351_;
}
}
}
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_val_352_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
v___x_355_ = 0;
v___x_356_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_345_, v___x_355_, v___x_354_, v___f_350_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed(lean_object* v___x_374_, lean_object* v_s_375_, lean_object* v_size_376_, lean_object* v___y_377_){
_start:
{
uint64_t v_size_boxed_378_; lean_object* v_res_379_; 
v_size_boxed_378_ = lean_unbox_uint64(v_size_376_);
lean_dec_ref(v_size_376_);
v_res_379_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1(v___x_374_, v_s_375_, v_size_boxed_378_);
lean_dec(v_s_375_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(lean_object* v_s_381_, uint64_t v_size_382_, lean_object* v_val_383_, lean_object* v_w_384_, lean_object* v_lose_385_){
_start:
{
lean_object* v_finished_387_; lean_object* v_promise_388_; lean_object* v_a_390_; lean_object* v___x_394_; lean_object* v___f_395_; uint8_t v___y_397_; uint8_t v___y_408_; uint8_t v___x_415_; 
v_finished_387_ = lean_ctor_get(v_w_384_, 0);
v_promise_388_ = lean_ctor_get(v_w_384_, 1);
v___x_394_ = lean_st_ref_take(v_finished_387_);
v___f_395_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0));
v___x_415_ = lean_unbox(v___x_394_);
lean_dec(v___x_394_);
if (v___x_415_ == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 1;
v___y_408_ = v___x_416_;
goto v___jp_407_;
}
else
{
uint8_t v___x_417_; 
v___x_417_ = 0;
v___y_408_ = v___x_417_;
goto v___jp_407_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_a_390_);
v___x_392_ = lean_io_promise_resolve(v___x_391_, v_promise_388_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_box_uint64(v_size_382_);
v___f_400_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed), 4, 3);
lean_closure_set(v___f_400_, 0, v___x_398_);
lean_closure_set(v___f_400_, 1, v_s_381_);
lean_closure_set(v___f_400_, 2, v___x_399_);
v___x_401_ = lean_io_as_task(v___f_400_, v___x_398_);
v___x_402_ = lean_task_bind(v___x_401_, v___f_395_, v___x_398_, v___y_397_);
v___x_403_ = lean_task_get_own(v___x_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v_a_390_ = v_a_404_;
goto v___jp_389_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_io_promise_resolve(v___x_403_, v_promise_388_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
v___jp_407_:
{
uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = 1;
v___x_410_ = lean_box(v___x_409_);
v___x_411_ = lean_st_ref_set(v_finished_387_, v___x_410_);
if (v___y_408_ == 0)
{
lean_object* v___x_412_; 
lean_dec_ref(v_val_383_);
lean_dec(v_s_381_);
v___x_412_ = lean_apply_1(v_lose_385_, lean_box(0));
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
lean_dec_ref(v_lose_385_);
v___x_413_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_val_383_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_dec_ref_known(v___x_413_, 1);
v___y_397_ = v___y_408_;
goto v___jp_396_;
}
else
{
if (lean_obj_tag(v___x_413_) == 0)
{
lean_dec_ref_known(v___x_413_, 1);
v___y_397_ = v___y_408_;
goto v___jp_396_;
}
else
{
lean_object* v_a_414_; 
lean_dec(v_s_381_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v_a_390_ = v_a_414_;
goto v___jp_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object* v_s_418_, lean_object* v_size_419_, lean_object* v_val_420_, lean_object* v_w_421_, lean_object* v_lose_422_, lean_object* v___y_423_){
_start:
{
uint64_t v_size_boxed_424_; lean_object* v_res_425_; 
v_size_boxed_424_ = lean_unbox_uint64(v_size_419_);
lean_dec_ref(v_size_419_);
v_res_425_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v_s_418_, v_size_boxed_424_, v_val_420_, v_w_421_, v_lose_422_);
lean_dec_ref(v_w_421_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1(lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_a_428_ = lean_ctor_get(v_x_426_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_426_);
if (v_isSharedCheck_436_ == 0)
{
v___x_430_ = v_x_426_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v_x_426_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_446_; 
v_a_437_ = lean_ctor_get(v_x_426_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_426_);
if (v_isSharedCheck_446_ == 0)
{
v___x_439_ = v_x_426_;
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v_x_426_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_446_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_a_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object* v_x_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_Async_UDP_Socket_recvSelector___lam__1(v_x_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0(lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_a_456_ = lean_ctor_get(v_x_454_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_454_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v_x_454_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v_x_454_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_463_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
}
else
{
lean_object* v___x_465_; 
lean_dec_ref_known(v_x_454_, 1);
v___x_465_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1));
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object* v_x_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Async_UDP_Socket_recvSelector___lam__0(v_x_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2(lean_object* v_s_469_){
_start:
{
lean_object* v_val_472_; lean_object* v___x_474_; 
v___x_474_ = lean_uv_udp_cancel_recv(v_s_469_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set_tag(v___x_477_, 1);
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
v_val_472_ = v___x_480_;
goto v___jp_471_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_474_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_474_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 0);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
v_val_472_ = v___x_488_;
goto v___jp_471_;
}
}
}
v___jp_471_:
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v_val_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed(lean_object* v_s_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Async_UDP_Socket_recvSelector___lam__2(v_s_491_);
lean_dec(v_s_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3(lean_object* v___x_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed(lean_object* v___x_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Async_UDP_Socket_recvSelector___lam__3(v___x_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4(lean_object* v_s_502_, uint64_t v_size_503_, lean_object* v_waiter_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_a_508_; 
if (lean_obj_tag(v_a_505_) == 0)
{
lean_object* v___x_510_; 
lean_dec(v_s_502_);
v___x_510_ = lean_box(0);
v_a_508_ = v___x_510_;
goto v___jp_507_;
}
else
{
lean_object* v_val_511_; lean_object* v___f_512_; lean_object* v___x_513_; 
v_val_511_ = lean_ctor_get(v_a_505_, 0);
lean_inc(v_val_511_);
lean_dec_ref_known(v_a_505_, 1);
v___f_512_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0));
v___x_513_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v_s_502_, v_size_503_, v_val_511_, v_waiter_504_, v___f_512_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v_a_508_ = v_a_514_;
goto v___jp_507_;
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_513_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_513_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 0);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
v___jp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_a_508_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed(lean_object* v_s_523_, lean_object* v_size_524_, lean_object* v_waiter_525_, lean_object* v_a_526_, lean_object* v___y_527_){
_start:
{
uint64_t v_size_boxed_528_; lean_object* v_res_529_; 
v_size_boxed_528_ = lean_unbox_uint64(v_size_524_);
lean_dec_ref(v_size_524_);
v_res_529_ = l_Std_Async_UDP_Socket_recvSelector___lam__4(v_s_523_, v_size_boxed_528_, v_waiter_525_, v_a_526_);
lean_dec_ref(v_waiter_525_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5(lean_object* v___f_534_, lean_object* v_x_535_){
_start:
{
if (lean_obj_tag(v_x_535_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v___f_534_);
v_a_537_ = lean_ctor_get(v_x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_539_ = v_x_535_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v_x_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_544_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; 
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_546_ = lean_ctor_get(v_x_535_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v_x_535_, 1);
v___x_547_ = lean_io_promise_result_opt(v_a_546_);
lean_dec(v_a_546_);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = 0;
v___x_550_ = lean_io_map_task(v___f_534_, v___x_547_, v___x_548_, v___x_549_);
lean_dec_ref(v___x_550_);
v___x_551_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1));
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed(lean_object* v___f_552_, lean_object* v_x_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_Async_UDP_Socket_recvSelector___lam__5(v___f_552_, v_x_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6(lean_object* v_s_556_, uint64_t v_size_557_, lean_object* v_waiter_558_){
_start:
{
lean_object* v___x_560_; lean_object* v___f_561_; lean_object* v___f_562_; lean_object* v_val_564_; lean_object* v___x_569_; 
v___x_560_ = lean_box_uint64(v_size_557_);
lean_inc(v_s_556_);
v___f_561_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_561_, 0, v_s_556_);
lean_closure_set(v___f_561_, 1, v___x_560_);
lean_closure_set(v___f_561_, 2, v_waiter_558_);
v___f_562_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_562_, 0, v___f_561_);
v___x_569_ = lean_uv_udp_wait_readable(v_s_556_);
lean_dec(v_s_556_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 1);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v_val_564_ = v___x_575_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_569_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 0);
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v_val_564_ = v___x_583_;
goto v___jp_563_;
}
}
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; 
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v_val_564_);
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = 0;
v___x_568_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_566_, v___x_567_, v___x_565_, v___f_562_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed(lean_object* v_s_586_, lean_object* v_size_587_, lean_object* v_waiter_588_, lean_object* v___y_589_){
_start:
{
uint64_t v_size_boxed_590_; lean_object* v_res_591_; 
v_size_boxed_590_ = lean_unbox_uint64(v_size_587_);
lean_dec_ref(v_size_587_);
v_res_591_ = l_Std_Async_UDP_Socket_recvSelector___lam__6(v_s_586_, v_size_boxed_590_, v_waiter_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10(lean_object* v___f_592_, lean_object* v_s_593_, uint64_t v_size_594_, lean_object* v___f_595_, lean_object* v___f_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v___f_596_);
lean_dec_ref(v___f_595_);
lean_dec(v_s_593_);
lean_dec_ref(v___f_592_);
v_a_599_ = lean_ctor_get(v_x_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_x_597_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_638_; 
v_a_608_ = lean_ctor_get(v_x_597_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_638_ == 0)
{
v___x_610_ = v_x_597_;
v_isShared_611_ = v_isSharedCheck_638_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v_x_597_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_638_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_val_613_; uint8_t v___x_618_; 
v___x_618_ = lean_unbox(v_a_608_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_dec_ref(v___f_596_);
lean_dec_ref(v___f_595_);
v___x_619_ = lean_uv_udp_cancel_recv(v_s_593_);
lean_dec(v_s_593_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref_known(v___x_619_, 1);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v_a_620_);
v___x_622_ = v___x_610_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
v_val_613_ = v___x_622_;
goto v___jp_612_;
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; 
v_a_624_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_619_, 1);
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 0);
lean_ctor_set(v___x_610_, 0, v_a_624_);
v___x_626_ = v___x_610_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
v_val_613_ = v___x_626_;
goto v___jp_612_;
}
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
lean_del_object(v___x_610_);
lean_dec_ref(v___f_592_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_box_uint64(v_size_594_);
v___f_630_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed), 4, 3);
lean_closure_set(v___f_630_, 0, v___x_628_);
lean_closure_set(v___f_630_, 1, v_s_593_);
lean_closure_set(v___f_630_, 2, v___x_629_);
v___x_631_ = lean_io_as_task(v___f_630_, v___x_628_);
v___x_632_ = lean_unbox(v_a_608_);
lean_dec(v_a_608_);
v___x_633_ = lean_task_bind(v___x_631_, v___f_595_, v___x_628_, v___x_632_);
v___x_634_ = lean_task_get_own(v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = 0;
v___x_637_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_628_, v___x_636_, v___x_635_, v___f_596_);
return v___x_637_;
}
v___jp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; 
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v_val_613_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_unbox(v_a_608_);
lean_dec(v_a_608_);
v___x_617_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_615_, v___x_616_, v___x_614_, v___f_592_);
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object* v___f_639_, lean_object* v_s_640_, lean_object* v_size_641_, lean_object* v___f_642_, lean_object* v___f_643_, lean_object* v_x_644_, lean_object* v___y_645_){
_start:
{
uint64_t v_size_boxed_646_; lean_object* v_res_647_; 
v_size_boxed_646_ = lean_unbox_uint64(v_size_641_);
lean_dec_ref(v_size_641_);
v_res_647_ = l_Std_Async_UDP_Socket_recvSelector___lam__10(v___f_639_, v_s_640_, v_size_boxed_646_, v___f_642_, v___f_643_, v_x_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7(lean_object* v___f_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v___f_648_);
v_a_651_ = lean_ctor_get(v_x_649_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_659_ == 0)
{
v___x_653_ = v_x_649_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v_x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_658_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_673_; 
v_a_660_ = lean_ctor_get(v_x_649_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_673_ == 0)
{
v___x_662_ = v_x_649_;
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v_x_649_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_664_ = l_IO_Promise_isResolved___redArg(v_a_660_);
lean_dec(v_a_660_);
v___x_665_ = lean_box(v___x_664_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_665_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_672_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = 0;
v___x_671_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_669_, v___x_670_, v___x_668_, v___f_648_);
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object* v___f_674_, lean_object* v_x_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_Async_UDP_Socket_recvSelector___lam__7(v___f_674_, v_x_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8(lean_object* v___f_678_, lean_object* v_s_679_){
_start:
{
lean_object* v_val_682_; lean_object* v___x_687_; 
v___x_687_ = lean_uv_udp_wait_readable(v_s_679_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 1);
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v_val_682_ = v___x_693_;
goto v___jp_681_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_a_696_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_687_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 0);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v_val_682_ = v___x_701_;
goto v___jp_681_;
}
}
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_val_682_);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = 0;
v___x_686_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_684_, v___x_685_, v___x_683_, v___f_678_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object* v___f_704_, lean_object* v_s_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_Async_UDP_Socket_recvSelector___lam__8(v___f_704_, v_s_705_);
lean_dec(v_s_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector(lean_object* v_s_710_, uint64_t v_size_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
v___f_712_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0));
v___f_713_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__0));
v___f_714_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__1));
lean_inc_n(v_s_710_, 3);
v___f_715_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_715_, 0, v_s_710_);
v___x_716_ = lean_box_uint64(v_size_711_);
v___f_717_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_717_, 0, v_s_710_);
lean_closure_set(v___f_717_, 1, v___x_716_);
v___x_718_ = lean_box_uint64(v_size_711_);
v___f_719_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed), 7, 5);
lean_closure_set(v___f_719_, 0, v___f_714_);
lean_closure_set(v___f_719_, 1, v_s_710_);
lean_closure_set(v___f_719_, 2, v___x_718_);
lean_closure_set(v___f_719_, 3, v___f_712_);
lean_closure_set(v___f_719_, 4, v___f_713_);
v___f_720_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_720_, 0, v___f_719_);
v___f_721_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_721_, 0, v___f_720_);
lean_closure_set(v___f_721_, 1, v_s_710_);
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

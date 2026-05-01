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
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Async_UDP_Membership_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Std_Async_UDP_Membership_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Async_UDP_Membership_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Std_Async_UDP_Membership_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(lean_object* v_leaveGroup_27_){
_start:
{
lean_inc(v_leaveGroup_27_);
return v_leaveGroup_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg___boxed(lean_object* v_leaveGroup_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(v_leaveGroup_28_);
lean_dec(v_leaveGroup_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_leaveGroup_33_){
_start:
{
lean_inc(v_leaveGroup_33_);
return v_leaveGroup_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_leaveGroup_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Std_Async_UDP_Membership_leaveGroup_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_leaveGroup_37_);
lean_dec(v_leaveGroup_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg(lean_object* v_enterGroup_40_){
_start:
{
lean_inc(v_enterGroup_40_);
return v_enterGroup_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg___boxed(lean_object* v_enterGroup_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Async_UDP_Membership_enterGroup_elim___redArg(v_enterGroup_41_);
lean_dec(v_enterGroup_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_enterGroup_46_){
_start:
{
lean_inc(v_enterGroup_46_);
return v_enterGroup_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_enterGroup_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Std_Async_UDP_Membership_enterGroup_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_enterGroup_50_);
lean_dec(v_enterGroup_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_mk(){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_uv_udp_new();
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_62_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_a_55_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_a_63_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_54_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_54_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_mk___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Async_UDP_Socket_mk();
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_bind(lean_object* v_s_73_, lean_object* v_addr_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_uv_udp_bind(v_s_73_, v_addr_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_bind___boxed(lean_object* v_s_77_, lean_object* v_addr_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_Async_UDP_Socket_bind(v_s_77_, v_addr_78_);
lean_dec_ref(v_addr_78_);
lean_dec(v_s_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_connect(lean_object* v_s_81_, lean_object* v_addr_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_uv_udp_connect(v_s_81_, v_addr_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_connect___boxed(lean_object* v_s_85_, lean_object* v_addr_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_Async_UDP_Socket_connect(v_s_85_, v_addr_86_);
lean_dec_ref(v_addr_86_);
lean_dec(v_s_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0(lean_object* v___x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_mk_io_user_error(v___x_89_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_val_93_; 
lean_dec_ref(v___x_89_);
v_val_93_ = lean_ctor_get(v_x_90_, 0);
lean_inc(v_val_93_);
return v_val_93_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0___boxed(lean_object* v___x_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Async_UDP_Socket_sendAll___lam__0(v___x_94_, v_x_95_);
lean_dec(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1(lean_object* v___f_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v___f_97_);
v_a_100_ = lean_ctor_get(v_x_98_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_98_);
if (v_isSharedCheck_108_ == 0)
{
v___x_102_ = v_x_98_;
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v_x_98_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_108_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_107_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; 
v_a_109_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v_x_98_);
if (lean_obj_tag(v_a_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_118_; 
lean_dec_ref(v___f_97_);
v_a_110_ = lean_ctor_get(v_a_109_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_118_ == 0)
{
v___x_112_ = v_a_109_;
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v_a_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_117_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_a_119_ = lean_ctor_get(v_a_109_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v_a_109_);
v___x_120_ = lean_io_promise_result_opt(v_a_119_);
lean_dec(v_a_119_);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = 0;
v___x_123_ = lean_task_map(v___f_97_, v___x_120_, v___x_121_, v___x_122_);
v___x_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1___boxed(lean_object* v___f_125_, lean_object* v_x_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Async_UDP_Socket_sendAll___lam__1(v___f_125_, v_x_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll(lean_object* v_s_134_, lean_object* v_data_135_, lean_object* v_addr_136_){
_start:
{
lean_object* v___f_138_; lean_object* v_val_140_; lean_object* v___x_146_; 
v___f_138_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
v___x_146_ = lean_uv_udp_send(v_s_134_, v_data_135_, v_addr_136_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 1);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v_val_140_ = v___x_152_;
goto v___jp_139_;
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_a_155_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_146_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_146_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 0);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
v_val_140_ = v___x_160_;
goto v___jp_139_;
}
}
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; 
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_val_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = 0;
v___x_145_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_143_, v___x_144_, v___x_142_, v___f_138_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___boxed(lean_object* v_s_163_, lean_object* v_data_164_, lean_object* v_addr_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Async_UDP_Socket_sendAll(v_s_163_, v_data_164_, v_addr_165_);
lean_dec(v_addr_165_);
lean_dec(v_s_163_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_send(lean_object* v_s_168_, lean_object* v_data_169_, lean_object* v_addr_170_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v_val_177_; lean_object* v___x_183_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_174_ = lean_array_push(v___x_173_, v_data_169_);
v___f_175_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
v___x_183_ = lean_uv_udp_send(v_s_168_, v___x_174_, v_addr_170_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v_val_177_ = v___x_189_;
goto v___jp_176_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_183_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_183_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 0);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
v_val_177_ = v___x_197_;
goto v___jp_176_;
}
}
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; 
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v_val_177_);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = 0;
v___x_182_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_180_, v___x_181_, v___x_179_, v___f_175_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_send___boxed(lean_object* v_s_200_, lean_object* v_data_201_, lean_object* v_addr_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_Async_UDP_Socket_send(v_s_200_, v_data_201_, v_addr_202_);
lean_dec(v_addr_202_);
lean_dec(v_s_200_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0(lean_object* v___x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_mk_io_user_error(v___x_205_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v_val_209_; 
lean_dec_ref(v___x_205_);
v_val_209_ = lean_ctor_get(v_x_206_, 0);
lean_inc(v_val_209_);
return v_val_209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0___boxed(lean_object* v___x_210_, lean_object* v_x_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Async_UDP_Socket_recv___lam__0(v___x_210_, v_x_211_);
lean_dec(v_x_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__1(lean_object* v___f_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v___f_213_);
v_a_216_ = lean_ctor_get(v_x_214_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v_x_214_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v_x_214_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_223_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
}
else
{
lean_object* v_a_225_; 
v_a_225_ = lean_ctor_get(v_x_214_, 0);
lean_inc(v_a_225_);
lean_dec_ref(v_x_214_);
if (lean_obj_tag(v_a_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v___f_213_);
v_a_226_ = lean_ctor_get(v_a_225_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_a_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v_a_225_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v_a_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_233_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_a_235_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v_a_225_);
v___x_236_ = lean_io_promise_result_opt(v_a_235_);
lean_dec(v_a_235_);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = 0;
v___x_239_ = lean_task_map(v___f_213_, v___x_236_, v___x_237_, v___x_238_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__1___boxed(lean_object* v___f_241_, lean_object* v_x_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Async_UDP_Socket_recv___lam__1(v___f_241_, v_x_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv(lean_object* v_s_249_, uint64_t v_size_250_){
_start:
{
lean_object* v___f_252_; lean_object* v_val_254_; lean_object* v___x_260_; 
v___f_252_ = ((lean_object*)(l_Std_Async_UDP_Socket_recv___closed__1));
v___x_260_ = lean_uv_udp_recv(v_s_249_, v_size_250_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 1);
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
v_val_254_ = v___x_266_;
goto v___jp_253_;
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_260_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_260_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 0);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
v_val_254_ = v___x_274_;
goto v___jp_253_;
}
}
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v_val_254_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = 0;
v___x_259_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_257_, v___x_258_, v___x_256_, v___f_252_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___boxed(lean_object* v_s_277_, lean_object* v_size_278_, lean_object* v_a_279_){
_start:
{
uint64_t v_size_boxed_280_; lean_object* v_res_281_; 
v_size_boxed_280_ = lean_unbox_uint64(v_size_278_);
lean_dec_ref(v_size_278_);
v_res_281_ = l_Std_Async_UDP_Socket_recv(v_s_277_, v_size_boxed_280_);
lean_dec(v_s_277_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(lean_object* v_e_282_){
_start:
{
if (lean_obj_tag(v_e_282_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_293_; 
v_a_284_ = lean_ctor_get(v_e_282_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_e_282_);
if (v_isSharedCheck_293_ == 0)
{
v___x_286_ = v_e_282_;
v_isShared_287_ = v_isSharedCheck_293_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v_e_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_293_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_288_ = lean_io_error_to_string(v_a_284_);
v___x_289_ = lean_mk_io_user_error(v___x_288_);
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 1);
lean_ctor_set(v___x_286_, 0, v___x_289_);
v___x_291_ = v___x_286_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_a_294_ = lean_ctor_get(v_e_282_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_e_282_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v_e_282_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v_e_282_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 0);
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg___boxed(lean_object* v_e_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(lean_object* v_00_u03b1_305_, lean_object* v_e_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_309_, lean_object* v_e_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(v_00_u03b1_309_, v_e_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_315_; 
v_a_314_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref(v_x_313_);
v___x_315_ = lean_task_pure(v_a_314_);
return v___x_315_;
}
else
{
lean_object* v_a_316_; 
v_a_316_ = lean_ctor_get(v_x_313_, 0);
lean_inc_ref(v_a_316_);
lean_dec_ref(v_x_313_);
return v_a_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2(lean_object* v___f_317_, lean_object* v___x_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
lean_dec(v___x_318_);
lean_dec_ref(v___f_317_);
v_a_321_ = lean_ctor_get(v_x_319_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_319_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v_x_319_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v_x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
else
{
lean_object* v_a_330_; 
v_a_330_ = lean_ctor_get(v_x_319_, 0);
lean_inc(v_a_330_);
lean_dec_ref(v_x_319_);
if (lean_obj_tag(v_a_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_339_; 
lean_dec(v___x_318_);
lean_dec_ref(v___f_317_);
v_a_331_ = lean_ctor_get(v_a_330_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_339_ == 0)
{
v___x_333_ = v_a_330_;
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v_a_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_338_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_a_340_ = lean_ctor_get(v_a_330_, 0);
lean_inc(v_a_340_);
lean_dec_ref(v_a_330_);
v___x_341_ = lean_io_promise_result_opt(v_a_340_);
lean_dec(v_a_340_);
v___x_342_ = 0;
v___x_343_ = lean_task_map(v___f_317_, v___x_341_, v___x_318_, v___x_342_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed(lean_object* v___f_345_, lean_object* v___x_346_, lean_object* v_x_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2(v___f_345_, v___x_346_, v_x_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1(lean_object* v___x_350_, lean_object* v_s_351_, uint64_t v_size_352_){
_start:
{
lean_object* v___f_354_; lean_object* v___f_355_; lean_object* v_val_357_; lean_object* v___x_362_; 
v___f_354_ = ((lean_object*)(l_Std_Async_UDP_Socket_recv___closed__0));
lean_inc(v___x_350_);
v___f_355_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed), 4, 2);
lean_closure_set(v___f_355_, 0, v___f_354_);
lean_closure_set(v___f_355_, 1, v___x_350_);
v___x_362_ = lean_uv_udp_recv(v_s_351_, v_size_352_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_362_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 1);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
v_val_357_ = v___x_368_;
goto v___jp_356_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_a_371_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_362_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_362_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 0);
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v_val_357_ = v___x_376_;
goto v___jp_356_;
}
}
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v_val_357_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
v___x_360_ = 0;
v___x_361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_350_, v___x_360_, v___x_359_, v___f_355_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed(lean_object* v___x_379_, lean_object* v_s_380_, lean_object* v_size_381_, lean_object* v___y_382_){
_start:
{
uint64_t v_size_boxed_383_; lean_object* v_res_384_; 
v_size_boxed_383_ = lean_unbox_uint64(v_size_381_);
lean_dec_ref(v_size_381_);
v_res_384_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1(v___x_379_, v_s_380_, v_size_boxed_383_);
lean_dec(v_s_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(lean_object* v_s_386_, uint64_t v_size_387_, lean_object* v_val_388_, lean_object* v_w_389_, lean_object* v_lose_390_){
_start:
{
lean_object* v_finished_392_; lean_object* v_promise_393_; lean_object* v_a_395_; lean_object* v___x_399_; lean_object* v___f_400_; uint8_t v___y_402_; uint8_t v___y_413_; uint8_t v___x_420_; 
v_finished_392_ = lean_ctor_get(v_w_389_, 0);
v_promise_393_ = lean_ctor_get(v_w_389_, 1);
v___x_399_ = lean_st_ref_take(v_finished_392_);
v___f_400_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0));
v___x_420_ = lean_unbox(v___x_399_);
lean_dec(v___x_399_);
if (v___x_420_ == 0)
{
uint8_t v___x_421_; 
v___x_421_ = 1;
v___y_413_ = v___x_421_;
goto v___jp_412_;
}
else
{
uint8_t v___x_422_; 
v___x_422_ = 0;
v___y_413_ = v___x_422_;
goto v___jp_412_;
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_a_395_);
v___x_397_ = lean_io_promise_resolve(v___x_396_, v_promise_393_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_box_uint64(v_size_387_);
v___f_405_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed), 4, 3);
lean_closure_set(v___f_405_, 0, v___x_403_);
lean_closure_set(v___f_405_, 1, v_s_386_);
lean_closure_set(v___f_405_, 2, v___x_404_);
v___x_406_ = lean_io_as_task(v___f_405_, v___x_403_);
v___x_407_ = lean_task_bind(v___x_406_, v___f_400_, v___x_403_, v___y_402_);
v___x_408_ = lean_task_get_own(v___x_407_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref(v___x_408_);
v_a_395_ = v_a_409_;
goto v___jp_394_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_io_promise_resolve(v___x_408_, v_promise_393_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
v___jp_412_:
{
uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = 1;
v___x_415_ = lean_box(v___x_414_);
v___x_416_ = lean_st_ref_set(v_finished_392_, v___x_415_);
if (v___y_413_ == 0)
{
lean_object* v___x_417_; 
lean_dec_ref(v_val_388_);
lean_dec(v_s_386_);
v___x_417_ = lean_apply_1(v_lose_390_, lean_box(0));
return v___x_417_;
}
else
{
lean_object* v___x_418_; 
lean_dec_ref(v_lose_390_);
v___x_418_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_val_388_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_dec_ref(v___x_418_);
v___y_402_ = v___y_413_;
goto v___jp_401_;
}
else
{
if (lean_obj_tag(v___x_418_) == 0)
{
lean_dec_ref(v___x_418_);
v___y_402_ = v___y_413_;
goto v___jp_401_;
}
else
{
lean_object* v_a_419_; 
lean_dec(v_s_386_);
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
v_a_395_ = v_a_419_;
goto v___jp_394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object* v_s_423_, lean_object* v_size_424_, lean_object* v_val_425_, lean_object* v_w_426_, lean_object* v_lose_427_, lean_object* v___y_428_){
_start:
{
uint64_t v_size_boxed_429_; lean_object* v_res_430_; 
v_size_boxed_429_ = lean_unbox_uint64(v_size_424_);
lean_dec_ref(v_size_424_);
v_res_430_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v_s_423_, v_size_boxed_429_, v_val_425_, v_w_426_, v_lose_427_);
lean_dec_ref(v_w_426_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1(lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v_a_433_ = lean_ctor_get(v_x_431_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_441_ == 0)
{
v___x_435_ = v_x_431_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v_x_431_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_451_; 
v_a_442_ = lean_ctor_get(v_x_431_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_451_ == 0)
{
v___x_444_ = v_x_431_;
v_isShared_445_ = v_isSharedCheck_451_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v_x_431_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_451_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_450_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; 
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object* v_x_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Async_UDP_Socket_recvSelector___lam__1(v_x_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0(lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
v_a_461_ = lean_ctor_get(v_x_459_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v_x_459_);
if (v_isSharedCheck_469_ == 0)
{
v___x_463_ = v_x_459_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v_x_459_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
}
else
{
lean_object* v___x_470_; 
lean_dec_ref(v_x_459_);
v___x_470_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1));
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object* v_x_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_Async_UDP_Socket_recvSelector___lam__0(v_x_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2(lean_object* v_s_474_){
_start:
{
lean_object* v_val_477_; lean_object* v___x_479_; 
v___x_479_ = lean_uv_udp_cancel_recv(v_s_474_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 1);
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
v_val_477_ = v___x_485_;
goto v___jp_476_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
v_a_488_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_479_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_479_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 0);
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
v_val_477_ = v___x_493_;
goto v___jp_476_;
}
}
}
v___jp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_val_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed(lean_object* v_s_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Async_UDP_Socket_recvSelector___lam__2(v_s_496_);
lean_dec(v_s_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3(lean_object* v___x_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed(lean_object* v___x_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_Async_UDP_Socket_recvSelector___lam__3(v___x_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4(lean_object* v_s_507_, uint64_t v_size_508_, lean_object* v_waiter_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_a_513_; 
if (lean_obj_tag(v_a_510_) == 0)
{
lean_object* v___x_515_; 
lean_dec(v_s_507_);
v___x_515_ = lean_box(0);
v_a_513_ = v___x_515_;
goto v___jp_512_;
}
else
{
lean_object* v_val_516_; lean_object* v___f_517_; lean_object* v___x_518_; 
v_val_516_ = lean_ctor_get(v_a_510_, 0);
lean_inc(v_val_516_);
lean_dec_ref(v_a_510_);
v___f_517_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0));
v___x_518_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v_s_507_, v_size_508_, v_val_516_, v_waiter_509_, v___f_517_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref(v___x_518_);
v_a_513_ = v_a_519_;
goto v___jp_512_;
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_518_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 0);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
v___jp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_a_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed(lean_object* v_s_528_, lean_object* v_size_529_, lean_object* v_waiter_530_, lean_object* v_a_531_, lean_object* v___y_532_){
_start:
{
uint64_t v_size_boxed_533_; lean_object* v_res_534_; 
v_size_boxed_533_ = lean_unbox_uint64(v_size_529_);
lean_dec_ref(v_size_529_);
v_res_534_ = l_Std_Async_UDP_Socket_recvSelector___lam__4(v_s_528_, v_size_boxed_533_, v_waiter_530_, v_a_531_);
lean_dec_ref(v_waiter_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5(lean_object* v___f_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref(v___f_539_);
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
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_a_551_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_a_551_);
lean_dec_ref(v_x_540_);
v___x_552_ = lean_io_promise_result_opt(v_a_551_);
lean_dec(v_a_551_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = 0;
v___x_555_ = lean_io_map_task(v___f_539_, v___x_552_, v___x_553_, v___x_554_);
lean_dec_ref(v___x_555_);
v___x_556_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1));
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed(lean_object* v___f_557_, lean_object* v_x_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Async_UDP_Socket_recvSelector___lam__5(v___f_557_, v_x_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6(lean_object* v_s_561_, uint64_t v_size_562_, lean_object* v_waiter_563_){
_start:
{
lean_object* v___x_565_; lean_object* v___f_566_; lean_object* v___f_567_; lean_object* v_val_569_; lean_object* v___x_574_; 
v___x_565_ = lean_box_uint64(v_size_562_);
lean_inc(v_s_561_);
v___f_566_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_566_, 0, v_s_561_);
lean_closure_set(v___f_566_, 1, v___x_565_);
lean_closure_set(v___f_566_, 2, v_waiter_563_);
v___f_567_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_567_, 0, v___f_566_);
v___x_574_ = lean_uv_udp_wait_readable(v_s_561_);
lean_dec(v_s_561_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 1);
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
v_val_569_ = v___x_580_;
goto v___jp_568_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_574_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_574_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 0);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v_val_569_ = v___x_588_;
goto v___jp_568_;
}
}
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v_val_569_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = 0;
v___x_573_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_571_, v___x_572_, v___x_570_, v___f_567_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed(lean_object* v_s_591_, lean_object* v_size_592_, lean_object* v_waiter_593_, lean_object* v___y_594_){
_start:
{
uint64_t v_size_boxed_595_; lean_object* v_res_596_; 
v_size_boxed_595_ = lean_unbox_uint64(v_size_592_);
lean_dec_ref(v_size_592_);
v_res_596_ = l_Std_Async_UDP_Socket_recvSelector___lam__6(v_s_591_, v_size_boxed_595_, v_waiter_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10(lean_object* v___f_597_, lean_object* v_s_598_, uint64_t v_size_599_, lean_object* v___f_600_, lean_object* v___f_601_, lean_object* v_x_602_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v___f_601_);
lean_dec_ref(v___f_600_);
lean_dec(v_s_598_);
lean_dec_ref(v___f_597_);
v_a_604_ = lean_ctor_get(v_x_602_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_612_ == 0)
{
v___x_606_ = v_x_602_;
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v_x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_612_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_611_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; 
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_643_; 
v_a_613_ = lean_ctor_get(v_x_602_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_602_);
if (v_isSharedCheck_643_ == 0)
{
v___x_615_ = v_x_602_;
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v_x_602_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_val_618_; uint8_t v___x_623_; 
v___x_623_ = lean_unbox(v_a_613_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
lean_dec_ref(v___f_601_);
lean_dec_ref(v___f_600_);
v___x_624_ = lean_uv_udp_cancel_recv(v_s_598_);
lean_dec(v_s_598_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref(v___x_624_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_a_625_);
v___x_627_ = v___x_615_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v_val_618_ = v___x_627_;
goto v___jp_617_;
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; 
v_a_629_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_629_);
lean_dec_ref(v___x_624_);
if (v_isShared_616_ == 0)
{
lean_ctor_set_tag(v___x_615_, 0);
lean_ctor_set(v___x_615_, 0, v_a_629_);
v___x_631_ = v___x_615_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v_val_618_ = v___x_631_;
goto v___jp_617_;
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; 
lean_del_object(v___x_615_);
lean_dec_ref(v___f_597_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_box_uint64(v_size_599_);
v___f_635_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed), 4, 3);
lean_closure_set(v___f_635_, 0, v___x_633_);
lean_closure_set(v___f_635_, 1, v_s_598_);
lean_closure_set(v___f_635_, 2, v___x_634_);
v___x_636_ = lean_io_as_task(v___f_635_, v___x_633_);
v___x_637_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
v___x_638_ = lean_task_bind(v___x_636_, v___f_600_, v___x_633_, v___x_637_);
v___x_639_ = lean_task_get_own(v___x_638_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = 0;
v___x_642_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_633_, v___x_641_, v___x_640_, v___f_601_);
return v___x_642_;
}
v___jp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; 
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_val_618_);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
v___x_622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_620_, v___x_621_, v___x_619_, v___f_597_);
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object* v___f_644_, lean_object* v_s_645_, lean_object* v_size_646_, lean_object* v___f_647_, lean_object* v___f_648_, lean_object* v_x_649_, lean_object* v___y_650_){
_start:
{
uint64_t v_size_boxed_651_; lean_object* v_res_652_; 
v_size_boxed_651_ = lean_unbox_uint64(v_size_646_);
lean_dec_ref(v_size_646_);
v_res_652_ = l_Std_Async_UDP_Socket_recvSelector___lam__10(v___f_644_, v_s_645_, v_size_boxed_651_, v___f_647_, v___f_648_, v_x_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7(lean_object* v___f_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref(v___f_653_);
v_a_656_ = lean_ctor_get(v_x_654_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v_x_654_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v_x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_678_; 
v_a_665_ = lean_ctor_get(v_x_654_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_678_ == 0)
{
v___x_667_ = v_x_654_;
v_isShared_668_ = v_isSharedCheck_678_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v_x_654_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_678_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_669_ = l_IO_Promise_isResolved___redArg(v_a_665_);
lean_dec(v_a_665_);
v___x_670_ = lean_box(v___x_669_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_670_);
v___x_672_ = v___x_667_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_677_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; 
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = 0;
v___x_676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_674_, v___x_675_, v___x_673_, v___f_653_);
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object* v___f_679_, lean_object* v_x_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_Async_UDP_Socket_recvSelector___lam__7(v___f_679_, v_x_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8(lean_object* v___f_683_, lean_object* v_s_684_){
_start:
{
lean_object* v_val_687_; lean_object* v___x_692_; 
v___x_692_ = lean_uv_udp_wait_readable(v_s_684_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set_tag(v___x_695_, 1);
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v_val_687_ = v___x_698_;
goto v___jp_686_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_692_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v_val_687_ = v___x_706_;
goto v___jp_686_;
}
}
}
v___jp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; 
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_val_687_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = 0;
v___x_691_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_689_, v___x_690_, v___x_688_, v___f_683_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object* v___f_709_, lean_object* v_s_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_Async_UDP_Socket_recvSelector___lam__8(v___f_709_, v_s_710_);
lean_dec(v_s_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector(lean_object* v_s_715_, uint64_t v_size_716_){
_start:
{
lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___f_726_; lean_object* v___x_727_; 
v___f_717_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0));
v___f_718_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__0));
v___f_719_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__1));
lean_inc_n(v_s_715_, 3);
v___f_720_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_720_, 0, v_s_715_);
v___x_721_ = lean_box_uint64(v_size_716_);
v___f_722_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_722_, 0, v_s_715_);
lean_closure_set(v___f_722_, 1, v___x_721_);
v___x_723_ = lean_box_uint64(v_size_716_);
v___f_724_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed), 7, 5);
lean_closure_set(v___f_724_, 0, v___f_719_);
lean_closure_set(v___f_724_, 1, v_s_715_);
lean_closure_set(v___f_724_, 2, v___x_723_);
lean_closure_set(v___f_724_, 3, v___f_717_);
lean_closure_set(v___f_724_, 4, v___f_718_);
v___f_725_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_725_, 0, v___f_724_);
v___f_726_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_726_, 0, v___f_725_);
lean_closure_set(v___f_726_, 1, v_s_715_);
v___x_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_727_, 0, v___f_726_);
lean_ctor_set(v___x_727_, 1, v___f_722_);
lean_ctor_set(v___x_727_, 2, v___f_720_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___boxed(lean_object* v_s_728_, lean_object* v_size_729_){
_start:
{
uint64_t v_size_boxed_730_; lean_object* v_res_731_; 
v_size_boxed_730_ = lean_unbox_uint64(v_size_729_);
lean_dec_ref(v_size_729_);
v_res_731_ = l_Std_Async_UDP_Socket_recvSelector(v_s_728_, v_size_boxed_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getSockName(lean_object* v_s_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_uv_udp_getsockname(v_s_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getSockName___boxed(lean_object* v_s_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_Async_UDP_Socket_getSockName(v_s_735_);
lean_dec(v_s_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getPeerName(lean_object* v_s_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_uv_udp_getpeername(v_s_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getPeerName___boxed(lean_object* v_s_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Std_Async_UDP_Socket_getPeerName(v_s_741_);
lean_dec(v_s_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setBroadcast(lean_object* v_s_744_, uint8_t v_enable_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = lean_uv_udp_set_broadcast(v_s_744_, v_enable_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setBroadcast___boxed(lean_object* v_s_748_, lean_object* v_enable_749_, lean_object* v_a_750_){
_start:
{
uint8_t v_enable_boxed_751_; lean_object* v_res_752_; 
v_enable_boxed_751_ = lean_unbox(v_enable_749_);
v_res_752_ = l_Std_Async_UDP_Socket_setBroadcast(v_s_748_, v_enable_boxed_751_);
lean_dec(v_s_748_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastLoop(lean_object* v_s_753_, uint8_t v_enable_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_uv_udp_set_multicast_loop(v_s_753_, v_enable_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastLoop___boxed(lean_object* v_s_757_, lean_object* v_enable_758_, lean_object* v_a_759_){
_start:
{
uint8_t v_enable_boxed_760_; lean_object* v_res_761_; 
v_enable_boxed_760_ = lean_unbox(v_enable_758_);
v_res_761_ = l_Std_Async_UDP_Socket_setMulticastLoop(v_s_757_, v_enable_boxed_760_);
lean_dec(v_s_757_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastTTL(lean_object* v_s_762_, uint32_t v_ttl_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_uv_udp_set_multicast_ttl(v_s_762_, v_ttl_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastTTL___boxed(lean_object* v_s_766_, lean_object* v_ttl_767_, lean_object* v_a_768_){
_start:
{
uint32_t v_ttl_boxed_769_; lean_object* v_res_770_; 
v_ttl_boxed_769_ = lean_unbox_uint32(v_ttl_767_);
lean_dec(v_ttl_767_);
v_res_770_ = l_Std_Async_UDP_Socket_setMulticastTTL(v_s_766_, v_ttl_boxed_769_);
lean_dec(v_s_766_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMembership(lean_object* v_s_771_, lean_object* v_multicastAddr_772_, lean_object* v_interfaceAddr_773_, uint8_t v_membership_774_){
_start:
{
if (v_membership_774_ == 0)
{
uint8_t v___x_776_; lean_object* v___x_777_; 
v___x_776_ = 0;
v___x_777_ = lean_uv_udp_set_membership(v_s_771_, v_multicastAddr_772_, v_interfaceAddr_773_, v___x_776_);
return v___x_777_;
}
else
{
uint8_t v___x_778_; lean_object* v___x_779_; 
v___x_778_ = 1;
v___x_779_ = lean_uv_udp_set_membership(v_s_771_, v_multicastAddr_772_, v_interfaceAddr_773_, v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMembership___boxed(lean_object* v_s_780_, lean_object* v_multicastAddr_781_, lean_object* v_interfaceAddr_782_, lean_object* v_membership_783_, lean_object* v_a_784_){
_start:
{
uint8_t v_membership_boxed_785_; lean_object* v_res_786_; 
v_membership_boxed_785_ = lean_unbox(v_membership_783_);
v_res_786_ = l_Std_Async_UDP_Socket_setMembership(v_s_780_, v_multicastAddr_781_, v_interfaceAddr_782_, v_membership_boxed_785_);
lean_dec(v_interfaceAddr_782_);
lean_dec_ref(v_multicastAddr_781_);
lean_dec(v_s_780_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastInterface(lean_object* v_s_787_, lean_object* v_interfaceAddr_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_uv_udp_set_multicast_interface(v_s_787_, v_interfaceAddr_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastInterface___boxed(lean_object* v_s_791_, lean_object* v_interfaceAddr_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_Async_UDP_Socket_setMulticastInterface(v_s_791_, v_interfaceAddr_792_);
lean_dec_ref(v_interfaceAddr_792_);
lean_dec(v_s_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setTTL(lean_object* v_s_795_, uint32_t v_ttl_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_uv_udp_set_ttl(v_s_795_, v_ttl_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setTTL___boxed(lean_object* v_s_799_, lean_object* v_ttl_800_, lean_object* v_a_801_){
_start:
{
uint32_t v_ttl_boxed_802_; lean_object* v_res_803_; 
v_ttl_boxed_802_ = lean_unbox_uint32(v_ttl_800_);
lean_dec(v_ttl_800_);
v_res_803_ = l_Std_Async_UDP_Socket_setTTL(v_s_799_, v_ttl_boxed_802_);
lean_dec(v_s_799_);
return v_res_803_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_UDP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_UDP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

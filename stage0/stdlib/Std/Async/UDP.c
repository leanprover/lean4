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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_uv_udp_set_multicast_ttl(lean_object*, uint32_t);
lean_object* lean_uv_udp_getpeername(lean_object*);
lean_object* lean_uv_udp_set_membership(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_udp_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Std_Async_UDP_Membership_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Membership_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Async_UDP_Membership_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Async_UDP_Membership_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Async_UDP_Membership_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Async_UDP_Membership_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Membership_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Async_UDP_Membership_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Async_UDP_Membership_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(lean_object* v_leaveGroup_24_){
_start:
{
lean_inc(v_leaveGroup_24_);
return v_leaveGroup_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___redArg___boxed(lean_object* v_leaveGroup_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(v_leaveGroup_25_);
lean_dec(v_leaveGroup_25_);
return v_res_26_;
}
}
lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_leaveGroup_30_){
_start:
{
lean_inc(v_leaveGroup_30_);
return v_leaveGroup_30_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Membership_leaveGroup_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_leaveGroup_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Async_UDP_Membership_leaveGroup_elim(lean_box(0), v_t_28_, lean_box(0), v_leaveGroup_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_leaveGroup_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_leaveGroup_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Async_UDP_Membership_leaveGroup_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_leaveGroup_35_);
lean_dec(v_leaveGroup_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg(lean_object* v_enterGroup_38_){
_start:
{
lean_inc(v_enterGroup_38_);
return v_enterGroup_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___redArg___boxed(lean_object* v_enterGroup_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Async_UDP_Membership_enterGroup_elim___redArg(v_enterGroup_39_);
lean_dec(v_enterGroup_39_);
return v_res_40_;
}
}
lean_object* l_Std_Async_UDP_Membership_enterGroup_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_enterGroup_44_){
_start:
{
lean_inc(v_enterGroup_44_);
return v_enterGroup_44_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Membership_enterGroup_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_enterGroup_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Async_UDP_Membership_enterGroup_elim(lean_box(0), v_t_42_, lean_box(0), v_enterGroup_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Membership_enterGroup_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_enterGroup_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Async_UDP_Membership_enterGroup_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_enterGroup_49_);
lean_dec(v_enterGroup_49_);
return v_res_51_;
}
}
lean_object* l_Std_Async_UDP_Socket_mk(){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_uv_udp_new();
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_53_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_53_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_70_;
v_res_70_ = l_Std_Async_UDP_Socket_mk();
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_mk___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Async_UDP_Socket_mk();
return v_res_72_;
}
}
lean_object* l_Std_Async_UDP_Socket_bind(lean_object* v_s_73_, lean_object* v_addr_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_uv_udp_bind(v_s_73_, v_addr_74_);
return v___x_76_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_73_ = stack[0].m_obj;
lean_object* v_addr_74_ = stack[1].m_obj;
lean_object* v_res_77_;
v_res_77_ = l_Std_Async_UDP_Socket_bind(v_s_73_, v_addr_74_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_bind___boxed(lean_object* v_s_78_, lean_object* v_addr_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_Async_UDP_Socket_bind(v_s_78_, v_addr_79_);
lean_dec_ref(v_addr_79_);
lean_dec(v_s_78_);
return v_res_81_;
}
}
lean_object* l_Std_Async_UDP_Socket_connect(lean_object* v_s_82_, lean_object* v_addr_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_uv_udp_connect(v_s_82_, v_addr_83_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_connect_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_82_ = stack[0].m_obj;
lean_object* v_addr_83_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Std_Async_UDP_Socket_connect(v_s_82_, v_addr_83_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_connect___boxed(lean_object* v_s_87_, lean_object* v_addr_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_Async_UDP_Socket_connect(v_s_87_, v_addr_88_);
lean_dec_ref(v_addr_88_);
lean_dec(v_s_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0(lean_object* v___x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_mk_io_user_error(v___x_91_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
else
{
lean_object* v_val_95_; 
lean_dec_ref(v___x_91_);
v_val_95_ = lean_ctor_get(v_x_92_, 0);
lean_inc(v_val_95_);
return v_val_95_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__0___boxed(lean_object* v___x_96_, lean_object* v_x_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_Async_UDP_Socket_sendAll___lam__0(v___x_96_, v_x_97_);
lean_dec(v_x_97_);
return v_res_98_;
}
}
lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1(lean_object* v___f_99_, lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v___f_99_);
v_a_102_ = lean_ctor_get(v_x_100_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_x_100_);
if (v_isSharedCheck_110_ == 0)
{
v___x_104_ = v_x_100_;
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v_x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_109_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_108_; 
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
else
{
lean_object* v_a_111_; 
v_a_111_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v_x_100_, 1);
if (lean_obj_tag(v_a_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_120_; 
lean_dec_ref(v___f_99_);
v_a_112_ = lean_ctor_get(v_a_111_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_a_111_);
if (v_isSharedCheck_120_ == 0)
{
v___x_114_ = v_a_111_;
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v_a_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_120_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_119_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_a_121_ = lean_ctor_get(v_a_111_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v_a_111_, 1);
v___x_122_ = lean_io_promise_result_opt(v_a_121_);
lean_dec(v_a_121_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = 0;
v___x_125_ = lean_task_map(v___f_99_, v___x_122_, v___x_123_, v___x_124_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_sendAll___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_99_ = stack[0].m_obj;
lean_object* v_x_100_ = stack[1].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Std_Async_UDP_Socket_sendAll___lam__1(v___f_99_, v_x_100_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___lam__1___boxed(lean_object* v___f_128_, lean_object* v_x_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_Async_UDP_Socket_sendAll___lam__1(v___f_128_, v_x_129_);
return v_res_131_;
}
}
lean_object* l_Std_Async_UDP_Socket_sendAll(lean_object* v_s_137_, lean_object* v_data_138_, lean_object* v_addr_139_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v_val_145_; lean_object* v___x_149_; 
v___f_141_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = 0;
v___x_149_ = lean_uv_udp_send(v_s_137_, v_data_138_, v_addr_139_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 1);
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
v_val_145_ = v___x_155_;
goto v___jp_144_;
}
}
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_158_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_149_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_149_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 0);
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
v_val_145_ = v___x_163_;
goto v___jp_144_;
}
}
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v_val_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
v___x_148_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_142_, v___x_143_, v___x_147_, v___f_141_);
return v___x_148_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_sendAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_137_ = stack[0].m_obj;
lean_object* v_data_138_ = stack[1].m_obj;
lean_object* v_addr_139_ = stack[2].m_obj;
lean_object* v_res_166_;
v_res_166_ = l_Std_Async_UDP_Socket_sendAll(v_s_137_, v_data_138_, v_addr_139_);
stack->m_obj
 = v_res_166_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_sendAll___boxed(lean_object* v_s_167_, lean_object* v_data_168_, lean_object* v_addr_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_Async_UDP_Socket_sendAll(v_s_167_, v_data_168_, v_addr_169_);
lean_dec(v_addr_169_);
lean_dec(v_s_167_);
return v_res_171_;
}
}
lean_object* l_Std_Async_UDP_Socket_send(lean_object* v_s_172_, lean_object* v_data_173_, lean_object* v_addr_174_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v_val_183_; lean_object* v___x_187_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_mk_empty_array_with_capacity(v___x_176_);
v___x_178_ = lean_array_push(v___x_177_, v_data_173_);
v___f_179_ = ((lean_object*)(l_Std_Async_UDP_Socket_sendAll___closed__2));
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = 0;
v___x_187_ = lean_uv_udp_send(v_s_172_, v___x_178_, v_addr_174_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_187_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_187_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 1);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
v_val_183_ = v___x_193_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_187_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_187_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 0);
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
v_val_183_ = v___x_201_;
goto v___jp_182_;
}
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_val_183_);
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
v___x_186_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_180_, v___x_181_, v___x_185_, v___f_179_);
return v___x_186_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_172_ = stack[0].m_obj;
lean_object* v_data_173_ = stack[1].m_obj;
lean_object* v_addr_174_ = stack[2].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Std_Async_UDP_Socket_send(v_s_172_, v_data_173_, v_addr_174_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_send___boxed(lean_object* v_s_205_, lean_object* v_data_206_, lean_object* v_addr_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Std_Async_UDP_Socket_send(v_s_205_, v_data_206_, v_addr_207_);
lean_dec(v_addr_207_);
lean_dec(v_s_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0(lean_object* v___x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_mk_io_user_error(v___x_210_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
else
{
lean_object* v_val_214_; 
lean_dec_ref(v___x_210_);
v_val_214_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_val_214_);
return v_val_214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__0___boxed(lean_object* v___x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_Async_UDP_Socket_recv___lam__0(v___x_215_, v_x_216_);
lean_dec(v_x_216_);
return v_res_217_;
}
}
lean_object* l_Std_Async_UDP_Socket_recv___lam__1(lean_object* v___f_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v___f_218_);
v_a_221_ = lean_ctor_get(v_x_219_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v_x_219_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v_x_219_);
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
lean_object* v_a_230_; 
v_a_230_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v_x_219_, 1);
if (lean_obj_tag(v_a_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v___f_218_);
v_a_231_ = lean_ctor_get(v_a_230_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_a_230_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v_a_230_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v_a_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_240_ = lean_ctor_get(v_a_230_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v_a_230_, 1);
v___x_241_ = lean_io_promise_result_opt(v_a_240_);
lean_dec(v_a_240_);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = 0;
v___x_244_ = lean_task_map(v___f_218_, v___x_241_, v___x_242_, v___x_243_);
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recv___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_218_ = stack[0].m_obj;
lean_object* v_x_219_ = stack[1].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Std_Async_UDP_Socket_recv___lam__1(v___f_218_, v_x_219_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___lam__1___boxed(lean_object* v___f_247_, lean_object* v_x_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_Async_UDP_Socket_recv___lam__1(v___f_247_, v_x_248_);
return v_res_250_;
}
}
lean_object* l_Std_Async_UDP_Socket_recv(lean_object* v_s_255_, uint64_t v_size_256_){
_start:
{
lean_object* v___f_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v_val_262_; lean_object* v___x_266_; 
v___f_258_ = ((lean_object*)(l_Std_Async_UDP_Socket_recv___closed__1));
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = 0;
v___x_266_ = lean_uv_udp_recv(v_s_255_, v_size_256_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set_tag(v___x_269_, 1);
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
v_val_262_ = v___x_272_;
goto v___jp_261_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_266_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_266_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 0);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
v_val_262_ = v___x_280_;
goto v___jp_261_;
}
}
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v_val_262_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
v___x_265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_259_, v___x_260_, v___x_264_, v___f_258_);
return v___x_265_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_255_ = stack[0].m_obj;
uint64_t v_size_256_ = stack[1].m_num;
lean_object* v_res_283_;
v_res_283_ = l_Std_Async_UDP_Socket_recv(v_s_255_, v_size_256_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recv___boxed(lean_object* v_s_284_, lean_object* v_size_285_, lean_object* v_a_286_){
_start:
{
uint64_t v_size_boxed_287_; lean_object* v_res_288_; 
v_size_boxed_287_ = lean_unbox_uint64(v_size_285_);
lean_dec_ref(v_size_285_);
v_res_288_ = l_Std_Async_UDP_Socket_recv(v_s_284_, v_size_boxed_287_);
lean_dec(v_s_284_);
return v_res_288_;
}
}
lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(lean_object* v_e_289_){
_start:
{
if (lean_obj_tag(v_e_289_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_300_; 
v_a_291_ = lean_ctor_get(v_e_289_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v_e_289_);
if (v_isSharedCheck_300_ == 0)
{
v___x_293_ = v_e_289_;
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v_e_289_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_300_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_295_ = lean_io_error_to_string(v_a_291_);
v___x_296_ = lean_mk_io_user_error(v___x_295_);
if (v_isShared_294_ == 0)
{
lean_ctor_set_tag(v___x_293_, 1);
lean_ctor_set(v___x_293_, 0, v___x_296_);
v___x_298_ = v___x_293_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_a_301_ = lean_ctor_get(v_e_289_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_e_289_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v_e_289_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v_e_289_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 0);
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_289_ = stack[0].m_obj;
lean_object* v_res_309_;
v_res_309_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_289_);
stack->m_obj
 = v_res_309_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg___boxed(lean_object* v_e_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_310_);
return v_res_312_;
}
}
lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(lean_object* v_00_u03b1_313_, lean_object* v_e_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_314_);
return v___x_316_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_314_ = stack[1].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(lean_box(0), v_e_314_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_318_, lean_object* v_e_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(v_00_u03b1_318_, v_e_319_);
return v_res_321_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(lean_object* v_promise_322_, lean_object* v_value_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_io_promise_resolve(v_value_323_, v_promise_322_);
return v___x_325_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_322_ = stack[0].m_obj;
lean_object* v_value_323_ = stack[1].m_obj;
lean_object* v_res_326_;
v_res_326_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(v_promise_322_, v_value_323_);
stack->m_obj
 = v_res_326_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0___boxed(lean_object* v_promise_327_, lean_object* v_value_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(v_promise_327_, v_value_328_);
lean_dec(v_promise_327_);
return v_res_330_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(lean_object* v___x_334_, uint64_t v_size_335_, lean_object* v_val_336_, lean_object* v_w_337_, lean_object* v_lose_338_){
_start:
{
lean_object* v_finished_340_; lean_object* v_promise_341_; lean_object* v_a_343_; lean_object* v___f_347_; lean_object* v___x_366_; uint8_t v___y_368_; uint8_t v___x_375_; 
v_finished_340_ = lean_ctor_get(v_w_337_, 0);
lean_inc(v_finished_340_);
v_promise_341_ = lean_ctor_get(v_w_337_, 1);
lean_inc_n(v_promise_341_, 2);
lean_dec_ref(v_w_337_);
v___f_347_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0___boxed), 3, 1);
lean_closure_set(v___f_347_, 0, v_promise_341_);
v___x_366_ = lean_st_ref_take(v_finished_340_);
v___x_375_ = lean_unbox(v___x_366_);
lean_dec(v___x_366_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
v___x_376_ = 1;
v___y_368_ = v___x_376_;
goto v___jp_367_;
}
else
{
uint8_t v___x_377_; 
v___x_377_ = 0;
v___y_368_ = v___x_377_;
goto v___jp_367_;
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_a_343_);
v___x_345_ = lean_io_promise_resolve(v___x_344_, v_promise_341_);
lean_dec(v_promise_341_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
v___jp_348_:
{
lean_object* v___x_349_; 
v___x_349_ = lean_uv_udp_recv(v___x_334_, v_size_335_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_promise_341_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_364_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_364_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_364_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___f_354_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__1));
v___x_355_ = lean_io_promise_result_opt(v_a_350_);
lean_dec(v_a_350_);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = 0;
v___x_358_ = lean_task_map(v___f_354_, v___x_355_, v___x_356_, v___x_357_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_io_map_task(v___f_347_, v___x_358_, v___x_356_, v___x_357_);
lean_dec_ref(v___x_360_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_359_);
v___x_362_ = v___x_352_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_359_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v_a_365_; 
lean_dec_ref(v___f_347_);
v_a_365_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_349_, 1);
v_a_343_ = v_a_365_;
goto v___jp_342_;
}
}
v___jp_367_:
{
uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = 1;
v___x_370_ = lean_box(v___x_369_);
v___x_371_ = lean_st_ref_put(v_finished_340_, v___x_370_);
lean_dec(v_finished_340_);
if (v___y_368_ == 0)
{
lean_object* v___x_372_; 
lean_dec_ref(v___f_347_);
lean_dec(v_promise_341_);
lean_dec_ref(v_val_336_);
v___x_372_ = lean_apply_1(v_lose_338_, lean_box(0));
return v___x_372_;
}
else
{
lean_object* v___x_373_; 
lean_dec_ref(v_lose_338_);
v___x_373_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_val_336_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_dec_ref_known(v___x_373_, 1);
goto v___jp_348_;
}
else
{
if (lean_obj_tag(v___x_373_) == 0)
{
lean_dec_ref_known(v___x_373_, 1);
goto v___jp_348_;
}
else
{
lean_object* v_a_374_; 
lean_dec_ref(v___f_347_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
v_a_343_ = v_a_374_;
goto v___jp_342_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_334_ = stack[0].m_obj;
uint64_t v_size_335_ = stack[1].m_num;
lean_object* v_val_336_ = stack[2].m_obj;
lean_object* v_w_337_ = stack[3].m_obj;
lean_object* v_lose_338_ = stack[4].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v___x_334_, v_size_335_, v_val_336_, v_w_337_, v_lose_338_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___boxed(lean_object* v___x_379_, lean_object* v_size_380_, lean_object* v_val_381_, lean_object* v_w_382_, lean_object* v_lose_383_, lean_object* v___y_384_){
_start:
{
uint64_t v_size_boxed_385_; lean_object* v_res_386_; 
v_size_boxed_385_ = lean_unbox_uint64(v_size_380_);
lean_dec_ref(v_size_380_);
v_res_386_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v___x_379_, v_size_boxed_385_, v_val_381_, v_w_382_, v_lose_383_);
lean_dec(v___x_379_);
return v_res_386_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0(lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v_a_389_ = lean_ctor_get(v_x_387_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_x_387_);
if (v_isSharedCheck_397_ == 0)
{
v___x_391_ = v_x_387_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v_x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_407_; 
v_a_398_ = lean_ctor_get(v_x_387_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_387_);
if (v_isSharedCheck_407_ == 0)
{
v___x_400_ = v_x_387_;
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v_x_387_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_407_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v_a_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_406_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_387_ = stack[0].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Std_Async_UDP_Socket_recvSelector___lam__0(v_x_387_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed(lean_object* v_x_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_Async_UDP_Socket_recvSelector___lam__0(v_x_409_);
return v_res_411_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1(lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_a_418_ = lean_ctor_get(v_x_416_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_416_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v_x_416_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v_x_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_425_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
else
{
lean_object* v___x_427_; 
lean_dec_ref_known(v_x_416_, 1);
v___x_427_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__1___closed__1));
return v___x_427_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_416_ = stack[0].m_obj;
lean_object* v_res_428_;
v_res_428_ = l_Std_Async_UDP_Socket_recvSelector___lam__1(v_x_416_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed(lean_object* v_x_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_Async_UDP_Socket_recvSelector___lam__1(v_x_429_);
return v_res_431_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2(lean_object* v_s_432_){
_start:
{
lean_object* v_val_435_; lean_object* v___x_437_; 
v___x_437_ = lean_uv_udp_cancel_recv(v_s_432_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 1);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v_val_435_ = v___x_443_;
goto v___jp_434_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_437_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_437_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
v_val_435_ = v___x_451_;
goto v___jp_434_;
}
}
}
v___jp_434_:
{
lean_object* v___x_436_; 
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v_val_435_);
return v___x_436_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_432_ = stack[0].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_Std_Async_UDP_Socket_recvSelector___lam__2(v_s_432_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed(lean_object* v_s_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_Async_UDP_Socket_recvSelector___lam__2(v_s_455_);
lean_dec(v_s_455_);
return v_res_457_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3(lean_object* v___x_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
return v___x_460_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_458_ = stack[0].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Std_Async_UDP_Socket_recvSelector___lam__3(v___x_458_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed(lean_object* v___x_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Async_UDP_Socket_recvSelector___lam__3(v___x_462_);
return v_res_464_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4(lean_object* v_s_467_, uint64_t v_size_468_, lean_object* v_waiter_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_a_473_; 
if (lean_obj_tag(v_a_470_) == 0)
{
lean_object* v___x_475_; 
lean_dec_ref(v_waiter_469_);
v___x_475_ = lean_box(0);
v_a_473_ = v___x_475_;
goto v___jp_472_;
}
else
{
lean_object* v_val_476_; lean_object* v___f_477_; lean_object* v___x_478_; 
v_val_476_ = lean_ctor_get(v_a_470_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_a_470_, 1);
v___f_477_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0));
v___x_478_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(v_s_467_, v_size_468_, v_val_476_, v_waiter_469_, v___f_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_a_473_ = v_a_479_;
goto v___jp_472_;
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_a_480_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_478_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_478_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 0);
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
v___jp_472_:
{
lean_object* v___x_474_; 
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v_a_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_467_ = stack[0].m_obj;
uint64_t v_size_468_ = stack[1].m_num;
lean_object* v_waiter_469_ = stack[2].m_obj;
lean_object* v_a_470_ = stack[3].m_obj;
lean_object* v_res_488_;
v_res_488_ = l_Std_Async_UDP_Socket_recvSelector___lam__4(v_s_467_, v_size_468_, v_waiter_469_, v_a_470_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed(lean_object* v_s_489_, lean_object* v_size_490_, lean_object* v_waiter_491_, lean_object* v_a_492_, lean_object* v___y_493_){
_start:
{
uint64_t v_size_boxed_494_; lean_object* v_res_495_; 
v_size_boxed_494_ = lean_unbox_uint64(v_size_490_);
lean_dec_ref(v_size_490_);
v_res_495_ = l_Std_Async_UDP_Socket_recvSelector___lam__4(v_s_489_, v_size_boxed_494_, v_waiter_491_, v_a_492_);
lean_dec(v_s_489_);
return v_res_495_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5(lean_object* v___f_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v___f_500_);
v_a_503_ = lean_ctor_get(v_x_501_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_x_501_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v_x_501_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v_x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_a_512_ = lean_ctor_get(v_x_501_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v_x_501_, 1);
v___x_513_ = lean_io_promise_result_opt(v_a_512_);
lean_dec(v_a_512_);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = 0;
v___x_516_ = lean_io_map_task(v___f_500_, v___x_513_, v___x_514_, v___x_515_);
lean_dec_ref(v___x_516_);
v___x_517_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1));
return v___x_517_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_500_ = stack[0].m_obj;
lean_object* v_x_501_ = stack[1].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Std_Async_UDP_Socket_recvSelector___lam__5(v___f_500_, v_x_501_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed(lean_object* v___f_519_, lean_object* v_x_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Async_UDP_Socket_recvSelector___lam__5(v___f_519_, v_x_520_);
return v_res_522_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6(lean_object* v_s_523_, uint64_t v_size_524_, lean_object* v_waiter_525_){
_start:
{
lean_object* v___x_527_; lean_object* v___f_528_; lean_object* v___f_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v_val_533_; lean_object* v___x_536_; 
v___x_527_ = lean_box_uint64(v_size_524_);
lean_inc(v_s_523_);
v___f_528_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_528_, 0, v_s_523_);
lean_closure_set(v___f_528_, 1, v___x_527_);
lean_closure_set(v___f_528_, 2, v_waiter_525_);
v___f_529_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_529_, 0, v___f_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = 0;
v___x_536_ = lean_uv_udp_wait_readable(v_s_523_);
lean_dec(v_s_523_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set_tag(v___x_539_, 1);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
v_val_533_ = v___x_542_;
goto v___jp_532_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_536_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_536_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 0);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v_val_533_ = v___x_550_;
goto v___jp_532_;
}
}
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v_val_533_);
v___x_535_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_530_, v___x_531_, v___x_534_, v___f_529_);
return v___x_535_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_523_ = stack[0].m_obj;
uint64_t v_size_524_ = stack[1].m_num;
lean_object* v_waiter_525_ = stack[2].m_obj;
lean_object* v_res_553_;
v_res_553_ = l_Std_Async_UDP_Socket_recvSelector___lam__6(v_s_523_, v_size_524_, v_waiter_525_);
stack->m_obj
 = v_res_553_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed(lean_object* v_s_554_, lean_object* v_size_555_, lean_object* v_waiter_556_, lean_object* v___y_557_){
_start:
{
uint64_t v_size_boxed_558_; lean_object* v_res_559_; 
v_size_boxed_558_ = lean_unbox_uint64(v_size_555_);
lean_dec_ref(v_size_555_);
v_res_559_ = l_Std_Async_UDP_Socket_recvSelector___lam__6(v_s_554_, v_size_boxed_558_, v_waiter_556_);
return v_res_559_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8(lean_object* v___f_560_, lean_object* v___x_561_, uint8_t v___x_562_, lean_object* v_x_563_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
lean_dec(v___x_561_);
lean_dec_ref(v___f_560_);
v_a_565_ = lean_ctor_get(v_x_563_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_x_563_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v_x_563_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v_x_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; 
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
}
else
{
lean_object* v_a_574_; 
v_a_574_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v_x_563_, 1);
if (lean_obj_tag(v_a_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_583_; 
lean_dec(v___x_561_);
lean_dec_ref(v___f_560_);
v_a_575_ = lean_ctor_get(v_a_574_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_574_);
if (v_isSharedCheck_583_ == 0)
{
v___x_577_ = v_a_574_;
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v_a_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_583_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_582_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_a_584_ = lean_ctor_get(v_a_574_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v_a_574_, 1);
v___x_585_ = lean_io_promise_result_opt(v_a_584_);
lean_dec(v_a_584_);
v___x_586_ = lean_task_map(v___f_560_, v___x_585_, v___x_561_, v___x_562_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_560_ = stack[0].m_obj;
lean_object* v___x_561_ = stack[1].m_obj;
uint8_t v___x_562_ = stack[2].m_num;
lean_object* v_x_563_ = stack[3].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_Std_Async_UDP_Socket_recvSelector___lam__8(v___f_560_, v___x_561_, v___x_562_, v_x_563_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed(lean_object* v___f_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v_x_592_, lean_object* v___y_593_){
_start:
{
uint8_t v___x_3189__boxed_594_; lean_object* v_res_595_; 
v___x_3189__boxed_594_ = lean_unbox(v___x_591_);
v_res_595_ = l_Std_Async_UDP_Socket_recvSelector___lam__8(v___f_589_, v___x_590_, v___x_3189__boxed_594_, v_x_592_);
return v_res_595_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7(lean_object* v___f_601_, lean_object* v_s_602_, lean_object* v___f_603_, uint64_t v_size_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v___f_603_);
lean_dec_ref(v___f_601_);
v_a_607_ = lean_ctor_get(v_x_605_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v_x_605_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v_x_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_614_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_664_; 
v_a_616_ = lean_ctor_get(v_x_605_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_x_605_);
if (v_isSharedCheck_664_ == 0)
{
v___x_618_ = v_x_605_;
v_isShared_619_ = v_isSharedCheck_664_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v_x_605_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_664_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___x_620_; 
v___x_620_ = lean_unbox(v_a_616_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v_val_623_; lean_object* v___x_627_; 
lean_dec_ref(v___f_603_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_uv_udp_cancel_recv(v_s_602_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_a_628_);
v___x_630_ = v___x_618_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
v_val_623_ = v___x_630_;
goto v___jp_622_;
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; 
v_a_632_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_627_, 1);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 0);
lean_ctor_set(v___x_618_, 0, v_a_632_);
v___x_634_ = v___x_618_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
v_val_623_ = v___x_634_;
goto v___jp_622_;
}
}
v___jp_622_:
{
lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_val_623_);
v___x_625_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
v___x_626_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_621_, v___x_625_, v___x_624_, v___f_601_);
return v___x_626_;
}
}
else
{
lean_object* v___x_636_; uint8_t v___x_637_; lean_object* v___f_638_; lean_object* v_val_640_; lean_object* v___x_647_; 
lean_dec(v_a_616_);
lean_dec_ref(v___f_601_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = 0;
v___f_638_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___lam__7___closed__0));
v___x_647_ = lean_uv_udp_recv(v_s_602_, v_size_604_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 1);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
v_val_640_ = v___x_653_;
goto v___jp_639_;
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_647_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_647_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 0);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v_val_640_ = v___x_661_;
goto v___jp_639_;
}
}
}
v___jp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v_val_640_);
v___x_642_ = v___x_618_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_val_640_);
v___x_642_ = v_reuseFailAlloc_646_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_636_, v___x_637_, v___x_643_, v___f_638_);
v___x_645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_636_, v___x_637_, v___x_644_, v___f_603_);
return v___x_645_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_601_ = stack[0].m_obj;
lean_object* v_s_602_ = stack[1].m_obj;
lean_object* v___f_603_ = stack[2].m_obj;
uint64_t v_size_604_ = stack[3].m_num;
lean_object* v_x_605_ = stack[4].m_obj;
lean_object* v_res_665_;
v_res_665_ = l_Std_Async_UDP_Socket_recvSelector___lam__7(v___f_601_, v_s_602_, v___f_603_, v_size_604_, v_x_605_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed(lean_object* v___f_666_, lean_object* v_s_667_, lean_object* v___f_668_, lean_object* v_size_669_, lean_object* v_x_670_, lean_object* v___y_671_){
_start:
{
uint64_t v_size_boxed_672_; lean_object* v_res_673_; 
v_size_boxed_672_ = lean_unbox_uint64(v_size_669_);
lean_dec_ref(v_size_669_);
v_res_673_ = l_Std_Async_UDP_Socket_recvSelector___lam__7(v___f_666_, v_s_667_, v___f_668_, v_size_boxed_672_, v_x_670_);
lean_dec(v_s_667_);
return v_res_673_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__9(lean_object* v___f_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_675_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v___f_674_);
v_a_677_ = lean_ctor_get(v_x_675_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_685_ == 0)
{
v___x_679_ = v_x_675_;
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v_x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_685_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_684_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_699_; 
v_a_686_ = lean_ctor_get(v_x_675_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_699_ == 0)
{
v___x_688_ = v_x_675_;
v_isShared_689_ = v_isSharedCheck_699_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v_x_675_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_699_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; uint8_t v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = 0;
v___x_692_ = l_IO_Promise_isResolved___redArg(v_a_686_);
lean_dec(v_a_686_);
v___x_693_ = lean_box(v___x_692_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_693_);
v___x_695_ = v___x_688_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_698_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
v___x_697_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_690_, v___x_691_, v___x_696_, v___f_674_);
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_674_ = stack[0].m_obj;
lean_object* v_x_675_ = stack[1].m_obj;
lean_object* v_res_700_;
v_res_700_ = l_Std_Async_UDP_Socket_recvSelector___lam__9(v___f_674_, v_x_675_);
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__9___boxed(lean_object* v___f_701_, lean_object* v_x_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_Async_UDP_Socket_recvSelector___lam__9(v___f_701_, v_x_702_);
return v_res_704_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10(lean_object* v___f_705_, lean_object* v_s_706_){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v_val_711_; lean_object* v___x_714_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = 0;
v___x_714_ = lean_uv_udp_wait_readable(v_s_706_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 1);
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_val_711_ = v___x_720_;
goto v___jp_710_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_a_723_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_714_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_714_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 0);
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
v_val_711_ = v___x_728_;
goto v___jp_710_;
}
}
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_val_711_);
v___x_713_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_708_, v___x_709_, v___x_712_, v___f_705_);
return v___x_713_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_705_ = stack[0].m_obj;
lean_object* v_s_706_ = stack[1].m_obj;
lean_object* v_res_731_;
v_res_731_ = l_Std_Async_UDP_Socket_recvSelector___lam__10(v___f_705_, v_s_706_);
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed(lean_object* v___f_732_, lean_object* v_s_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Async_UDP_Socket_recvSelector___lam__10(v___f_732_, v_s_733_);
lean_dec(v_s_733_);
return v_res_735_;
}
}
lean_object* l_Std_Async_UDP_Socket_recvSelector(lean_object* v_s_738_, uint64_t v_size_739_){
_start:
{
lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___f_748_; lean_object* v___x_749_; 
v___f_740_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__0));
v___f_741_ = ((lean_object*)(l_Std_Async_UDP_Socket_recvSelector___closed__1));
lean_inc_n(v_s_738_, 3);
v___f_742_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_742_, 0, v_s_738_);
v___x_743_ = lean_box_uint64(v_size_739_);
v___f_744_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_744_, 0, v_s_738_);
lean_closure_set(v___f_744_, 1, v___x_743_);
v___x_745_ = lean_box_uint64(v_size_739_);
v___f_746_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed), 6, 4);
lean_closure_set(v___f_746_, 0, v___f_741_);
lean_closure_set(v___f_746_, 1, v_s_738_);
lean_closure_set(v___f_746_, 2, v___f_740_);
lean_closure_set(v___f_746_, 3, v___x_745_);
v___f_747_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__9___boxed), 3, 1);
lean_closure_set(v___f_747_, 0, v___f_746_);
v___f_748_ = lean_alloc_closure((void*)(l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed), 3, 2);
lean_closure_set(v___f_748_, 0, v___f_747_);
lean_closure_set(v___f_748_, 1, v_s_738_);
v___x_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_749_, 0, v___f_748_);
lean_ctor_set(v___x_749_, 1, v___f_744_);
lean_ctor_set(v___x_749_, 2, v___f_742_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_recvSelector_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_738_ = stack[0].m_obj;
uint64_t v_size_739_ = stack[1].m_num;
lean_object* v_res_750_;
v_res_750_ = l_Std_Async_UDP_Socket_recvSelector(v_s_738_, v_size_739_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_recvSelector___boxed(lean_object* v_s_751_, lean_object* v_size_752_){
_start:
{
uint64_t v_size_boxed_753_; lean_object* v_res_754_; 
v_size_boxed_753_ = lean_unbox_uint64(v_size_752_);
lean_dec_ref(v_size_752_);
v_res_754_ = l_Std_Async_UDP_Socket_recvSelector(v_s_751_, v_size_boxed_753_);
return v_res_754_;
}
}
lean_object* l_Std_Async_UDP_Socket_getSockName(lean_object* v_s_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_uv_udp_getsockname(v_s_755_);
return v___x_757_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_getSockName_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_755_ = stack[0].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Std_Async_UDP_Socket_getSockName(v_s_755_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getSockName___boxed(lean_object* v_s_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_Async_UDP_Socket_getSockName(v_s_759_);
lean_dec(v_s_759_);
return v_res_761_;
}
}
lean_object* l_Std_Async_UDP_Socket_getPeerName(lean_object* v_s_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_uv_udp_getpeername(v_s_762_);
return v___x_764_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_getPeerName_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_762_ = stack[0].m_obj;
lean_object* v_res_765_;
v_res_765_ = l_Std_Async_UDP_Socket_getPeerName(v_s_762_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_getPeerName___boxed(lean_object* v_s_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_Async_UDP_Socket_getPeerName(v_s_766_);
lean_dec(v_s_766_);
return v_res_768_;
}
}
lean_object* l_Std_Async_UDP_Socket_setBroadcast(lean_object* v_s_769_, uint8_t v_enable_770_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = lean_uv_udp_set_broadcast(v_s_769_, v_enable_770_);
return v___x_772_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_setBroadcast_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_769_ = stack[0].m_obj;
uint8_t v_enable_770_ = stack[1].m_num;
lean_object* v_res_773_;
v_res_773_ = l_Std_Async_UDP_Socket_setBroadcast(v_s_769_, v_enable_770_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setBroadcast___boxed(lean_object* v_s_774_, lean_object* v_enable_775_, lean_object* v_a_776_){
_start:
{
uint8_t v_enable_boxed_777_; lean_object* v_res_778_; 
v_enable_boxed_777_ = lean_unbox(v_enable_775_);
v_res_778_ = l_Std_Async_UDP_Socket_setBroadcast(v_s_774_, v_enable_boxed_777_);
lean_dec(v_s_774_);
return v_res_778_;
}
}
lean_object* l_Std_Async_UDP_Socket_setMulticastLoop(lean_object* v_s_779_, uint8_t v_enable_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_uv_udp_set_multicast_loop(v_s_779_, v_enable_780_);
return v___x_782_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_setMulticastLoop_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_779_ = stack[0].m_obj;
uint8_t v_enable_780_ = stack[1].m_num;
lean_object* v_res_783_;
v_res_783_ = l_Std_Async_UDP_Socket_setMulticastLoop(v_s_779_, v_enable_780_);
stack->m_obj
 = v_res_783_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastLoop___boxed(lean_object* v_s_784_, lean_object* v_enable_785_, lean_object* v_a_786_){
_start:
{
uint8_t v_enable_boxed_787_; lean_object* v_res_788_; 
v_enable_boxed_787_ = lean_unbox(v_enable_785_);
v_res_788_ = l_Std_Async_UDP_Socket_setMulticastLoop(v_s_784_, v_enable_boxed_787_);
lean_dec(v_s_784_);
return v_res_788_;
}
}
lean_object* l_Std_Async_UDP_Socket_setMulticastTTL(lean_object* v_s_789_, uint32_t v_ttl_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_uv_udp_set_multicast_ttl(v_s_789_, v_ttl_790_);
return v___x_792_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_setMulticastTTL_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_789_ = stack[0].m_obj;
uint32_t v_ttl_790_ = stack[1].m_num;
lean_object* v_res_793_;
v_res_793_ = l_Std_Async_UDP_Socket_setMulticastTTL(v_s_789_, v_ttl_790_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastTTL___boxed(lean_object* v_s_794_, lean_object* v_ttl_795_, lean_object* v_a_796_){
_start:
{
uint32_t v_ttl_boxed_797_; lean_object* v_res_798_; 
v_ttl_boxed_797_ = lean_unbox_uint32(v_ttl_795_);
lean_dec(v_ttl_795_);
v_res_798_ = l_Std_Async_UDP_Socket_setMulticastTTL(v_s_794_, v_ttl_boxed_797_);
lean_dec(v_s_794_);
return v_res_798_;
}
}
lean_object* l_Std_Async_UDP_Socket_setMembership(lean_object* v_s_799_, lean_object* v_multicastAddr_800_, lean_object* v_interfaceAddr_801_, uint8_t v_membership_802_){
_start:
{
if (v_membership_802_ == 0)
{
uint8_t v___x_804_; lean_object* v___x_805_; 
v___x_804_ = 0;
v___x_805_ = lean_uv_udp_set_membership(v_s_799_, v_multicastAddr_800_, v_interfaceAddr_801_, v___x_804_);
return v___x_805_;
}
else
{
uint8_t v___x_806_; lean_object* v___x_807_; 
v___x_806_ = 1;
v___x_807_ = lean_uv_udp_set_membership(v_s_799_, v_multicastAddr_800_, v_interfaceAddr_801_, v___x_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_setMembership_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_799_ = stack[0].m_obj;
lean_object* v_multicastAddr_800_ = stack[1].m_obj;
lean_object* v_interfaceAddr_801_ = stack[2].m_obj;
uint8_t v_membership_802_ = stack[3].m_num;
lean_object* v_res_808_;
v_res_808_ = l_Std_Async_UDP_Socket_setMembership(v_s_799_, v_multicastAddr_800_, v_interfaceAddr_801_, v_membership_802_);
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMembership___boxed(lean_object* v_s_809_, lean_object* v_multicastAddr_810_, lean_object* v_interfaceAddr_811_, lean_object* v_membership_812_, lean_object* v_a_813_){
_start:
{
uint8_t v_membership_boxed_814_; lean_object* v_res_815_; 
v_membership_boxed_814_ = lean_unbox(v_membership_812_);
v_res_815_ = l_Std_Async_UDP_Socket_setMembership(v_s_809_, v_multicastAddr_810_, v_interfaceAddr_811_, v_membership_boxed_814_);
lean_dec(v_interfaceAddr_811_);
lean_dec_ref(v_multicastAddr_810_);
lean_dec(v_s_809_);
return v_res_815_;
}
}
lean_object* l_Std_Async_UDP_Socket_setMulticastInterface(lean_object* v_s_816_, lean_object* v_interfaceAddr_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = lean_uv_udp_set_multicast_interface(v_s_816_, v_interfaceAddr_817_);
return v___x_819_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_setMulticastInterface_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_816_ = stack[0].m_obj;
lean_object* v_interfaceAddr_817_ = stack[1].m_obj;
lean_object* v_res_820_;
v_res_820_ = l_Std_Async_UDP_Socket_setMulticastInterface(v_s_816_, v_interfaceAddr_817_);
stack->m_obj
 = v_res_820_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setMulticastInterface___boxed(lean_object* v_s_821_, lean_object* v_interfaceAddr_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_Async_UDP_Socket_setMulticastInterface(v_s_821_, v_interfaceAddr_822_);
lean_dec_ref(v_interfaceAddr_822_);
lean_dec(v_s_821_);
return v_res_824_;
}
}
lean_object* l_Std_Async_UDP_Socket_setTTL(lean_object* v_s_825_, uint32_t v_ttl_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_uv_udp_set_ttl(v_s_825_, v_ttl_826_);
return v___x_828_;
}
}
LEAN_EXPORT void l_Std_Async_UDP_Socket_setTTL_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_825_ = stack[0].m_obj;
uint32_t v_ttl_826_ = stack[1].m_num;
lean_object* v_res_829_;
v_res_829_ = l_Std_Async_UDP_Socket_setTTL(v_s_825_, v_ttl_826_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l_Std_Async_UDP_Socket_setTTL___boxed(lean_object* v_s_830_, lean_object* v_ttl_831_, lean_object* v_a_832_){
_start:
{
uint32_t v_ttl_boxed_833_; lean_object* v_res_834_; 
v_ttl_boxed_833_ = lean_unbox_uint32(v_ttl_831_);
lean_dec(v_ttl_831_);
v_res_834_ = l_Std_Async_UDP_Socket_setTTL(v_s_830_, v_ttl_boxed_833_);
lean_dec(v_s_830_);
return v_res_834_;
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

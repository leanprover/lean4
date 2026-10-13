// Lean compiler output
// Module: Std.Async.TCP
// Imports: public import Std.Time public import Std.Internal.UV.TCP public import Std.Async.Select
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_new();
lean_object* lean_uv_tcp_try_accept(lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t lean_bool_to_int8(uint8_t);
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t);
lean_object* lean_uv_tcp_getsockname(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_uv_tcp_wait_readable(lean_object*);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_uv_tcp_cancel_accept(lean_object*);
lean_object* lean_uv_tcp_shutdown(lean_object*);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
lean_object* lean_uv_tcp_wait_acceptable(lean_object*);
lean_object* lean_uv_tcp_cancel_recv(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_string_object l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "keep-alive delay of "};
static const lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__0 = (const lean_object*)&l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__0_value;
static const lean_string_object l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " s is too large"};
static const lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__1 = (const lean_object*)&l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_mk();
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_listen(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_listen___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Server_accept___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Server_accept___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_TCP_Socket_Server_accept___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__0_value;
static const lean_string_object l_Std_Async_TCP_Socket_Server_accept___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Async_TCP_Socket_Server_accept___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__1_value;
static const lean_closure_object l_Std_Async_TCP_Socket_Server_accept___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Server_accept___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__1_value)} };
static const lean_object* l_Std_Async_TCP_Socket_Server_accept___closed__2 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__2_value;
static const lean_closure_object l_Std_Async_TCP_Socket_Server_accept___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Server_accept___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__2_value)} };
static const lean_object* l_Std_Async_TCP_Socket_Server_accept___closed__3 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__3_value;
static const lean_closure_object l_Std_Async_TCP_Socket_Server_accept___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__0_value)} };
static const lean_object* l_Std_Async_TCP_Socket_Server_accept___closed__4 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Server_tryAccept___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_io_error_to_string, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_TCP_Socket_Server_tryAccept___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_tryAccept___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_tryAccept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_tryAccept___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "the pending connection was accepted concurrently"};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__0_value;
static const lean_ctor_object l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__0_value)}};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__1 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__1_value;
static const lean_ctor_object l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__1_value)}};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__2 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value;
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value;
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value;
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value;
static const lean_array_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5_value;
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value;
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9_value;
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13;
static const lean_string_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_0),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_1),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_2),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9_value),((lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5_value)}};
static const lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16 = (const lean_object*)&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16_value;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25;
static lean_once_cell_t l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___auto__1;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk();
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Client_connect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__1_value)} };
static const lean_object* l_Std_Async_TCP_Socket_Client_connect___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_connect___closed__0_value;
static const lean_closure_object l_Std_Async_TCP_Socket_Client_connect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Client_connect___closed__0_value)} };
static const lean_object* l_Std_Async_TCP_Socket_Client_connect___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_connect___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Server_accept___closed__1_value)} };
static const lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0_value;
static const lean_closure_object l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0_value)} };
static const lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "the promise linked to the Async Task was dropped"};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0_value;
static const lean_closure_object l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0_value)} };
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__1 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__0_value)}};
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0_value;
static const lean_ctor_object l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0_value)}};
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_TCP_Socket_Client_recvSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___closed__0 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___closed__0_value;
static const lean_closure_object l_Std_Async_TCP_Socket_Client_recvSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___closed__1 = (const lean_object*)&l_Std_Async_TCP_Socket_Client_recvSelector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___auto__1;
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(lean_object* v_delay_3_){
_start:
{
lean_object* v_seconds_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_seconds_5_ = l_Int_toNat(v_delay_3_);
v___x_6_ = lean_cstr_to_nat("4294967296");
v___x_7_ = lean_nat_dec_lt(v_seconds_5_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_8_ = ((lean_object*)(l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__0));
v___x_9_ = l_Nat_reprFast(v_seconds_5_);
v___x_10_ = lean_string_append(v___x_8_, v___x_9_);
lean_dec_ref(v___x_9_);
v___x_11_ = ((lean_object*)(l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___closed__1));
v___x_12_ = lean_string_append(v___x_10_, v___x_11_);
v___x_13_ = lean_mk_io_user_error(v___x_12_);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
else
{
uint32_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_uint32_of_nat(v_seconds_5_);
lean_dec(v_seconds_5_);
v___x_16_ = lean_box_uint32(v___x_15_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___boxed(lean_object* v_delay_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_18_);
lean_dec(v_delay_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_mk(){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_22_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_22_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_mk___boxed(lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Async_TCP_Socket_Server_mk();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_bind(lean_object* v_s_41_, lean_object* v_addr_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_uv_tcp_bind(v_s_41_, v_addr_42_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_bind___boxed(lean_object* v_s_45_, lean_object* v_addr_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Async_TCP_Socket_Server_bind(v_s_45_, v_addr_46_);
lean_dec_ref(v_addr_46_);
lean_dec(v_s_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_listen(lean_object* v_s_49_, uint32_t v_backlog_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_uv_tcp_listen(v_s_49_, v_backlog_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_listen___boxed(lean_object* v_s_53_, lean_object* v_backlog_54_, lean_object* v_a_55_){
_start:
{
uint32_t v_backlog_boxed_56_; lean_object* v_res_57_; 
v_backlog_boxed_56_ = lean_unbox_uint32(v_backlog_54_);
lean_dec(v_backlog_54_);
v_res_57_ = l_Std_Async_TCP_Socket_Server_listen(v_s_53_, v_backlog_boxed_56_);
lean_dec(v_s_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0(lean_object* v_native_58_){
_start:
{
lean_inc(v_native_58_);
return v_native_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0___boxed(lean_object* v_native_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Async_TCP_Socket_Server_accept___lam__0(v_native_59_);
lean_dec(v_native_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1(lean_object* v___x_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_mk_io_user_error(v___x_61_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
else
{
lean_object* v_val_65_; 
lean_dec_ref(v___x_61_);
v_val_65_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_val_65_);
return v_val_65_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1___boxed(lean_object* v___x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Async_TCP_Socket_Server_accept___lam__1(v___x_66_, v_x_67_);
lean_dec(v_x_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2(lean_object* v___f_69_, lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_70_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v___f_69_);
v_a_72_ = lean_ctor_get(v_x_70_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_70_);
if (v_isSharedCheck_80_ == 0)
{
v___x_74_ = v_x_70_;
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v_x_70_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_79_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
else
{
lean_object* v_a_81_; 
v_a_81_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v_x_70_, 1);
if (lean_obj_tag(v_a_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
lean_dec_ref(v___f_69_);
v_a_82_ = lean_ctor_get(v_a_81_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_81_);
if (v_isSharedCheck_90_ == 0)
{
v___x_84_ = v_a_81_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v_a_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_89_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; 
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
}
else
{
lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_a_91_ = lean_ctor_get(v_a_81_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v_a_81_, 1);
v___x_92_ = lean_io_promise_result_opt(v_a_91_);
lean_dec(v_a_91_);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = 0;
v___x_95_ = lean_task_map(v___f_69_, v___x_92_, v___x_93_, v___x_94_);
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2___boxed(lean_object* v___f_97_, lean_object* v_x_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Async_TCP_Socket_Server_accept___lam__2(v___f_97_, v_x_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept(lean_object* v_s_109_){
_start:
{
lean_object* v___y_112_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v_val_119_; lean_object* v___x_149_; 
v___f_114_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_accept___closed__3));
v___x_115_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_accept___closed__4));
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = 0;
v___x_149_ = lean_uv_tcp_accept(v_s_109_);
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
v_val_119_ = v___x_155_;
goto v___jp_118_;
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
v_val_119_ = v___x_163_;
goto v___jp_118_;
}
}
}
v___jp_111_:
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___y_112_);
return v___x_113_;
}
v___jp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v_val_119_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
v___x_122_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_116_, v___x_117_, v___x_121_, v___f_114_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
if (lean_obj_tag(v_a_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_124_ = lean_ctor_get(v_a_123_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_a_123_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v_a_123_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v_a_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
v___y_112_ = v___x_129_;
goto v___jp_111_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v_a_123_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v_a_123_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v_a_123_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v_a_123_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
v___y_112_ = v___x_137_;
goto v___jp_111_;
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v_a_140_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_148_ == 0)
{
v___x_142_ = v___x_122_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_122_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_task_map(v___x_115_, v_a_140_, v___x_116_, v___x_117_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_144_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___boxed(lean_object* v_s_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Async_TCP_Socket_Server_accept(v_s_166_);
lean_dec(v_s_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_tryAccept(lean_object* v_s_170_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_tryAccept___closed__0));
v___x_173_ = lean_uv_tcp_try_accept(v_s_170_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = l_IO_ofExcept___redArg(v___x_172_, v_a_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_195_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_195_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_195_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_195_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
if (lean_obj_tag(v_a_176_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
else
{
lean_object* v_val_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_194_; 
v_val_184_ = lean_ctor_get(v_a_176_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_194_ == 0)
{
v___x_186_ = v_a_176_;
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_val_184_);
lean_dec(v_a_176_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_val_184_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_189_);
v___x_191_ = v___x_178_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_175_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_175_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_a_204_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_173_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_173_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_tryAccept___boxed(lean_object* v_s_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Async_TCP_Socket_Server_tryAccept(v_s_212_);
lean_dec(v_s_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(lean_object* v_e_215_){
_start:
{
if (lean_obj_tag(v_e_215_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_226_; 
v_a_217_ = lean_ctor_get(v_e_215_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_e_215_);
if (v_isSharedCheck_226_ == 0)
{
v___x_219_ = v_e_215_;
v_isShared_220_ = v_isSharedCheck_226_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v_e_215_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_226_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = lean_io_error_to_string(v_a_217_);
v___x_222_ = lean_mk_io_user_error(v___x_221_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
lean_ctor_set(v___x_219_, 0, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_a_227_ = lean_ctor_get(v_e_215_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_e_215_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v_e_215_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v_e_215_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 0);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg___boxed(lean_object* v_e_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_e_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(lean_object* v_00_u03b1_238_, lean_object* v_e_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_e_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___boxed(lean_object* v_00_u03b1_242_, lean_object* v_e_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(v_00_u03b1_242_, v_e_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(lean_object* v_val_251_, lean_object* v_s_252_, lean_object* v_w_253_, lean_object* v_lose_254_){
_start:
{
lean_object* v_finished_256_; lean_object* v_promise_257_; lean_object* v_a_259_; lean_object* v___x_263_; uint8_t v___y_265_; uint8_t v___x_299_; 
v_finished_256_ = lean_ctor_get(v_w_253_, 0);
v_promise_257_ = lean_ctor_get(v_w_253_, 1);
v___x_263_ = lean_st_ref_take(v_finished_256_);
v___x_299_ = lean_unbox(v___x_263_);
lean_dec(v___x_263_);
if (v___x_299_ == 0)
{
uint8_t v___x_300_; 
v___x_300_ = 1;
v___y_265_ = v___x_300_;
goto v___jp_264_;
}
else
{
uint8_t v___x_301_; 
v___x_301_ = 0;
v___y_265_ = v___x_301_;
goto v___jp_264_;
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v_a_259_);
v___x_261_ = lean_io_promise_resolve(v___x_260_, v_promise_257_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
v___jp_264_:
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = 1;
v___x_267_ = lean_box(v___x_266_);
v___x_268_ = lean_st_ref_put(v_finished_256_, v___x_267_);
if (v___y_265_ == 0)
{
lean_object* v___x_269_; 
lean_dec_ref(v_val_251_);
v___x_269_ = lean_apply_1(v_lose_254_, lean_box(0));
return v___x_269_;
}
else
{
lean_object* v___x_270_; 
lean_dec_ref(v_lose_254_);
v___x_270_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_251_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_271_; 
lean_dec_ref_known(v___x_270_, 1);
v___x_271_ = lean_uv_tcp_try_accept(v_s_252_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_a_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_295_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_295_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_295_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_295_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
if (lean_obj_tag(v_a_274_) == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_278_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__2));
v___x_279_ = lean_io_promise_resolve(v___x_278_, v_promise_257_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_279_);
v___x_281_ = v___x_276_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
else
{
lean_object* v_val_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_294_; 
v_val_283_ = lean_ctor_get(v_a_274_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_a_274_);
if (v_isSharedCheck_294_ == 0)
{
v___x_285_ = v_a_274_;
v_isShared_286_ = v_isSharedCheck_294_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_val_283_);
lean_dec(v_a_274_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_294_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_val_283_);
v___x_288_ = v_reuseFailAlloc_293_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_io_promise_resolve(v___x_288_, v_promise_257_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_289_);
v___x_291_ = v___x_276_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
else
{
lean_object* v_a_296_; 
v_a_296_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v___x_273_, 1);
v_a_259_ = v_a_296_;
goto v___jp_258_;
}
}
else
{
lean_object* v_a_297_; 
v_a_297_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_271_, 1);
v_a_259_ = v_a_297_;
goto v___jp_258_;
}
}
else
{
lean_object* v_a_298_; 
v_a_298_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_270_, 1);
v_a_259_ = v_a_298_;
goto v___jp_258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(lean_object* v_val_302_, lean_object* v_s_303_, lean_object* v_w_304_, lean_object* v_lose_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(v_val_302_, v_s_303_, v_w_304_, v_lose_305_);
lean_dec_ref(v_w_304_);
lean_dec(v_s_303_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(lean_object* v_s_308_){
_start:
{
lean_object* v_val_311_; lean_object* v_a_314_; lean_object* v_a_317_; lean_object* v___x_319_; 
v___x_319_ = lean_uv_tcp_try_accept(v_s_308_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_321_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
v___x_321_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_a_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
if (lean_obj_tag(v_a_322_) == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
v_a_314_ = v___x_323_;
goto v___jp_313_;
}
else
{
lean_object* v_val_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_val_324_ = lean_ctor_get(v_a_322_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_322_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v_a_322_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_val_324_);
lean_dec(v_a_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_val_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v_a_314_ = v___x_329_;
goto v___jp_313_;
}
}
}
}
else
{
lean_object* v_a_332_; 
v_a_332_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_321_, 1);
v_a_317_ = v_a_332_;
goto v___jp_316_;
}
}
else
{
lean_object* v_a_333_; 
v_a_333_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_319_, 1);
v_a_317_ = v_a_333_;
goto v___jp_316_;
}
v___jp_310_:
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v_val_311_);
return v___x_312_;
}
v___jp_313_:
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v_a_314_);
v_val_311_ = v___x_315_;
goto v___jp_310_;
}
v___jp_316_:
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v_a_317_);
v_val_311_ = v___x_318_;
goto v___jp_310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(lean_object* v_s_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(v_s_334_);
lean_dec(v_s_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(lean_object* v___x_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(lean_object* v___x_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(v___x_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(lean_object* v_s_345_, lean_object* v_waiter_346_, lean_object* v_x_347_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
else
{
lean_object* v_val_351_; lean_object* v___f_352_; lean_object* v___x_353_; 
v_val_351_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v_x_347_, 1);
v___f_352_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0));
v___x_353_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(v_val_351_, v_s_345_, v_waiter_346_, v___f_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(lean_object* v_s_354_, lean_object* v_waiter_355_, lean_object* v_x_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(v_s_354_, v_waiter_355_, v_x_356_);
lean_dec_ref(v_waiter_355_);
lean_dec(v_s_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(lean_object* v___f_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_val_363_; 
if (lean_obj_tag(v_x_360_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v___f_359_);
v_a_365_ = lean_ctor_get(v_x_360_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v_x_360_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v_x_360_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_372_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_390_; 
v_a_374_ = lean_ctor_get(v_x_360_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_390_ == 0)
{
v___x_376_ = v_x_360_;
v_isShared_377_ = v_isSharedCheck_390_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v_x_360_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_390_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; 
v___x_378_ = lean_io_promise_result_opt(v_a_374_);
lean_dec(v_a_374_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_380_ = 0;
v___x_381_ = l_EIO_chainTask___redArg(v___x_378_, v___f_359_, v___x_379_, v___x_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_a_382_);
v___x_384_ = v___x_376_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
v_val_363_ = v___x_384_;
goto v___jp_362_;
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; 
v_a_386_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_381_, 1);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 0);
lean_ctor_set(v___x_376_, 0, v_a_386_);
v___x_388_ = v___x_376_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v_val_363_ = v___x_388_;
goto v___jp_362_;
}
}
}
}
v___jp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_val_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed(lean_object* v___f_391_, lean_object* v_x_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(v___f_391_, v_x_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(lean_object* v_s_395_, lean_object* v_waiter_396_){
_start:
{
lean_object* v___f_398_; lean_object* v___f_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v_val_403_; lean_object* v___x_406_; 
lean_inc(v_s_395_);
v___f_398_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_398_, 0, v_s_395_);
lean_closure_set(v___f_398_, 1, v_waiter_396_);
v___f_399_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_399_, 0, v___f_398_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = 0;
v___x_406_ = lean_uv_tcp_wait_acceptable(v_s_395_);
lean_dec(v_s_395_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 1);
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
v_val_403_ = v___x_412_;
goto v___jp_402_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_406_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_406_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set_tag(v___x_417_, 0);
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v_val_403_ = v___x_420_;
goto v___jp_402_;
}
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v_val_403_);
v___x_405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_400_, v___x_401_, v___x_404_, v___f_399_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed(lean_object* v_s_423_, lean_object* v_waiter_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(v_s_423_, v_waiter_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(lean_object* v_s_427_){
_start:
{
lean_object* v_val_430_; lean_object* v___x_432_; 
v___x_432_ = lean_uv_tcp_cancel_accept(v_s_427_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set_tag(v___x_435_, 1);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_433_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
v_val_430_ = v___x_438_;
goto v___jp_429_;
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_432_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_432_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 0);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
v_val_430_ = v___x_446_;
goto v___jp_429_;
}
}
}
v___jp_429_:
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_val_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed(lean_object* v_s_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(v_s_449_);
lean_dec(v_s_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector(lean_object* v_s_452_){
_start:
{
lean_object* v___f_453_; lean_object* v___f_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
lean_inc_n(v_s_452_, 2);
v___f_453_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed), 2, 1);
lean_closure_set(v___f_453_, 0, v_s_452_);
v___f_454_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_454_, 0, v_s_452_);
v___f_455_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed), 2, 1);
lean_closure_set(v___f_455_, 0, v_s_452_);
v___x_456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_456_, 0, v___f_453_);
lean_ctor_set(v___x_456_, 1, v___f_454_);
lean_ctor_set(v___x_456_, 2, v___f_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName(lean_object* v_s_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_uv_tcp_getsockname(v_s_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName___boxed(lean_object* v_s_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_Async_TCP_Socket_Server_getSockName(v_s_460_);
lean_dec(v_s_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay(lean_object* v_s_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_uv_tcp_nodelay(v_s_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay___boxed(lean_object* v_s_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Async_TCP_Socket_Server_noDelay(v_s_466_);
lean_dec(v_s_466_);
return v_res_468_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10));
v___x_496_ = l_Lean_mkAtom(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12);
v___x_498_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_499_ = lean_array_push(v___x_498_, v___x_497_);
return v___x_499_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16));
v___x_511_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_512_ = lean_array_push(v___x_511_, v___x_510_);
return v___x_512_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17);
v___x_514_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15));
v___x_515_ = lean_box(2);
v___x_516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_513_);
return v___x_516_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18);
v___x_518_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13);
v___x_519_ = lean_array_push(v___x_518_, v___x_517_);
return v___x_519_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19);
v___x_521_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11));
v___x_522_ = lean_box(2);
v___x_523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_521_);
lean_ctor_set(v___x_523_, 2, v___x_520_);
return v___x_523_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20);
v___x_525_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_526_ = lean_array_push(v___x_525_, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_527_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21);
v___x_528_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9));
v___x_529_ = lean_box(2);
v___x_530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
lean_ctor_set(v___x_530_, 2, v___x_527_);
return v___x_530_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22);
v___x_532_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_533_ = lean_array_push(v___x_532_, v___x_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23);
v___x_535_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7));
v___x_536_ = lean_box(2);
v___x_537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_534_);
return v___x_537_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24);
v___x_539_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_540_ = lean_array_push(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25);
v___x_542_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4));
v___x_543_ = lean_box(2);
v___x_544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_542_);
lean_ctor_set(v___x_544_, 2, v___x_541_);
return v___x_544_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg(lean_object* v_s_546_, uint8_t v_enable_547_, lean_object* v_delay_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_548_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; uint8_t v___x_552_; uint32_t v___x_553_; lean_object* v___x_554_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = lean_bool_to_int8(v_enable_547_);
v___x_553_ = lean_unbox_uint32(v_a_551_);
lean_dec(v_a_551_);
v___x_554_ = lean_uv_tcp_keepalive(v_s_546_, v___x_552_, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_550_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_550_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object* v_s_563_, lean_object* v_enable_564_, lean_object* v_delay_565_, lean_object* v_a_566_){
_start:
{
uint8_t v_enable_boxed_567_; lean_object* v_res_568_; 
v_enable_boxed_567_ = lean_unbox(v_enable_564_);
v_res_568_ = l_Std_Async_TCP_Socket_Server_keepAlive___redArg(v_s_563_, v_enable_boxed_567_, v_delay_565_);
lean_dec(v_delay_565_);
lean_dec(v_s_563_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive(lean_object* v_s_569_, uint8_t v_enable_570_, lean_object* v_delay_571_, lean_object* v_x_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_571_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; uint8_t v___x_576_; uint32_t v___x_577_; lean_object* v___x_578_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_bool_to_int8(v_enable_570_);
v___x_577_ = lean_unbox_uint32(v_a_575_);
lean_dec(v_a_575_);
v___x_578_ = lean_uv_tcp_keepalive(v_s_569_, v___x_576_, v___x_577_);
return v___x_578_;
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_a_579_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_574_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_574_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___boxed(lean_object* v_s_587_, lean_object* v_enable_588_, lean_object* v_delay_589_, lean_object* v_x_590_, lean_object* v_a_591_){
_start:
{
uint8_t v_enable_boxed_592_; lean_object* v_res_593_; 
v_enable_boxed_592_ = lean_unbox(v_enable_588_);
v_res_593_ = l_Std_Async_TCP_Socket_Server_keepAlive(v_s_587_, v_enable_boxed_592_, v_delay_589_, v_x_590_);
lean_dec(v_delay_589_);
lean_dec(v_s_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk(){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_a_604_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_595_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_595_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
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
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk___boxed(lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Async_TCP_Socket_Client_mk();
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind(lean_object* v_s_614_, lean_object* v_addr_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = lean_uv_tcp_bind(v_s_614_, v_addr_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind___boxed(lean_object* v_s_618_, lean_object* v_addr_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Async_TCP_Socket_Client_bind(v_s_618_, v_addr_619_);
lean_dec_ref(v_addr_619_);
lean_dec(v_s_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0(lean_object* v___x_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_mk_io_user_error(v___x_622_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v_val_626_; 
lean_dec_ref(v___x_622_);
v_val_626_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_val_626_);
return v_val_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed(lean_object* v___x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_Async_TCP_Socket_Client_connect___lam__0(v___x_627_, v_x_628_);
lean_dec(v_x_628_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1(lean_object* v___f_630_, lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref(v___f_630_);
v_a_633_ = lean_ctor_get(v_x_631_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_641_ == 0)
{
v___x_635_ = v_x_631_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v_x_631_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_640_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; 
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
}
else
{
lean_object* v_a_642_; 
v_a_642_ = lean_ctor_get(v_x_631_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v_x_631_, 1);
if (lean_obj_tag(v_a_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v___f_630_);
v_a_643_ = lean_ctor_get(v_a_642_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_642_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v_a_642_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v_a_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_650_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_652_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v_a_642_, 1);
v___x_653_ = lean_io_promise_result_opt(v_a_652_);
lean_dec(v_a_652_);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = 0;
v___x_656_ = lean_task_map(v___f_630_, v___x_653_, v___x_654_, v___x_655_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed(lean_object* v___f_658_, lean_object* v_x_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_Async_TCP_Socket_Client_connect___lam__1(v___f_658_, v_x_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect(lean_object* v_s_666_, lean_object* v_addr_667_){
_start:
{
lean_object* v___f_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v_val_673_; lean_object* v___x_677_; 
v___f_669_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = 0;
v___x_677_ = lean_uv_tcp_connect(v_s_666_, v_addr_667_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set_tag(v___x_680_, 1);
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
v_val_673_ = v___x_683_;
goto v___jp_672_;
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_686_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_677_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_677_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 0);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_val_673_ = v___x_691_;
goto v___jp_672_;
}
}
}
v___jp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_val_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
v___x_676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_670_, v___x_671_, v___x_675_, v___f_669_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___boxed(lean_object* v_s_694_, lean_object* v_addr_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_Async_TCP_Socket_Client_connect(v_s_694_, v_addr_695_);
lean_dec_ref(v_addr_695_);
lean_dec(v_s_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll(lean_object* v_s_698_, lean_object* v_data_699_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v_val_705_; lean_object* v___x_709_; 
v___f_701_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = 0;
v___x_709_ = lean_uv_tcp_send(v_s_698_, v_data_699_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 1);
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
v_val_705_ = v___x_715_;
goto v___jp_704_;
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_709_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_709_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 0);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v_val_705_ = v___x_723_;
goto v___jp_704_;
}
}
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_val_705_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
v___x_708_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_702_, v___x_703_, v___x_707_, v___f_701_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll___boxed(lean_object* v_s_726_, lean_object* v_data_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_Async_TCP_Socket_Client_sendAll(v_s_726_, v_data_727_);
lean_dec(v_s_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send(lean_object* v_s_730_, lean_object* v_data_731_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___f_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v_val_740_; lean_object* v___x_744_; 
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_mk_empty_array_with_capacity(v___x_733_);
v___x_735_ = lean_array_push(v___x_734_, v_data_731_);
v___f_736_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = 0;
v___x_744_ = lean_uv_tcp_send(v_s_730_, v___x_735_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 1);
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
v_val_740_ = v___x_750_;
goto v___jp_739_;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_753_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_744_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_744_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 0);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
v_val_740_ = v___x_758_;
goto v___jp_739_;
}
}
}
v___jp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_val_740_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
v___x_743_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_737_, v___x_738_, v___x_742_, v___f_736_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send___boxed(lean_object* v_s_761_, lean_object* v_data_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Std_Async_TCP_Socket_Client_send(v_s_761_, v_data_762_);
lean_dec(v_s_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object* v___x_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_mk_io_user_error(v___x_765_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
else
{
lean_object* v_val_769_; 
lean_dec_ref(v___x_765_);
v_val_769_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_val_769_);
return v_val_769_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(lean_object* v___x_770_, lean_object* v_x_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(v___x_770_, v_x_771_);
lean_dec(v_x_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(lean_object* v___f_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___f_773_);
v_a_776_ = lean_ctor_get(v_x_774_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_784_ == 0)
{
v___x_778_ = v_x_774_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v_x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
else
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v_x_774_, 1);
if (lean_obj_tag(v_a_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v___f_773_);
v_a_786_ = lean_ctor_get(v_a_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_788_ = v_a_785_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v_a_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_a_795_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v_a_785_, 1);
v___x_796_ = lean_io_promise_result_opt(v_a_795_);
lean_dec(v_a_795_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = 0;
v___x_799_ = lean_task_map(v___f_773_, v___x_796_, v___x_797_, v___x_798_);
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(lean_object* v___f_801_, lean_object* v_x_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(v___f_801_, v_x_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f(lean_object* v_s_809_, uint64_t v_size_810_){
_start:
{
lean_object* v___f_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v_val_816_; lean_object* v___x_820_; 
v___f_812_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1));
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = 0;
v___x_820_ = lean_uv_tcp_recv(v_s_809_, v_size_810_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 1);
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v_val_816_ = v___x_826_;
goto v___jp_815_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_820_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_820_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v_val_816_ = v___x_834_;
goto v___jp_815_;
}
}
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v_val_816_);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_813_, v___x_814_, v___x_818_, v___f_812_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object* v_s_837_, lean_object* v_size_838_, lean_object* v_a_839_){
_start:
{
uint64_t v_size_boxed_840_; lean_object* v_res_841_; 
v_size_boxed_840_ = lean_unbox_uint64(v_size_838_);
lean_dec_ref(v_size_838_);
v_res_841_ = l_Std_Async_TCP_Socket_Client_recv_x3f(v_s_837_, v_size_boxed_840_);
lean_dec(v_s_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object* v_promise_842_, lean_object* v_value_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = lean_io_promise_resolve(v_value_843_, v_promise_842_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0___boxed(lean_object* v_promise_846_, lean_object* v_value_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(v_promise_846_, v_value_847_);
lean_dec(v_promise_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object* v_val_853_, lean_object* v___x_854_, uint64_t v_size_855_, lean_object* v_w_856_, lean_object* v_lose_857_){
_start:
{
lean_object* v_finished_859_; lean_object* v_promise_860_; lean_object* v_a_862_; lean_object* v___f_866_; lean_object* v___x_867_; uint8_t v___y_869_; uint8_t v___x_893_; 
v_finished_859_ = lean_ctor_get(v_w_856_, 0);
lean_inc(v_finished_859_);
v_promise_860_ = lean_ctor_get(v_w_856_, 1);
lean_inc_n(v_promise_860_, 2);
lean_dec_ref(v_w_856_);
v___f_866_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_866_, 0, v_promise_860_);
v___x_867_ = lean_st_ref_take(v_finished_859_);
v___x_893_ = lean_unbox(v___x_867_);
lean_dec(v___x_867_);
if (v___x_893_ == 0)
{
uint8_t v___x_894_; 
v___x_894_ = 1;
v___y_869_ = v___x_894_;
goto v___jp_868_;
}
else
{
uint8_t v___x_895_; 
v___x_895_ = 0;
v___y_869_ = v___x_895_;
goto v___jp_868_;
}
v___jp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_a_862_);
v___x_864_ = lean_io_promise_resolve(v___x_863_, v_promise_860_);
lean_dec(v_promise_860_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
v___jp_868_:
{
uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = 1;
v___x_871_ = lean_box(v___x_870_);
v___x_872_ = lean_st_ref_put(v_finished_859_, v___x_871_);
lean_dec(v_finished_859_);
if (v___y_869_ == 0)
{
lean_object* v___x_873_; 
lean_dec_ref(v___f_866_);
lean_dec(v_promise_860_);
lean_dec_ref(v_val_853_);
v___x_873_ = lean_apply_1(v_lose_857_, lean_box(0));
return v___x_873_;
}
else
{
lean_object* v___x_874_; 
lean_dec_ref(v_lose_857_);
v___x_874_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_853_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_875_; 
lean_dec_ref_known(v___x_874_, 1);
v___x_875_ = lean_uv_tcp_recv(v___x_854_, v_size_855_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_promise_860_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_890_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___f_880_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__1));
v___x_881_ = lean_io_promise_result_opt(v_a_876_);
lean_dec(v_a_876_);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = 0;
v___x_884_ = lean_task_map(v___f_880_, v___x_881_, v___x_882_, v___x_883_);
v___x_885_ = lean_box(0);
v___x_886_ = lean_io_map_task(v___f_866_, v___x_884_, v___x_882_, v___x_883_);
lean_dec_ref(v___x_886_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_885_);
v___x_888_ = v___x_878_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_885_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_891_; 
lean_dec_ref(v___f_866_);
v_a_891_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_875_, 1);
v_a_862_ = v_a_891_;
goto v___jp_861_;
}
}
else
{
lean_object* v_a_892_; 
lean_dec_ref(v___f_866_);
v_a_892_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_874_, 1);
v_a_862_ = v_a_892_;
goto v___jp_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object* v_val_896_, lean_object* v___x_897_, lean_object* v_size_898_, lean_object* v_w_899_, lean_object* v_lose_900_, lean_object* v___y_901_){
_start:
{
uint64_t v_size_boxed_902_; lean_object* v_res_903_; 
v_size_boxed_902_ = lean_unbox_uint64(v_size_898_);
lean_dec_ref(v_size_898_);
v_res_903_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_896_, v___x_897_, v_size_boxed_902_, v_w_899_, v_lose_900_);
lean_dec(v___x_897_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object* v_x_904_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_914_; 
v_a_906_ = lean_ctor_get(v_x_904_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_914_ == 0)
{
v___x_908_ = v_x_904_;
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v_x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_913_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_924_; 
v_a_915_ = lean_ctor_get(v_x_904_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_924_ == 0)
{
v___x_917_ = v_x_904_;
v_isShared_918_ = v_isSharedCheck_924_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v_x_904_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_924_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_923_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object* v_x_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(v_x_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object* v_x_932_){
_start:
{
if (lean_obj_tag(v_x_932_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_942_; 
v_a_934_ = lean_ctor_get(v_x_932_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v_x_932_);
if (v_isSharedCheck_942_ == 0)
{
v___x_936_ = v_x_932_;
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v_x_932_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_941_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec_ref_known(v_x_932_, 1);
v___x_943_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__1));
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object* v_x_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(v_x_944_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object* v_s_947_){
_start:
{
lean_object* v_val_950_; lean_object* v___x_952_; 
v___x_952_ = lean_uv_tcp_cancel_recv(v_s_947_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 1);
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
v_val_950_ = v___x_958_;
goto v___jp_949_;
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_952_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_952_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 0);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
v_val_950_ = v___x_966_;
goto v___jp_949_;
}
}
}
v___jp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_val_950_);
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object* v_s_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(v_s_969_);
lean_dec(v_s_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object* v_s_972_, uint64_t v_size_973_, lean_object* v_waiter_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_a_978_; 
if (lean_obj_tag(v_a_975_) == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v_waiter_974_);
v___x_980_ = lean_box(0);
v_a_978_ = v___x_980_;
goto v___jp_977_;
}
else
{
lean_object* v_val_981_; lean_object* v___f_982_; lean_object* v___x_983_; 
v_val_981_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_val_981_);
lean_dec_ref_known(v_a_975_, 1);
v___f_982_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0));
v___x_983_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_981_, v_s_972_, v_size_973_, v_waiter_974_, v___f_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v_a_978_ = v_a_984_;
goto v___jp_977_;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
v_a_985_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
v___jp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v_a_978_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object* v_s_993_, lean_object* v_size_994_, lean_object* v_waiter_995_, lean_object* v_a_996_, lean_object* v___y_997_){
_start:
{
uint64_t v_size_boxed_998_; lean_object* v_res_999_; 
v_size_boxed_998_ = lean_unbox_uint64(v_size_994_);
lean_dec_ref(v_size_994_);
v_res_999_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(v_s_993_, v_size_boxed_998_, v_waiter_995_, v_a_996_);
lean_dec(v_s_993_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object* v___f_1004_, lean_object* v_x_1005_){
_start:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v___f_1004_);
v_a_1007_ = lean_ctor_get(v_x_1005_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_x_1005_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1009_ = v_x_1005_;
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v_x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1015_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1016_ = lean_ctor_get(v_x_1005_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v_x_1005_, 1);
v___x_1017_ = lean_io_promise_result_opt(v_a_1016_);
lean_dec(v_a_1016_);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = 0;
v___x_1020_ = lean_io_map_task(v___f_1004_, v___x_1017_, v___x_1018_, v___x_1019_);
lean_dec_ref(v___x_1020_);
v___x_1021_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1));
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object* v___f_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(v___f_1022_, v_x_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object* v_s_1026_, uint64_t v_size_1027_, lean_object* v_waiter_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v_val_1036_; lean_object* v___x_1039_; 
v___x_1030_ = lean_box_uint64(v_size_1027_);
lean_inc(v_s_1026_);
v___f_1031_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1031_, 0, v_s_1026_);
lean_closure_set(v___f_1031_, 1, v___x_1030_);
lean_closure_set(v___f_1031_, 2, v_waiter_1028_);
v___f_1032_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1032_, 0, v___f_1031_);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = 0;
v___x_1039_ = lean_uv_tcp_wait_readable(v_s_1026_);
lean_dec(v_s_1026_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 1);
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
v_val_1036_ = v___x_1045_;
goto v___jp_1035_;
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v_a_1048_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1039_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1039_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
lean_ctor_set_tag(v___x_1050_, 0);
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
v_val_1036_ = v___x_1053_;
goto v___jp_1035_;
}
}
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_val_1036_);
v___x_1038_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1033_, v___x_1034_, v___x_1037_, v___f_1032_);
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object* v_s_1056_, lean_object* v_size_1057_, lean_object* v_waiter_1058_, lean_object* v___y_1059_){
_start:
{
uint64_t v_size_boxed_1060_; lean_object* v_res_1061_; 
v_size_boxed_1060_ = lean_unbox_uint64(v_size_1057_);
lean_dec_ref(v_size_1057_);
v_res_1061_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(v_s_1056_, v_size_boxed_1060_, v_waiter_1058_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object* v___f_1062_, lean_object* v___x_1063_, uint8_t v___x_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v___x_1063_);
lean_dec_ref(v___f_1062_);
v_a_1067_ = lean_ctor_get(v_x_1065_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_x_1065_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1069_ = v_x_1065_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v_x_1065_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1076_; 
v_a_1076_ = lean_ctor_get(v_x_1065_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v_x_1065_, 1);
if (lean_obj_tag(v_a_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v___x_1063_);
lean_dec_ref(v___f_1062_);
v_a_1077_ = lean_ctor_get(v_a_1076_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_a_1076_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1079_ = v_a_1076_;
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v_a_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1085_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1086_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1087_ = lean_io_promise_result_opt(v_a_1086_);
lean_dec(v_a_1086_);
v___x_1088_ = lean_task_map(v___f_1062_, v___x_1087_, v___x_1063_, v___x_1064_);
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object* v___f_1090_, lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v___x_2890__boxed_1095_; lean_object* v_res_1096_; 
v___x_2890__boxed_1095_ = lean_unbox(v___x_1092_);
v_res_1096_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(v___f_1090_, v___x_1091_, v___x_2890__boxed_1095_, v_x_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object* v___f_1102_, lean_object* v_s_1103_, lean_object* v___f_1104_, uint64_t v_size_1105_, lean_object* v_x_1106_){
_start:
{
if (lean_obj_tag(v_x_1106_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v___f_1104_);
lean_dec_ref(v___f_1102_);
v_a_1108_ = lean_ctor_get(v_x_1106_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_x_1106_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v_x_1106_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v_x_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1165_; 
v_a_1117_ = lean_ctor_get(v_x_1106_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1106_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1119_ = v_x_1106_;
v_isShared_1120_ = v_isSharedCheck_1165_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v_x_1106_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1165_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
uint8_t v___x_1121_; 
v___x_1121_ = lean_unbox(v_a_1117_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v_val_1124_; lean_object* v___x_1128_; 
lean_dec_ref(v___f_1104_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_uv_tcp_cancel_recv(v_s_1103_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v_a_1129_);
v___x_1131_ = v___x_1119_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v_val_1124_ = v___x_1131_;
goto v___jp_1123_;
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; 
v_a_1133_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1128_, 1);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 0);
lean_ctor_set(v___x_1119_, 0, v_a_1133_);
v___x_1135_ = v___x_1119_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
v_val_1124_ = v___x_1135_;
goto v___jp_1123_;
}
}
v___jp_1123_:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_val_1124_);
v___x_1126_ = lean_unbox(v_a_1117_);
lean_dec(v_a_1117_);
v___x_1127_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1122_, v___x_1126_, v___x_1125_, v___f_1102_);
return v___x_1127_;
}
}
else
{
lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___f_1139_; lean_object* v_val_1141_; lean_object* v___x_1148_; 
lean_dec(v_a_1117_);
lean_dec_ref(v___f_1102_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = 0;
v___f_1139_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0));
v___x_1148_ = lean_uv_tcp_recv(v_s_1103_, v_size_1105_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 1);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
v_val_1141_ = v___x_1154_;
goto v___jp_1140_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1148_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1148_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 0);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
v_val_1141_ = v___x_1162_;
goto v___jp_1140_;
}
}
}
v___jp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v_val_1141_);
v___x_1143_ = v___x_1119_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_val_1141_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
v___x_1145_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1137_, v___x_1138_, v___x_1144_, v___f_1139_);
v___x_1146_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1137_, v___x_1138_, v___x_1145_, v___f_1104_);
return v___x_1146_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object* v___f_1166_, lean_object* v_s_1167_, lean_object* v___f_1168_, lean_object* v_size_1169_, lean_object* v_x_1170_, lean_object* v___y_1171_){
_start:
{
uint64_t v_size_boxed_1172_; lean_object* v_res_1173_; 
v_size_boxed_1172_ = lean_unbox_uint64(v_size_1169_);
lean_dec_ref(v_size_1169_);
v_res_1173_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(v___f_1166_, v_s_1167_, v___f_1168_, v_size_boxed_1172_, v_x_1170_);
lean_dec(v_s_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(lean_object* v___f_1174_, lean_object* v_x_1175_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v___f_1174_);
v_a_1177_ = lean_ctor_get(v_x_1175_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1179_ = v_x_1175_;
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v_x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1199_; 
v_a_1186_ = lean_ctor_get(v_x_1175_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1188_ = v_x_1175_;
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v_x_1175_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1199_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; uint8_t v___x_1191_; uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = 0;
v___x_1192_ = l_IO_Promise_isResolved___redArg(v_a_1186_);
lean_dec(v_a_1186_);
v___x_1193_ = lean_box(v___x_1192_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1193_);
v___x_1195_ = v___x_1188_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1190_, v___x_1191_, v___x_1196_, v___f_1174_);
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8___boxed(lean_object* v___f_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(v___f_1200_, v_x_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object* v___f_1204_, lean_object* v_s_1205_){
_start:
{
lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v_val_1210_; lean_object* v___x_1213_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = 0;
v___x_1213_ = lean_uv_tcp_wait_readable(v_s_1205_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 1);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v_val_1210_ = v___x_1219_;
goto v___jp_1209_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_a_1222_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1213_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1213_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 0);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
v_val_1210_ = v___x_1227_;
goto v___jp_1209_;
}
}
}
v___jp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_val_1210_);
v___x_1212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1207_, v___x_1208_, v___x_1211_, v___f_1204_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object* v___f_1230_, lean_object* v_s_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(v___f_1230_, v_s_1231_);
lean_dec(v_s_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector(lean_object* v_s_1236_, uint64_t v_size_1237_){
_start:
{
lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
v___f_1238_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__0));
v___f_1239_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__1));
lean_inc_n(v_s_1236_, 3);
v___f_1240_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1240_, 0, v_s_1236_);
v___x_1241_ = lean_box_uint64(v_size_1237_);
v___f_1242_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1242_, 0, v_s_1236_);
lean_closure_set(v___f_1242_, 1, v___x_1241_);
v___x_1243_ = lean_box_uint64(v_size_1237_);
v___f_1244_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1244_, 0, v___f_1239_);
lean_closure_set(v___f_1244_, 1, v_s_1236_);
lean_closure_set(v___f_1244_, 2, v___f_1238_);
lean_closure_set(v___f_1244_, 3, v___x_1243_);
v___f_1245_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1245_, 0, v___f_1244_);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed), 3, 2);
lean_closure_set(v___f_1246_, 0, v___f_1245_);
lean_closure_set(v___f_1246_, 1, v_s_1236_);
v___x_1247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1247_, 0, v___f_1246_);
lean_ctor_set(v___x_1247_, 1, v___f_1242_);
lean_ctor_set(v___x_1247_, 2, v___f_1240_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___boxed(lean_object* v_s_1248_, lean_object* v_size_1249_){
_start:
{
uint64_t v_size_boxed_1250_; lean_object* v_res_1251_; 
v_size_boxed_1250_ = lean_unbox_uint64(v_size_1249_);
lean_dec_ref(v_size_1249_);
v_res_1251_ = l_Std_Async_TCP_Socket_Client_recvSelector(v_s_1248_, v_size_boxed_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown(lean_object* v_s_1252_){
_start:
{
lean_object* v___f_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; lean_object* v_val_1258_; lean_object* v___x_1262_; 
v___f_1254_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = 0;
v___x_1262_ = lean_uv_tcp_shutdown(v_s_1252_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 1);
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v_val_1258_ = v___x_1268_;
goto v___jp_1257_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
v_a_1271_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1262_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1262_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 0);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
v_val_1258_ = v___x_1276_;
goto v___jp_1257_;
}
}
}
v___jp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v_val_1258_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___x_1261_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1255_, v___x_1256_, v___x_1260_, v___f_1254_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown___boxed(lean_object* v_s_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_Async_TCP_Socket_Client_shutdown(v_s_1279_);
lean_dec(v_s_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName(lean_object* v_s_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_uv_tcp_getpeername(v_s_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName___boxed(lean_object* v_s_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_Async_TCP_Socket_Client_getPeerName(v_s_1285_);
lean_dec(v_s_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName(lean_object* v_s_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_uv_tcp_getsockname(v_s_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName___boxed(lean_object* v_s_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Std_Async_TCP_Socket_Client_getSockName(v_s_1291_);
lean_dec(v_s_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay(lean_object* v_s_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_uv_tcp_nodelay(v_s_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay___boxed(lean_object* v_s_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_Async_TCP_Socket_Client_noDelay(v_s_1297_);
lean_dec(v_s_1297_);
return v_res_1299_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Client_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg(lean_object* v_s_1301_, uint8_t v_enable_1302_, lean_object* v_delay_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_1303_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; uint8_t v___x_1307_; uint32_t v___x_1308_; lean_object* v___x_1309_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
v___x_1307_ = lean_bool_to_int8(v_enable_1302_);
v___x_1308_ = lean_unbox_uint32(v_a_1306_);
lean_dec(v_a_1306_);
v___x_1309_ = lean_uv_tcp_keepalive(v_s_1301_, v___x_1307_, v___x_1308_);
return v___x_1309_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1310_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1305_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1305_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object* v_s_1318_, lean_object* v_enable_1319_, lean_object* v_delay_1320_, lean_object* v_a_1321_){
_start:
{
uint8_t v_enable_boxed_1322_; lean_object* v_res_1323_; 
v_enable_boxed_1322_ = lean_unbox(v_enable_1319_);
v_res_1323_ = l_Std_Async_TCP_Socket_Client_keepAlive___redArg(v_s_1318_, v_enable_boxed_1322_, v_delay_1320_);
lean_dec(v_delay_1320_);
lean_dec(v_s_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive(lean_object* v_s_1324_, uint8_t v_enable_1325_, lean_object* v_delay_1326_, lean_object* v_x_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_1326_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; uint8_t v___x_1331_; uint32_t v___x_1332_; lean_object* v___x_1333_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___x_1331_ = lean_bool_to_int8(v_enable_1325_);
v___x_1332_ = lean_unbox_uint32(v_a_1330_);
lean_dec(v_a_1330_);
v___x_1333_ = lean_uv_tcp_keepalive(v_s_1324_, v___x_1331_, v___x_1332_);
return v___x_1333_;
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_a_1334_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1329_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1329_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___boxed(lean_object* v_s_1342_, lean_object* v_enable_1343_, lean_object* v_delay_1344_, lean_object* v_x_1345_, lean_object* v_a_1346_){
_start:
{
uint8_t v_enable_boxed_1347_; lean_object* v_res_1348_; 
v_enable_boxed_1347_ = lean_unbox(v_enable_1343_);
v_res_1348_ = l_Std_Async_TCP_Socket_Client_keepAlive(v_s_1342_, v_enable_boxed_1347_, v_delay_1344_, v_x_1345_);
lean_dec(v_delay_1344_);
lean_dec(v_s_1342_);
return v_res_1348_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_TCP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Async_TCP_Socket_Server_keepAlive___auto__1 = _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1();
lean_mark_persistent(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1);
l_Std_Async_TCP_Socket_Client_keepAlive___auto__1 = _init_l_Std_Async_TCP_Socket_Client_keepAlive___auto__1();
lean_mark_persistent(l_Std_Async_TCP_Socket_Client_keepAlive___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_TCP(uint8_t builtin);
lean_object* initialize_Std_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_TCP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_TCP(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* lean_uv_tcp_close(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_close___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_close(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_close___boxed(lean_object*, lean_object*);
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
lean_dec(v___x_6_);
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
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_close(lean_object* v_s_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = lean_uv_tcp_close(v_s_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_close___boxed(lean_object* v_s_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_Async_TCP_Socket_Server_close(v_s_460_);
lean_dec(v_s_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName(lean_object* v_s_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_uv_tcp_getsockname(v_s_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName___boxed(lean_object* v_s_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Async_TCP_Socket_Server_getSockName(v_s_466_);
lean_dec(v_s_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay(lean_object* v_s_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_uv_tcp_nodelay(v_s_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay___boxed(lean_object* v_s_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Async_TCP_Socket_Server_noDelay(v_s_472_);
lean_dec(v_s_472_);
return v_res_474_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10));
v___x_502_ = l_Lean_mkAtom(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12);
v___x_504_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_505_ = lean_array_push(v___x_504_, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16));
v___x_517_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_518_ = lean_array_push(v___x_517_, v___x_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_519_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17);
v___x_520_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15));
v___x_521_ = lean_box(2);
v___x_522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
lean_ctor_set(v___x_522_, 2, v___x_519_);
return v___x_522_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18);
v___x_524_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13);
v___x_525_ = lean_array_push(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19);
v___x_527_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11));
v___x_528_ = lean_box(2);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
lean_ctor_set(v___x_529_, 2, v___x_526_);
return v___x_529_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20);
v___x_531_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_532_ = lean_array_push(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21);
v___x_534_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9));
v___x_535_ = lean_box(2);
v___x_536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_534_);
lean_ctor_set(v___x_536_, 2, v___x_533_);
return v___x_536_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22);
v___x_538_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_539_ = lean_array_push(v___x_538_, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_540_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23);
v___x_541_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7));
v___x_542_ = lean_box(2);
v___x_543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
lean_ctor_set(v___x_543_, 2, v___x_540_);
return v___x_543_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24);
v___x_545_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_546_ = lean_array_push(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_547_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25);
v___x_548_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4));
v___x_549_ = lean_box(2);
v___x_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_547_);
return v___x_550_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg(lean_object* v_s_552_, uint8_t v_enable_553_, lean_object* v_delay_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_554_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; uint8_t v___x_558_; uint32_t v___x_559_; lean_object* v___x_560_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = lean_bool_to_int8(v_enable_553_);
v___x_559_ = lean_unbox_uint32(v_a_557_);
lean_dec(v_a_557_);
v___x_560_ = lean_uv_tcp_keepalive(v_s_552_, v___x_558_, v___x_559_);
return v___x_560_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_556_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_556_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object* v_s_569_, lean_object* v_enable_570_, lean_object* v_delay_571_, lean_object* v_a_572_){
_start:
{
uint8_t v_enable_boxed_573_; lean_object* v_res_574_; 
v_enable_boxed_573_ = lean_unbox(v_enable_570_);
v_res_574_ = l_Std_Async_TCP_Socket_Server_keepAlive___redArg(v_s_569_, v_enable_boxed_573_, v_delay_571_);
lean_dec(v_delay_571_);
lean_dec(v_s_569_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive(lean_object* v_s_575_, uint8_t v_enable_576_, lean_object* v_delay_577_, lean_object* v_x_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_577_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; uint8_t v___x_582_; uint32_t v___x_583_; lean_object* v___x_584_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = lean_bool_to_int8(v_enable_576_);
v___x_583_ = lean_unbox_uint32(v_a_581_);
lean_dec(v_a_581_);
v___x_584_ = lean_uv_tcp_keepalive(v_s_575_, v___x_582_, v___x_583_);
return v___x_584_;
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_a_585_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_580_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_580_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___boxed(lean_object* v_s_593_, lean_object* v_enable_594_, lean_object* v_delay_595_, lean_object* v_x_596_, lean_object* v_a_597_){
_start:
{
uint8_t v_enable_boxed_598_; lean_object* v_res_599_; 
v_enable_boxed_598_ = lean_unbox(v_enable_594_);
v_res_599_ = l_Std_Async_TCP_Socket_Server_keepAlive(v_s_593_, v_enable_boxed_598_, v_delay_595_, v_x_596_);
lean_dec(v_delay_595_);
lean_dec(v_s_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk(){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_a_610_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_601_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk___boxed(lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_Async_TCP_Socket_Client_mk();
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind(lean_object* v_s_620_, lean_object* v_addr_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = lean_uv_tcp_bind(v_s_620_, v_addr_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind___boxed(lean_object* v_s_624_, lean_object* v_addr_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Async_TCP_Socket_Client_bind(v_s_624_, v_addr_625_);
lean_dec_ref(v_addr_625_);
lean_dec(v_s_624_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0(lean_object* v___x_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_mk_io_user_error(v___x_628_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
else
{
lean_object* v_val_632_; 
lean_dec_ref(v___x_628_);
v_val_632_ = lean_ctor_get(v_x_629_, 0);
lean_inc(v_val_632_);
return v_val_632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed(lean_object* v___x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Async_TCP_Socket_Client_connect___lam__0(v___x_633_, v_x_634_);
lean_dec(v_x_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1(lean_object* v___f_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v___f_636_);
v_a_639_ = lean_ctor_get(v_x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_x_637_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v_x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v_x_637_, 1);
if (lean_obj_tag(v_a_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v___f_636_);
v_a_649_ = lean_ctor_get(v_a_648_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_a_648_);
if (v_isSharedCheck_657_ == 0)
{
v___x_651_ = v_a_648_;
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v_a_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_657_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_656_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_a_658_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v_a_648_, 1);
v___x_659_ = lean_io_promise_result_opt(v_a_658_);
lean_dec(v_a_658_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = 0;
v___x_662_ = lean_task_map(v___f_636_, v___x_659_, v___x_660_, v___x_661_);
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed(lean_object* v___f_664_, lean_object* v_x_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_Async_TCP_Socket_Client_connect___lam__1(v___f_664_, v_x_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect(lean_object* v_s_672_, lean_object* v_addr_673_){
_start:
{
lean_object* v___f_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v_val_679_; lean_object* v___x_683_; 
v___f_675_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = 0;
v___x_683_ = lean_uv_tcp_connect(v_s_672_, v_addr_673_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 1);
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_val_679_ = v___x_689_;
goto v___jp_678_;
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_683_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_683_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 0);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v_val_679_ = v___x_697_;
goto v___jp_678_;
}
}
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v_val_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
v___x_682_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_676_, v___x_677_, v___x_681_, v___f_675_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___boxed(lean_object* v_s_700_, lean_object* v_addr_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Std_Async_TCP_Socket_Client_connect(v_s_700_, v_addr_701_);
lean_dec_ref(v_addr_701_);
lean_dec(v_s_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll(lean_object* v_s_704_, lean_object* v_data_705_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v_val_711_; lean_object* v___x_715_; 
v___f_707_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = 0;
v___x_715_ = lean_uv_tcp_send(v_s_704_, v_data_705_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 1);
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v_val_711_ = v___x_721_;
goto v___jp_710_;
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v_a_724_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_715_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_715_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 0);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
v_val_711_ = v___x_729_;
goto v___jp_710_;
}
}
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v_val_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
v___x_714_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_708_, v___x_709_, v___x_713_, v___f_707_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll___boxed(lean_object* v_s_732_, lean_object* v_data_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Async_TCP_Socket_Client_sendAll(v_s_732_, v_data_733_);
lean_dec(v_s_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send(lean_object* v_s_736_, lean_object* v_data_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v_val_746_; lean_object* v___x_750_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_mk_empty_array_with_capacity(v___x_739_);
v___x_741_ = lean_array_push(v___x_740_, v_data_737_);
v___f_742_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = 0;
v___x_750_ = lean_uv_tcp_send(v_s_736_, v___x_741_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 1);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v_val_746_ = v___x_756_;
goto v___jp_745_;
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_750_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_750_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 0);
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v_val_746_ = v___x_764_;
goto v___jp_745_;
}
}
}
v___jp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v_val_746_);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v___x_749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_743_, v___x_744_, v___x_748_, v___f_742_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send___boxed(lean_object* v_s_767_, lean_object* v_data_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_Async_TCP_Socket_Client_send(v_s_767_, v_data_768_);
lean_dec(v_s_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object* v___x_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_mk_io_user_error(v___x_771_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_val_775_; 
lean_dec_ref(v___x_771_);
v_val_775_ = lean_ctor_get(v_x_772_, 0);
lean_inc(v_val_775_);
return v_val_775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(lean_object* v___x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(v___x_776_, v_x_777_);
lean_dec(v_x_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(lean_object* v___f_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v___f_779_);
v_a_782_ = lean_ctor_get(v_x_780_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_780_);
if (v_isSharedCheck_790_ == 0)
{
v___x_784_ = v_x_780_;
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v_x_780_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_790_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_789_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; 
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
else
{
lean_object* v_a_791_; 
v_a_791_ = lean_ctor_get(v_x_780_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v_x_780_, 1);
if (lean_obj_tag(v_a_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v___f_779_);
v_a_792_ = lean_ctor_get(v_a_791_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v_a_791_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v_a_791_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v_a_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_799_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_a_801_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v_a_791_, 1);
v___x_802_ = lean_io_promise_result_opt(v_a_801_);
lean_dec(v_a_801_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = 0;
v___x_805_ = lean_task_map(v___f_779_, v___x_802_, v___x_803_, v___x_804_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(lean_object* v___f_807_, lean_object* v_x_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(v___f_807_, v_x_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f(lean_object* v_s_815_, uint64_t v_size_816_){
_start:
{
lean_object* v___f_818_; lean_object* v___x_819_; uint8_t v___x_820_; lean_object* v_val_822_; lean_object* v___x_826_; 
v___f_818_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1));
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = 0;
v___x_826_ = lean_uv_tcp_recv(v_s_815_, v_size_816_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 1);
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
v_val_822_ = v___x_832_;
goto v___jp_821_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_826_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_826_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 0);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v_val_822_ = v___x_840_;
goto v___jp_821_;
}
}
}
v___jp_821_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_val_822_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
v___x_825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_819_, v___x_820_, v___x_824_, v___f_818_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object* v_s_843_, lean_object* v_size_844_, lean_object* v_a_845_){
_start:
{
uint64_t v_size_boxed_846_; lean_object* v_res_847_; 
v_size_boxed_846_ = lean_unbox_uint64(v_size_844_);
lean_dec_ref(v_size_844_);
v_res_847_ = l_Std_Async_TCP_Socket_Client_recv_x3f(v_s_843_, v_size_boxed_846_);
lean_dec(v_s_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object* v_promise_848_, lean_object* v_value_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_io_promise_resolve(v_value_849_, v_promise_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0___boxed(lean_object* v_promise_852_, lean_object* v_value_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(v_promise_852_, v_value_853_);
lean_dec(v_promise_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object* v_val_859_, lean_object* v___x_860_, uint64_t v_size_861_, lean_object* v_w_862_, lean_object* v_lose_863_){
_start:
{
lean_object* v_finished_865_; lean_object* v_promise_866_; lean_object* v_a_868_; lean_object* v___f_872_; lean_object* v___x_873_; uint8_t v___y_875_; uint8_t v___x_899_; 
v_finished_865_ = lean_ctor_get(v_w_862_, 0);
lean_inc(v_finished_865_);
v_promise_866_ = lean_ctor_get(v_w_862_, 1);
lean_inc_n(v_promise_866_, 2);
lean_dec_ref(v_w_862_);
v___f_872_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_872_, 0, v_promise_866_);
v___x_873_ = lean_st_ref_take(v_finished_865_);
v___x_899_ = lean_unbox(v___x_873_);
lean_dec(v___x_873_);
if (v___x_899_ == 0)
{
uint8_t v___x_900_; 
v___x_900_ = 1;
v___y_875_ = v___x_900_;
goto v___jp_874_;
}
else
{
uint8_t v___x_901_; 
v___x_901_ = 0;
v___y_875_ = v___x_901_;
goto v___jp_874_;
}
v___jp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_a_868_);
v___x_870_ = lean_io_promise_resolve(v___x_869_, v_promise_866_);
lean_dec(v_promise_866_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
v___jp_874_:
{
uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = 1;
v___x_877_ = lean_box(v___x_876_);
v___x_878_ = lean_st_ref_put(v_finished_865_, v___x_877_);
lean_dec(v_finished_865_);
if (v___y_875_ == 0)
{
lean_object* v___x_879_; 
lean_dec_ref(v___f_872_);
lean_dec(v_promise_866_);
lean_dec_ref(v_val_859_);
v___x_879_ = lean_apply_1(v_lose_863_, lean_box(0));
return v___x_879_;
}
else
{
lean_object* v___x_880_; 
lean_dec_ref(v_lose_863_);
v___x_880_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_859_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_881_; 
lean_dec_ref_known(v___x_880_, 1);
v___x_881_ = lean_uv_tcp_recv(v___x_860_, v_size_861_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_promise_866_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_896_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_896_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___f_886_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__1));
v___x_887_ = lean_io_promise_result_opt(v_a_882_);
lean_dec(v_a_882_);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = 0;
v___x_890_ = lean_task_map(v___f_886_, v___x_887_, v___x_888_, v___x_889_);
v___x_891_ = lean_box(0);
v___x_892_ = lean_io_map_task(v___f_872_, v___x_890_, v___x_888_, v___x_889_);
lean_dec_ref(v___x_892_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_891_);
v___x_894_ = v___x_884_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_891_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_a_897_; 
lean_dec_ref(v___f_872_);
v_a_897_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_881_, 1);
v_a_868_ = v_a_897_;
goto v___jp_867_;
}
}
else
{
lean_object* v_a_898_; 
lean_dec_ref(v___f_872_);
v_a_898_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_880_, 1);
v_a_868_ = v_a_898_;
goto v___jp_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object* v_val_902_, lean_object* v___x_903_, lean_object* v_size_904_, lean_object* v_w_905_, lean_object* v_lose_906_, lean_object* v___y_907_){
_start:
{
uint64_t v_size_boxed_908_; lean_object* v_res_909_; 
v_size_boxed_908_ = lean_unbox_uint64(v_size_904_);
lean_dec_ref(v_size_904_);
v_res_909_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_902_, v___x_903_, v_size_boxed_908_, v_w_905_, v_lose_906_);
lean_dec(v___x_903_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object* v_x_910_){
_start:
{
if (lean_obj_tag(v_x_910_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_920_; 
v_a_912_ = lean_ctor_get(v_x_910_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v_x_910_);
if (v_isSharedCheck_920_ == 0)
{
v___x_914_ = v_x_910_;
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v_x_910_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_919_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_930_; 
v_a_921_ = lean_ctor_get(v_x_910_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_910_);
if (v_isSharedCheck_930_ == 0)
{
v___x_923_ = v_x_910_;
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v_x_910_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_a_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_929_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object* v_x_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(v_x_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object* v_x_938_){
_start:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_948_; 
v_a_940_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_942_ = v_x_938_;
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v_x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_948_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
else
{
lean_object* v___x_949_; 
lean_dec_ref_known(v_x_938_, 1);
v___x_949_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__1));
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object* v_x_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(v_x_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object* v_s_953_){
_start:
{
lean_object* v_val_956_; lean_object* v___x_958_; 
v___x_958_ = lean_uv_tcp_cancel_recv(v_s_953_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 1);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
v_val_956_ = v___x_964_;
goto v___jp_955_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_958_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_958_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 0);
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v_val_956_ = v___x_972_;
goto v___jp_955_;
}
}
}
v___jp_955_:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v_val_956_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object* v_s_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(v_s_975_);
lean_dec(v_s_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object* v_s_978_, uint64_t v_size_979_, lean_object* v_waiter_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_a_984_; 
if (lean_obj_tag(v_a_981_) == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_waiter_980_);
v___x_986_ = lean_box(0);
v_a_984_ = v___x_986_;
goto v___jp_983_;
}
else
{
lean_object* v_val_987_; lean_object* v___f_988_; lean_object* v___x_989_; 
v_val_987_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v_a_981_, 1);
v___f_988_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0));
v___x_989_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_987_, v_s_978_, v_size_979_, v_waiter_980_, v___f_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v_a_984_ = v_a_990_;
goto v___jp_983_;
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_989_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 0);
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
v___jp_983_:
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_a_984_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object* v_s_999_, lean_object* v_size_1000_, lean_object* v_waiter_1001_, lean_object* v_a_1002_, lean_object* v___y_1003_){
_start:
{
uint64_t v_size_boxed_1004_; lean_object* v_res_1005_; 
v_size_boxed_1004_ = lean_unbox_uint64(v_size_1000_);
lean_dec_ref(v_size_1000_);
v_res_1005_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(v_s_999_, v_size_boxed_1004_, v_waiter_1001_, v_a_1002_);
lean_dec(v_s_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object* v___f_1010_, lean_object* v_x_1011_){
_start:
{
if (lean_obj_tag(v_x_1011_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v___f_1010_);
v_a_1013_ = lean_ctor_get(v_x_1011_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_x_1011_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1015_ = v_x_1011_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v_x_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_a_1022_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_x_1011_, 1);
v___x_1023_ = lean_io_promise_result_opt(v_a_1022_);
lean_dec(v_a_1022_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = 0;
v___x_1026_ = lean_io_map_task(v___f_1010_, v___x_1023_, v___x_1024_, v___x_1025_);
lean_dec_ref(v___x_1026_);
v___x_1027_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1));
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object* v___f_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(v___f_1028_, v_x_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object* v_s_1032_, uint64_t v_size_1033_, lean_object* v_waiter_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v_val_1042_; lean_object* v___x_1045_; 
v___x_1036_ = lean_box_uint64(v_size_1033_);
lean_inc(v_s_1032_);
v___f_1037_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1037_, 0, v_s_1032_);
lean_closure_set(v___f_1037_, 1, v___x_1036_);
lean_closure_set(v___f_1037_, 2, v_waiter_1034_);
v___f_1038_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1038_, 0, v___f_1037_);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = 0;
v___x_1045_ = lean_uv_tcp_wait_readable(v_s_1032_);
lean_dec(v_s_1032_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
v_val_1042_ = v___x_1051_;
goto v___jp_1041_;
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1045_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1045_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 0);
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
v_val_1042_ = v___x_1059_;
goto v___jp_1041_;
}
}
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_val_1042_);
v___x_1044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1039_, v___x_1040_, v___x_1043_, v___f_1038_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object* v_s_1062_, lean_object* v_size_1063_, lean_object* v_waiter_1064_, lean_object* v___y_1065_){
_start:
{
uint64_t v_size_boxed_1066_; lean_object* v_res_1067_; 
v_size_boxed_1066_ = lean_unbox_uint64(v_size_1063_);
lean_dec_ref(v_size_1063_);
v_res_1067_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(v_s_1062_, v_size_boxed_1066_, v_waiter_1064_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object* v___f_1068_, lean_object* v___x_1069_, uint8_t v___x_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v___x_1069_);
lean_dec_ref(v___f_1068_);
v_a_1073_ = lean_ctor_get(v_x_1071_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1075_ = v_x_1071_;
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v_x_1071_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1081_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1082_; 
v_a_1082_ = lean_ctor_get(v_x_1071_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v_x_1071_, 1);
if (lean_obj_tag(v_a_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v___x_1069_);
lean_dec_ref(v___f_1068_);
v_a_1083_ = lean_ctor_get(v_a_1082_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_a_1082_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1085_ = v_a_1082_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v_a_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1092_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_a_1082_, 1);
v___x_1093_ = lean_io_promise_result_opt(v_a_1092_);
lean_dec(v_a_1092_);
v___x_1094_ = lean_task_map(v___f_1068_, v___x_1093_, v___x_1069_, v___x_1070_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object* v___f_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v___x_2890__boxed_1101_; lean_object* v_res_1102_; 
v___x_2890__boxed_1101_ = lean_unbox(v___x_1098_);
v_res_1102_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(v___f_1096_, v___x_1097_, v___x_2890__boxed_1101_, v_x_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object* v___f_1108_, lean_object* v_s_1109_, lean_object* v___f_1110_, uint64_t v_size_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v___f_1110_);
lean_dec_ref(v___f_1108_);
v_a_1114_ = lean_ctor_get(v_x_1112_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1116_ = v_x_1112_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v_x_1112_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1171_; 
v_a_1123_ = lean_ctor_get(v_x_1112_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1112_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1125_ = v_x_1112_;
v_isShared_1126_ = v_isSharedCheck_1171_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v_x_1112_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1171_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_unbox(v_a_1123_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v_val_1130_; lean_object* v___x_1134_; 
lean_dec_ref(v___f_1110_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_uv_tcp_cancel_recv(v_s_1109_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v_a_1135_);
v___x_1137_ = v___x_1125_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
v_val_1130_ = v___x_1137_;
goto v___jp_1129_;
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; 
v_a_1139_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1134_, 1);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1139_);
v___x_1141_ = v___x_1125_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
v_val_1130_ = v___x_1141_;
goto v___jp_1129_;
}
}
v___jp_1129_:
{
lean_object* v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_val_1130_);
v___x_1132_ = lean_unbox(v_a_1123_);
lean_dec(v_a_1123_);
v___x_1133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1128_, v___x_1132_, v___x_1131_, v___f_1108_);
return v___x_1133_;
}
}
else
{
lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___f_1145_; lean_object* v_val_1147_; lean_object* v___x_1154_; 
lean_dec(v_a_1123_);
lean_dec_ref(v___f_1108_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = 0;
v___f_1145_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0));
v___x_1154_ = lean_uv_tcp_recv(v_s_1109_, v_size_1111_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 1);
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
v_val_1147_ = v___x_1160_;
goto v___jp_1146_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1154_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1154_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 0);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v_val_1147_ = v___x_1168_;
goto v___jp_1146_;
}
}
}
v___jp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v_val_1147_);
v___x_1149_ = v___x_1125_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_val_1147_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
v___x_1151_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1143_, v___x_1144_, v___x_1150_, v___f_1145_);
v___x_1152_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1143_, v___x_1144_, v___x_1151_, v___f_1110_);
return v___x_1152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object* v___f_1172_, lean_object* v_s_1173_, lean_object* v___f_1174_, lean_object* v_size_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_){
_start:
{
uint64_t v_size_boxed_1178_; lean_object* v_res_1179_; 
v_size_boxed_1178_ = lean_unbox_uint64(v_size_1175_);
lean_dec_ref(v_size_1175_);
v_res_1179_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(v___f_1172_, v_s_1173_, v___f_1174_, v_size_boxed_1178_, v_x_1176_);
lean_dec(v_s_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(lean_object* v___f_1180_, lean_object* v_x_1181_){
_start:
{
if (lean_obj_tag(v_x_1181_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v___f_1180_);
v_a_1183_ = lean_ctor_get(v_x_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1185_ = v_x_1181_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v_x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1205_; 
v_a_1192_ = lean_ctor_get(v_x_1181_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1194_ = v_x_1181_;
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v_x_1181_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1205_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = 0;
v___x_1198_ = l_IO_Promise_isResolved___redArg(v_a_1192_);
lean_dec(v_a_1192_);
v___x_1199_ = lean_box(v___x_1198_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1199_);
v___x_1201_ = v___x_1194_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
v___x_1203_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1196_, v___x_1197_, v___x_1202_, v___f_1180_);
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8___boxed(lean_object* v___f_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(v___f_1206_, v_x_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object* v___f_1210_, lean_object* v_s_1211_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v_val_1216_; lean_object* v___x_1219_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = 0;
v___x_1219_ = lean_uv_tcp_wait_readable(v_s_1211_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 1);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v_val_1216_ = v___x_1225_;
goto v___jp_1215_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_a_1228_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1219_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 0);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
v_val_1216_ = v___x_1233_;
goto v___jp_1215_;
}
}
}
v___jp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_val_1216_);
v___x_1218_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1213_, v___x_1214_, v___x_1217_, v___f_1210_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object* v___f_1236_, lean_object* v_s_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(v___f_1236_, v_s_1237_);
lean_dec(v_s_1237_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector(lean_object* v_s_1242_, uint64_t v_size_1243_){
_start:
{
lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___f_1252_; lean_object* v___x_1253_; 
v___f_1244_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__0));
v___f_1245_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__1));
lean_inc_n(v_s_1242_, 3);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1246_, 0, v_s_1242_);
v___x_1247_ = lean_box_uint64(v_size_1243_);
v___f_1248_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1248_, 0, v_s_1242_);
lean_closure_set(v___f_1248_, 1, v___x_1247_);
v___x_1249_ = lean_box_uint64(v_size_1243_);
v___f_1250_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1250_, 0, v___f_1245_);
lean_closure_set(v___f_1250_, 1, v_s_1242_);
lean_closure_set(v___f_1250_, 2, v___f_1244_);
lean_closure_set(v___f_1250_, 3, v___x_1249_);
v___f_1251_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1251_, 0, v___f_1250_);
v___f_1252_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed), 3, 2);
lean_closure_set(v___f_1252_, 0, v___f_1251_);
lean_closure_set(v___f_1252_, 1, v_s_1242_);
v___x_1253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1253_, 0, v___f_1252_);
lean_ctor_set(v___x_1253_, 1, v___f_1248_);
lean_ctor_set(v___x_1253_, 2, v___f_1246_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___boxed(lean_object* v_s_1254_, lean_object* v_size_1255_){
_start:
{
uint64_t v_size_boxed_1256_; lean_object* v_res_1257_; 
v_size_boxed_1256_ = lean_unbox_uint64(v_size_1255_);
lean_dec_ref(v_size_1255_);
v_res_1257_ = l_Std_Async_TCP_Socket_Client_recvSelector(v_s_1254_, v_size_boxed_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown(lean_object* v_s_1258_){
_start:
{
lean_object* v___f_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v_val_1264_; lean_object* v___x_1268_; 
v___f_1260_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = 0;
v___x_1268_ = lean_uv_tcp_shutdown(v_s_1258_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 1);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
v_val_1264_ = v___x_1274_;
goto v___jp_1263_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_a_1277_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1268_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1268_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 0);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
v_val_1264_ = v___x_1282_;
goto v___jp_1263_;
}
}
}
v___jp_1263_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_val_1264_);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
v___x_1267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1261_, v___x_1262_, v___x_1266_, v___f_1260_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown___boxed(lean_object* v_s_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Std_Async_TCP_Socket_Client_shutdown(v_s_1285_);
lean_dec(v_s_1285_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_close(lean_object* v_s_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_uv_tcp_close(v_s_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_close___boxed(lean_object* v_s_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Std_Async_TCP_Socket_Client_close(v_s_1291_);
lean_dec(v_s_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName(lean_object* v_s_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_uv_tcp_getpeername(v_s_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName___boxed(lean_object* v_s_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_Async_TCP_Socket_Client_getPeerName(v_s_1297_);
lean_dec(v_s_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName(lean_object* v_s_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_uv_tcp_getsockname(v_s_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName___boxed(lean_object* v_s_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_Async_TCP_Socket_Client_getSockName(v_s_1303_);
lean_dec(v_s_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay(lean_object* v_s_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_uv_tcp_nodelay(v_s_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay___boxed(lean_object* v_s_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_Async_TCP_Socket_Client_noDelay(v_s_1309_);
lean_dec(v_s_1309_);
return v_res_1311_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Client_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg(lean_object* v_s_1313_, uint8_t v_enable_1314_, lean_object* v_delay_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_1315_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; uint8_t v___x_1319_; uint32_t v___x_1320_; lean_object* v___x_1321_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
v___x_1319_ = lean_bool_to_int8(v_enable_1314_);
v___x_1320_ = lean_unbox_uint32(v_a_1318_);
lean_dec(v_a_1318_);
v___x_1321_ = lean_uv_tcp_keepalive(v_s_1313_, v___x_1319_, v___x_1320_);
return v___x_1321_;
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_a_1322_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1317_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1317_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object* v_s_1330_, lean_object* v_enable_1331_, lean_object* v_delay_1332_, lean_object* v_a_1333_){
_start:
{
uint8_t v_enable_boxed_1334_; lean_object* v_res_1335_; 
v_enable_boxed_1334_ = lean_unbox(v_enable_1331_);
v_res_1335_ = l_Std_Async_TCP_Socket_Client_keepAlive___redArg(v_s_1330_, v_enable_boxed_1334_, v_delay_1332_);
lean_dec(v_delay_1332_);
lean_dec(v_s_1330_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive(lean_object* v_s_1336_, uint8_t v_enable_1337_, lean_object* v_delay_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; uint8_t v___x_1343_; uint32_t v___x_1344_; lean_object* v___x_1345_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1343_ = lean_bool_to_int8(v_enable_1337_);
v___x_1344_ = lean_unbox_uint32(v_a_1342_);
lean_dec(v_a_1342_);
v___x_1345_ = lean_uv_tcp_keepalive(v_s_1336_, v___x_1343_, v___x_1344_);
return v___x_1345_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1341_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1341_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___boxed(lean_object* v_s_1354_, lean_object* v_enable_1355_, lean_object* v_delay_1356_, lean_object* v_x_1357_, lean_object* v_a_1358_){
_start:
{
uint8_t v_enable_boxed_1359_; lean_object* v_res_1360_; 
v_enable_boxed_1359_ = lean_unbox(v_enable_1355_);
v_res_1360_ = l_Std_Async_TCP_Socket_Client_keepAlive(v_s_1354_, v_enable_boxed_1359_, v_delay_1356_, v_x_1357_);
lean_dec(v_delay_1356_);
lean_dec(v_s_1354_);
return v_res_1360_;
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

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
lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(lean_object* v_delay_3_){
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
LEAN_EXPORT void l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay_0interp(lean_interpreter_value* stack)
{
lean_object* v_delay_3_ = stack[0].m_obj;
lean_object* v_res_18_;
v_res_18_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_3_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay___boxed(lean_object* v_delay_19_, lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_19_);
lean_dec(v_delay_19_);
return v_res_21_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_mk(){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_23_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_23_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_40_;
v_res_40_ = l_Std_Async_TCP_Socket_Server_mk();
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_mk___boxed(lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Async_TCP_Socket_Server_mk();
return v_res_42_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_bind(lean_object* v_s_43_, lean_object* v_addr_44_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_uv_tcp_bind(v_s_43_, v_addr_44_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_43_ = stack[0].m_obj;
lean_object* v_addr_44_ = stack[1].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Std_Async_TCP_Socket_Server_bind(v_s_43_, v_addr_44_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_bind___boxed(lean_object* v_s_48_, lean_object* v_addr_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Async_TCP_Socket_Server_bind(v_s_48_, v_addr_49_);
lean_dec_ref(v_addr_49_);
lean_dec(v_s_48_);
return v_res_51_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_listen(lean_object* v_s_52_, uint32_t v_backlog_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_uv_tcp_listen(v_s_52_, v_backlog_53_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_listen_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_52_ = stack[0].m_obj;
uint32_t v_backlog_53_ = stack[1].m_num;
lean_object* v_res_56_;
v_res_56_ = l_Std_Async_TCP_Socket_Server_listen(v_s_52_, v_backlog_53_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_listen___boxed(lean_object* v_s_57_, lean_object* v_backlog_58_, lean_object* v_a_59_){
_start:
{
uint32_t v_backlog_boxed_60_; lean_object* v_res_61_; 
v_backlog_boxed_60_ = lean_unbox_uint32(v_backlog_58_);
lean_dec(v_backlog_58_);
v_res_61_ = l_Std_Async_TCP_Socket_Server_listen(v_s_57_, v_backlog_boxed_60_);
lean_dec(v_s_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0(lean_object* v_native_62_){
_start:
{
lean_inc(v_native_62_);
return v_native_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__0___boxed(lean_object* v_native_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_Async_TCP_Socket_Server_accept___lam__0(v_native_63_);
lean_dec(v_native_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1(lean_object* v___x_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_mk_io_user_error(v___x_65_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
else
{
lean_object* v_val_69_; 
lean_dec_ref(v___x_65_);
v_val_69_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_val_69_);
return v_val_69_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__1___boxed(lean_object* v___x_70_, lean_object* v_x_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Async_TCP_Socket_Server_accept___lam__1(v___x_70_, v_x_71_);
lean_dec(v_x_71_);
return v_res_72_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2(lean_object* v___f_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
lean_dec_ref(v___f_73_);
v_a_76_ = lean_ctor_get(v_x_74_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_74_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v_x_74_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v_x_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_83_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
else
{
lean_object* v_a_85_; 
v_a_85_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v_x_74_, 1);
if (lean_obj_tag(v_a_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
lean_dec_ref(v___f_73_);
v_a_86_ = lean_ctor_get(v_a_85_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_a_85_);
if (v_isSharedCheck_94_ == 0)
{
v___x_88_ = v_a_85_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v_a_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_93_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; 
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_95_ = lean_ctor_get(v_a_85_, 0);
lean_inc(v_a_95_);
lean_dec_ref_known(v_a_85_, 1);
v___x_96_ = lean_io_promise_result_opt(v_a_95_);
lean_dec(v_a_95_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = 0;
v___x_99_ = lean_task_map(v___f_73_, v___x_96_, v___x_97_, v___x_98_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_accept___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_73_ = stack[0].m_obj;
lean_object* v_x_74_ = stack[1].m_obj;
lean_object* v_res_101_;
v_res_101_ = l_Std_Async_TCP_Socket_Server_accept___lam__2(v___f_73_, v_x_74_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___lam__2___boxed(lean_object* v___f_102_, lean_object* v_x_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_Async_TCP_Socket_Server_accept___lam__2(v___f_102_, v_x_103_);
return v_res_105_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_accept(lean_object* v_s_114_){
_start:
{
lean_object* v___y_117_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v_val_124_; lean_object* v___x_154_; 
v___f_119_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_accept___closed__3));
v___x_120_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_accept___closed__4));
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = 0;
v___x_154_ = lean_uv_tcp_accept(v_s_114_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 1);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
v_val_124_ = v___x_160_;
goto v___jp_123_;
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
v_a_163_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_154_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_154_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 0);
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v_val_124_ = v___x_168_;
goto v___jp_123_;
}
}
}
v___jp_116_:
{
lean_object* v___x_118_; 
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___y_117_);
return v___x_118_;
}
v___jp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v_val_124_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___x_127_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_121_, v___x_122_, v___x_126_, v___f_119_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
if (lean_obj_tag(v_a_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_a_129_ = lean_ctor_get(v_a_128_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_128_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v_a_128_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v_a_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v___y_117_ = v___x_134_;
goto v___jp_116_;
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
v_a_137_ = lean_ctor_get(v_a_128_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v_a_128_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v_a_128_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v_a_128_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
v___y_117_ = v___x_142_;
goto v___jp_116_;
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_153_; 
v_a_145_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_153_ == 0)
{
v___x_147_ = v___x_127_;
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_127_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_task_map(v___x_120_, v_a_145_, v___x_121_, v___x_122_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_accept_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_114_ = stack[0].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Std_Async_TCP_Socket_Server_accept(v_s_114_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_accept___boxed(lean_object* v_s_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Async_TCP_Socket_Server_accept(v_s_172_);
lean_dec(v_s_172_);
return v_res_174_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_tryAccept(lean_object* v_s_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_tryAccept___closed__0));
v___x_179_ = lean_uv_tcp_try_accept(v_s_176_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l_IO_ofExcept___redArg(v___x_178_, v_a_180_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_201_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_201_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_201_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_201_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
if (lean_obj_tag(v_a_182_) == 0)
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
else
{
lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
v_val_190_ = lean_ctor_get(v_a_182_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_a_182_);
if (v_isSharedCheck_200_ == 0)
{
v___x_192_ = v_a_182_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_dec(v_a_182_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_val_190_);
v___x_195_ = v_reuseFailAlloc_199_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_195_);
v___x_197_ = v___x_184_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_181_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_181_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_179_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_179_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_tryAccept_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_176_ = stack[0].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Std_Async_TCP_Socket_Server_tryAccept(v_s_176_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_tryAccept___boxed(lean_object* v_s_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Async_TCP_Socket_Server_tryAccept(v_s_219_);
lean_dec(v_s_219_);
return v_res_221_;
}
}
lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(lean_object* v_e_222_){
_start:
{
if (lean_obj_tag(v_e_222_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_233_; 
v_a_224_ = lean_ctor_get(v_e_222_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_e_222_);
if (v_isSharedCheck_233_ == 0)
{
v___x_226_ = v_e_222_;
v_isShared_227_ = v_isSharedCheck_233_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v_e_222_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_233_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_228_ = lean_io_error_to_string(v_a_224_);
v___x_229_ = lean_mk_io_user_error(v___x_228_);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 1);
lean_ctor_set(v___x_226_, 0, v___x_229_);
v___x_231_ = v___x_226_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v_e_222_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_e_222_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v_e_222_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v_e_222_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 0);
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_222_ = stack[0].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_e_222_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg___boxed(lean_object* v_e_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_e_243_);
return v_res_245_;
}
}
lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(lean_object* v_00_u03b1_246_, lean_object* v_e_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_e_247_);
return v___x_249_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_247_ = stack[1].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(lean_box(0), v_e_247_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___boxed(lean_object* v_00_u03b1_251_, lean_object* v_e_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(v_00_u03b1_251_, v_e_252_);
return v_res_254_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(lean_object* v_val_260_, lean_object* v_s_261_, lean_object* v_w_262_, lean_object* v_lose_263_){
_start:
{
lean_object* v_finished_265_; lean_object* v_promise_266_; lean_object* v_a_268_; lean_object* v___x_272_; uint8_t v___y_274_; uint8_t v___x_308_; 
v_finished_265_ = lean_ctor_get(v_w_262_, 0);
v_promise_266_ = lean_ctor_get(v_w_262_, 1);
v___x_272_ = lean_st_ref_take(v_finished_265_);
v___x_308_ = lean_unbox(v___x_272_);
lean_dec(v___x_272_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; 
v___x_309_ = 1;
v___y_274_ = v___x_309_;
goto v___jp_273_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = 0;
v___y_274_ = v___x_310_;
goto v___jp_273_;
}
v___jp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_a_268_);
v___x_270_ = lean_io_promise_resolve(v___x_269_, v_promise_266_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
v___jp_273_:
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = 1;
v___x_276_ = lean_box(v___x_275_);
v___x_277_ = lean_st_ref_put(v_finished_265_, v___x_276_);
if (v___y_274_ == 0)
{
lean_object* v___x_278_; 
lean_dec_ref(v_val_260_);
v___x_278_ = lean_apply_1(v_lose_263_, lean_box(0));
return v___x_278_;
}
else
{
lean_object* v___x_279_; 
lean_dec_ref(v_lose_263_);
v___x_279_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_260_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; 
lean_dec_ref_known(v___x_279_, 1);
v___x_280_ = lean_uv_tcp_try_accept(v_s_261_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_a_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_304_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_304_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_304_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_304_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
if (lean_obj_tag(v_a_283_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_287_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___closed__2));
v___x_288_ = lean_io_promise_resolve(v___x_287_, v_promise_266_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_288_);
v___x_290_ = v___x_285_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
else
{
lean_object* v_val_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_303_; 
v_val_292_ = lean_ctor_get(v_a_283_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_303_ == 0)
{
v___x_294_ = v_a_283_;
v_isShared_295_ = v_isSharedCheck_303_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_val_292_);
lean_dec(v_a_283_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_303_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_val_292_);
v___x_297_ = v_reuseFailAlloc_302_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_io_promise_resolve(v___x_297_, v_promise_266_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_298_);
v___x_300_ = v___x_285_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
}
else
{
lean_object* v_a_305_; 
v_a_305_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_282_, 1);
v_a_268_ = v_a_305_;
goto v___jp_267_;
}
}
else
{
lean_object* v_a_306_; 
v_a_306_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_280_, 1);
v_a_268_ = v_a_306_;
goto v___jp_267_;
}
}
else
{
lean_object* v_a_307_; 
v_a_307_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_279_, 1);
v_a_268_ = v_a_307_;
goto v___jp_267_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_260_ = stack[0].m_obj;
lean_object* v_s_261_ = stack[1].m_obj;
lean_object* v_w_262_ = stack[2].m_obj;
lean_object* v_lose_263_ = stack[3].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(v_val_260_, v_s_261_, v_w_262_, v_lose_263_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(lean_object* v_val_312_, lean_object* v_s_313_, lean_object* v_w_314_, lean_object* v_lose_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(v_val_312_, v_s_313_, v_w_314_, v_lose_315_);
lean_dec_ref(v_w_314_);
lean_dec(v_s_313_);
return v_res_317_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(lean_object* v_s_318_){
_start:
{
lean_object* v_val_321_; lean_object* v_a_324_; lean_object* v_a_327_; lean_object* v___x_329_; 
v___x_329_ = lean_uv_tcp_try_accept(v_s_318_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_a_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
if (lean_obj_tag(v_a_332_) == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
v_a_324_ = v___x_333_;
goto v___jp_323_;
}
else
{
lean_object* v_val_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_val_334_ = lean_ctor_get(v_a_332_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_a_332_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v_a_332_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_val_334_);
lean_dec(v_a_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_val_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v_a_324_ = v___x_339_;
goto v___jp_323_;
}
}
}
}
else
{
lean_object* v_a_342_; 
v_a_342_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_331_, 1);
v_a_327_ = v_a_342_;
goto v___jp_326_;
}
}
else
{
lean_object* v_a_343_; 
v_a_343_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_329_, 1);
v_a_327_ = v_a_343_;
goto v___jp_326_;
}
v___jp_320_:
{
lean_object* v___x_322_; 
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_val_321_);
return v___x_322_;
}
v___jp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_324_);
v_val_321_ = v___x_325_;
goto v___jp_320_;
}
v___jp_326_:
{
lean_object* v___x_328_; 
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v_a_327_);
v_val_321_ = v___x_328_;
goto v___jp_320_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_318_ = stack[0].m_obj;
lean_object* v_res_344_;
v_res_344_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(v_s_318_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(lean_object* v_s_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(v_s_345_);
lean_dec(v_s_345_);
return v_res_347_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(lean_object* v___x_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_348_ = stack[0].m_obj;
lean_object* v_res_351_;
v_res_351_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(v___x_348_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(lean_object* v___x_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(v___x_352_);
return v_res_354_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(lean_object* v_s_357_, lean_object* v_waiter_358_, lean_object* v_x_359_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_box(0);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
else
{
lean_object* v_val_363_; lean_object* v___f_364_; lean_object* v___x_365_; 
v_val_363_ = lean_ctor_get(v_x_359_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v_x_359_, 1);
v___f_364_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0));
v___x_365_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(v_val_363_, v_s_357_, v_waiter_358_, v___f_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_357_ = stack[0].m_obj;
lean_object* v_waiter_358_ = stack[1].m_obj;
lean_object* v_x_359_ = stack[2].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(v_s_357_, v_waiter_358_, v_x_359_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(lean_object* v_s_367_, lean_object* v_waiter_368_, lean_object* v_x_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(v_s_367_, v_waiter_368_, v_x_369_);
lean_dec_ref(v_waiter_368_);
lean_dec(v_s_367_);
return v_res_371_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(lean_object* v___f_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_val_376_; 
if (lean_obj_tag(v_x_373_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_386_; 
lean_dec_ref(v___f_372_);
v_a_378_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_386_ == 0)
{
v___x_380_ = v_x_373_;
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_x_373_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_386_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_385_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_403_; 
v_a_387_ = lean_ctor_get(v_x_373_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_373_);
if (v_isSharedCheck_403_ == 0)
{
v___x_389_ = v_x_373_;
v_isShared_390_ = v_isSharedCheck_403_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v_x_373_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_403_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_io_promise_result_opt(v_a_387_);
lean_dec(v_a_387_);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = 0;
v___x_394_ = l_EIO_chainTask___redArg(v___x_391_, v___f_372_, v___x_392_, v___x_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_a_395_);
v___x_397_ = v___x_389_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
v_val_376_ = v___x_397_;
goto v___jp_375_;
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; 
v_a_399_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_394_, 1);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 0);
lean_ctor_set(v___x_389_, 0, v_a_399_);
v___x_401_ = v___x_389_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
v_val_376_ = v___x_401_;
goto v___jp_375_;
}
}
}
}
v___jp_375_:
{
lean_object* v___x_377_; 
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v_val_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_372_ = stack[0].m_obj;
lean_object* v_x_373_ = stack[1].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(v___f_372_, v_x_373_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed(lean_object* v___f_405_, lean_object* v_x_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(v___f_405_, v_x_406_);
return v_res_408_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(lean_object* v_s_409_, lean_object* v_waiter_410_){
_start:
{
lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v_val_417_; lean_object* v___x_420_; 
lean_inc(v_s_409_);
v___f_412_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_412_, 0, v_s_409_);
lean_closure_set(v___f_412_, 1, v_waiter_410_);
v___f_413_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_413_, 0, v___f_412_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = 0;
v___x_420_ = lean_uv_tcp_wait_acceptable(v_s_409_);
lean_dec(v_s_409_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 1);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
v_val_417_ = v___x_426_;
goto v___jp_416_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_a_429_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_420_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_420_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 0);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v_val_417_ = v___x_434_;
goto v___jp_416_;
}
}
}
v___jp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v_val_417_);
v___x_419_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_414_, v___x_415_, v___x_418_, v___f_413_);
return v___x_419_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_409_ = stack[0].m_obj;
lean_object* v_waiter_410_ = stack[1].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(v_s_409_, v_waiter_410_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed(lean_object* v_s_438_, lean_object* v_waiter_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(v_s_438_, v_waiter_439_);
return v_res_441_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(lean_object* v_s_442_){
_start:
{
lean_object* v_val_445_; lean_object* v___x_447_; 
v___x_447_ = lean_uv_tcp_cancel_accept(v_s_442_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
v_val_445_ = v___x_453_;
goto v___jp_444_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_447_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_447_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 0);
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
v_val_445_ = v___x_461_;
goto v___jp_444_;
}
}
}
v___jp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v_val_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_442_ = stack[0].m_obj;
lean_object* v_res_464_;
v_res_464_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(v_s_442_);
stack->m_obj
 = v_res_464_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed(lean_object* v_s_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(v_s_465_);
lean_dec(v_s_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_acceptSelector(lean_object* v_s_468_){
_start:
{
lean_object* v___f_469_; lean_object* v___f_470_; lean_object* v___f_471_; lean_object* v___x_472_; 
lean_inc_n(v_s_468_, 2);
v___f_469_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed), 2, 1);
lean_closure_set(v___f_469_, 0, v_s_468_);
v___f_470_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_470_, 0, v_s_468_);
v___f_471_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed), 2, 1);
lean_closure_set(v___f_471_, 0, v_s_468_);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v___f_469_);
lean_ctor_set(v___x_472_, 1, v___f_470_);
lean_ctor_set(v___x_472_, 2, v___f_471_);
return v___x_472_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_getSockName(lean_object* v_s_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_uv_tcp_getsockname(v_s_473_);
return v___x_475_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_getSockName_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_473_ = stack[0].m_obj;
lean_object* v_res_476_;
v_res_476_ = l_Std_Async_TCP_Socket_Server_getSockName(v_s_473_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_getSockName___boxed(lean_object* v_s_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Async_TCP_Socket_Server_getSockName(v_s_477_);
lean_dec(v_s_477_);
return v_res_479_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_noDelay(lean_object* v_s_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = lean_uv_tcp_nodelay(v_s_480_);
return v___x_482_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_noDelay_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_480_ = stack[0].m_obj;
lean_object* v_res_483_;
v_res_483_ = l_Std_Async_TCP_Socket_Server_noDelay(v_s_480_);
stack->m_obj
 = v_res_483_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_noDelay___boxed(lean_object* v_s_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Async_TCP_Socket_Server_noDelay(v_s_484_);
lean_dec(v_s_484_);
return v_res_486_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10));
v___x_514_ = l_Lean_mkAtom(v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12);
v___x_516_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_517_ = lean_array_push(v___x_516_, v___x_515_);
return v___x_517_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16));
v___x_529_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_530_ = lean_array_push(v___x_529_, v___x_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_531_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17);
v___x_532_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15));
v___x_533_ = lean_box(2);
v___x_534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_531_);
return v___x_534_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18);
v___x_536_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13);
v___x_537_ = lean_array_push(v___x_536_, v___x_535_);
return v___x_537_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19);
v___x_539_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11));
v___x_540_ = lean_box(2);
v___x_541_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_539_);
lean_ctor_set(v___x_541_, 2, v___x_538_);
return v___x_541_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20);
v___x_543_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_544_ = lean_array_push(v___x_543_, v___x_542_);
return v___x_544_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_545_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21);
v___x_546_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9));
v___x_547_ = lean_box(2);
v___x_548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_545_);
return v___x_548_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22);
v___x_550_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_551_ = lean_array_push(v___x_550_, v___x_549_);
return v___x_551_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23);
v___x_553_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7));
v___x_554_ = lean_box(2);
v___x_555_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
lean_ctor_set(v___x_555_, 2, v___x_552_);
return v___x_555_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24);
v___x_557_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5));
v___x_558_ = lean_array_push(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25);
v___x_560_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4));
v___x_561_ = lean_box(2);
v___x_562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_559_);
return v___x_562_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_563_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg(lean_object* v_s_564_, uint8_t v_enable_565_, lean_object* v_delay_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_566_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; uint8_t v___x_570_; uint32_t v___x_571_; lean_object* v___x_572_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = lean_bool_to_int8(v_enable_565_);
v___x_571_ = lean_unbox_uint32(v_a_569_);
lean_dec(v_a_569_);
v___x_572_ = lean_uv_tcp_keepalive(v_s_564_, v___x_570_, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_568_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_568_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_keepAlive___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_564_ = stack[0].m_obj;
uint8_t v_enable_565_ = stack[1].m_num;
lean_object* v_delay_566_ = stack[2].m_obj;
lean_object* v_res_581_;
v_res_581_ = l_Std_Async_TCP_Socket_Server_keepAlive___redArg(v_s_564_, v_enable_565_, v_delay_566_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___redArg___boxed(lean_object* v_s_582_, lean_object* v_enable_583_, lean_object* v_delay_584_, lean_object* v_a_585_){
_start:
{
uint8_t v_enable_boxed_586_; lean_object* v_res_587_; 
v_enable_boxed_586_ = lean_unbox(v_enable_583_);
v_res_587_ = l_Std_Async_TCP_Socket_Server_keepAlive___redArg(v_s_582_, v_enable_boxed_586_, v_delay_584_);
lean_dec(v_delay_584_);
lean_dec(v_s_582_);
return v_res_587_;
}
}
lean_object* l_Std_Async_TCP_Socket_Server_keepAlive(lean_object* v_s_588_, uint8_t v_enable_589_, lean_object* v_delay_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_590_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; uint8_t v___x_595_; uint32_t v___x_596_; lean_object* v___x_597_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_bool_to_int8(v_enable_589_);
v___x_596_ = lean_unbox_uint32(v_a_594_);
lean_dec(v_a_594_);
v___x_597_ = lean_uv_tcp_keepalive(v_s_588_, v___x_595_, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
v_a_598_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_593_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_593_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Server_keepAlive_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_588_ = stack[0].m_obj;
uint8_t v_enable_589_ = stack[1].m_num;
lean_object* v_delay_590_ = stack[2].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_Std_Async_TCP_Socket_Server_keepAlive(v_s_588_, v_enable_589_, v_delay_590_, lean_box(0));
stack->m_obj
 = v_res_606_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Server_keepAlive___boxed(lean_object* v_s_607_, lean_object* v_enable_608_, lean_object* v_delay_609_, lean_object* v_x_610_, lean_object* v_a_611_){
_start:
{
uint8_t v_enable_boxed_612_; lean_object* v_res_613_; 
v_enable_boxed_612_ = lean_unbox(v_enable_608_);
v_res_613_ = l_Std_Async_TCP_Socket_Server_keepAlive(v_s_607_, v_enable_boxed_612_, v_delay_609_, v_x_610_);
lean_dec(v_delay_609_);
lean_dec(v_s_607_);
return v_res_613_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_mk(){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_uv_tcp_new();
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
v_a_624_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_615_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_615_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
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
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_632_;
v_res_632_ = l_Std_Async_TCP_Socket_Client_mk();
stack->m_obj
 = v_res_632_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_mk___boxed(lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Async_TCP_Socket_Client_mk();
return v_res_634_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_bind(lean_object* v_s_635_, lean_object* v_addr_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_uv_tcp_bind(v_s_635_, v_addr_636_);
return v___x_638_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_635_ = stack[0].m_obj;
lean_object* v_addr_636_ = stack[1].m_obj;
lean_object* v_res_639_;
v_res_639_ = l_Std_Async_TCP_Socket_Client_bind(v_s_635_, v_addr_636_);
stack->m_obj
 = v_res_639_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_bind___boxed(lean_object* v_s_640_, lean_object* v_addr_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_Async_TCP_Socket_Client_bind(v_s_640_, v_addr_641_);
lean_dec_ref(v_addr_641_);
lean_dec(v_s_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0(lean_object* v___x_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_mk_io_user_error(v___x_644_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
else
{
lean_object* v_val_648_; 
lean_dec_ref(v___x_644_);
v_val_648_ = lean_ctor_get(v_x_645_, 0);
lean_inc(v_val_648_);
return v_val_648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed(lean_object* v___x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Async_TCP_Socket_Client_connect___lam__0(v___x_649_, v_x_650_);
lean_dec(v_x_650_);
return v_res_651_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1(lean_object* v___f_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v___f_652_);
v_a_655_ = lean_ctor_get(v_x_653_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v_x_653_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v_x_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_662_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
else
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v_x_653_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v_x_653_, 1);
if (lean_obj_tag(v_a_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v___f_652_);
v_a_665_ = lean_ctor_get(v_a_664_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_a_664_);
if (v_isSharedCheck_673_ == 0)
{
v___x_667_ = v_a_664_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v_a_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_672_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_a_674_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v_a_664_, 1);
v___x_675_ = lean_io_promise_result_opt(v_a_674_);
lean_dec(v_a_674_);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = 0;
v___x_678_ = lean_task_map(v___f_652_, v___x_675_, v___x_676_, v___x_677_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_connect___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_652_ = stack[0].m_obj;
lean_object* v_x_653_ = stack[1].m_obj;
lean_object* v_res_680_;
v_res_680_ = l_Std_Async_TCP_Socket_Client_connect___lam__1(v___f_652_, v_x_653_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed(lean_object* v___f_681_, lean_object* v_x_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_Async_TCP_Socket_Client_connect___lam__1(v___f_681_, v_x_682_);
return v_res_684_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_connect(lean_object* v_s_689_, lean_object* v_addr_690_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v_val_696_; lean_object* v___x_700_; 
v___f_692_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = 0;
v___x_700_ = lean_uv_tcp_connect(v_s_689_, v_addr_690_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 1);
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
v_val_696_ = v___x_706_;
goto v___jp_695_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_700_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_700_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 0);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
v_val_696_ = v___x_714_;
goto v___jp_695_;
}
}
}
v___jp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_val_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
v___x_699_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_693_, v___x_694_, v___x_698_, v___f_692_);
return v___x_699_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_connect_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_689_ = stack[0].m_obj;
lean_object* v_addr_690_ = stack[1].m_obj;
lean_object* v_res_717_;
v_res_717_ = l_Std_Async_TCP_Socket_Client_connect(v_s_689_, v_addr_690_);
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_connect___boxed(lean_object* v_s_718_, lean_object* v_addr_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_Async_TCP_Socket_Client_connect(v_s_718_, v_addr_719_);
lean_dec_ref(v_addr_719_);
lean_dec(v_s_718_);
return v_res_721_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_sendAll(lean_object* v_s_722_, lean_object* v_data_723_){
_start:
{
lean_object* v___f_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v_val_729_; lean_object* v___x_733_; 
v___f_725_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_726_ = lean_unsigned_to_nat(0u);
v___x_727_ = 0;
v___x_733_ = lean_uv_tcp_send(v_s_722_, v_data_723_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 1);
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v_val_729_ = v___x_739_;
goto v___jp_728_;
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
v_a_742_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_733_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_733_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 0);
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
v_val_729_ = v___x_747_;
goto v___jp_728_;
}
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_val_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
v___x_732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_726_, v___x_727_, v___x_731_, v___f_725_);
return v___x_732_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_sendAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_722_ = stack[0].m_obj;
lean_object* v_data_723_ = stack[1].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Std_Async_TCP_Socket_Client_sendAll(v_s_722_, v_data_723_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_sendAll___boxed(lean_object* v_s_751_, lean_object* v_data_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_Async_TCP_Socket_Client_sendAll(v_s_751_, v_data_752_);
lean_dec(v_s_751_);
return v_res_754_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_send(lean_object* v_s_755_, lean_object* v_data_756_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___f_761_; lean_object* v___x_762_; uint8_t v___x_763_; lean_object* v_val_765_; lean_object* v___x_769_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_mk_empty_array_with_capacity(v___x_758_);
v___x_760_ = lean_array_push(v___x_759_, v_data_756_);
v___f_761_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = 0;
v___x_769_ = lean_uv_tcp_send(v_s_755_, v___x_760_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 1);
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
v_val_765_ = v___x_775_;
goto v___jp_764_;
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_769_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_769_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 0);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
v_val_765_ = v___x_783_;
goto v___jp_764_;
}
}
}
v___jp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_val_765_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
v___x_768_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_762_, v___x_763_, v___x_767_, v___f_761_);
return v___x_768_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_755_ = stack[0].m_obj;
lean_object* v_data_756_ = stack[1].m_obj;
lean_object* v_res_786_;
v_res_786_ = l_Std_Async_TCP_Socket_Client_send(v_s_755_, v_data_756_);
stack->m_obj
 = v_res_786_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_send___boxed(lean_object* v_s_787_, lean_object* v_data_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_Async_TCP_Socket_Client_send(v_s_787_, v_data_788_);
lean_dec(v_s_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(lean_object* v___x_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_mk_io_user_error(v___x_791_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
else
{
lean_object* v_val_795_; 
lean_dec_ref(v___x_791_);
v_val_795_ = lean_ctor_get(v_x_792_, 0);
lean_inc(v_val_795_);
return v_val_795_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(lean_object* v___x_796_, lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(v___x_796_, v_x_797_);
lean_dec(v_x_797_);
return v_res_798_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(lean_object* v___f_799_, lean_object* v_x_800_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
lean_dec_ref(v___f_799_);
v_a_802_ = lean_ctor_get(v_x_800_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_810_ == 0)
{
v___x_804_ = v_x_800_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v_x_800_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_809_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
else
{
lean_object* v_a_811_; 
v_a_811_ = lean_ctor_get(v_x_800_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v_x_800_, 1);
if (lean_obj_tag(v_a_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v___f_799_);
v_a_812_ = lean_ctor_get(v_a_811_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v_a_811_);
if (v_isSharedCheck_820_ == 0)
{
v___x_814_ = v_a_811_;
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v_a_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_819_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_a_821_ = lean_ctor_get(v_a_811_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v_a_811_, 1);
v___x_822_ = lean_io_promise_result_opt(v_a_821_);
lean_dec(v_a_821_);
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = 0;
v___x_825_ = lean_task_map(v___f_799_, v___x_822_, v___x_823_, v___x_824_);
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_799_ = stack[0].m_obj;
lean_object* v_x_800_ = stack[1].m_obj;
lean_object* v_res_827_;
v_res_827_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(v___f_799_, v_x_800_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(lean_object* v___f_828_, lean_object* v_x_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(v___f_828_, v_x_829_);
return v_res_831_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f(lean_object* v_s_836_, uint64_t v_size_837_){
_start:
{
lean_object* v___f_839_; lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v_val_843_; lean_object* v___x_847_; 
v___f_839_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1));
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = 0;
v___x_847_ = lean_uv_tcp_recv(v_s_836_, v_size_837_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 1);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v_val_843_ = v___x_853_;
goto v___jp_842_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_847_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_847_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 0);
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v_val_843_ = v___x_861_;
goto v___jp_842_;
}
}
}
v___jp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_val_843_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_840_, v___x_841_, v___x_845_, v___f_839_);
return v___x_846_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recv_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_836_ = stack[0].m_obj;
uint64_t v_size_837_ = stack[1].m_num;
lean_object* v_res_864_;
v_res_864_ = l_Std_Async_TCP_Socket_Client_recv_x3f(v_s_836_, v_size_837_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object* v_s_865_, lean_object* v_size_866_, lean_object* v_a_867_){
_start:
{
uint64_t v_size_boxed_868_; lean_object* v_res_869_; 
v_size_boxed_868_ = lean_unbox_uint64(v_size_866_);
lean_dec_ref(v_size_866_);
v_res_869_ = l_Std_Async_TCP_Socket_Client_recv_x3f(v_s_865_, v_size_boxed_868_);
lean_dec(v_s_865_);
return v_res_869_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(lean_object* v_promise_870_, lean_object* v_value_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_io_promise_resolve(v_value_871_, v_promise_870_);
return v___x_873_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_870_ = stack[0].m_obj;
lean_object* v_value_871_ = stack[1].m_obj;
lean_object* v_res_874_;
v_res_874_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(v_promise_870_, v_value_871_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0___boxed(lean_object* v_promise_875_, lean_object* v_value_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(v_promise_875_, v_value_876_);
lean_dec(v_promise_875_);
return v_res_878_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(lean_object* v_val_882_, lean_object* v___x_883_, uint64_t v_size_884_, lean_object* v_w_885_, lean_object* v_lose_886_){
_start:
{
lean_object* v_finished_888_; lean_object* v_promise_889_; lean_object* v_a_891_; lean_object* v___f_895_; lean_object* v___x_896_; uint8_t v___y_898_; uint8_t v___x_922_; 
v_finished_888_ = lean_ctor_get(v_w_885_, 0);
lean_inc(v_finished_888_);
v_promise_889_ = lean_ctor_get(v_w_885_, 1);
lean_inc_n(v_promise_889_, 2);
lean_dec_ref(v_w_885_);
v___f_895_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0___boxed), 3, 1);
lean_closure_set(v___f_895_, 0, v_promise_889_);
v___x_896_ = lean_st_ref_take(v_finished_888_);
v___x_922_ = lean_unbox(v___x_896_);
lean_dec(v___x_896_);
if (v___x_922_ == 0)
{
uint8_t v___x_923_; 
v___x_923_ = 1;
v___y_898_ = v___x_923_;
goto v___jp_897_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = 0;
v___y_898_ = v___x_924_;
goto v___jp_897_;
}
v___jp_890_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_a_891_);
v___x_893_ = lean_io_promise_resolve(v___x_892_, v_promise_889_);
lean_dec(v_promise_889_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
v___jp_897_:
{
uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = 1;
v___x_900_ = lean_box(v___x_899_);
v___x_901_ = lean_st_ref_put(v_finished_888_, v___x_900_);
lean_dec(v_finished_888_);
if (v___y_898_ == 0)
{
lean_object* v___x_902_; 
lean_dec_ref(v___f_895_);
lean_dec(v_promise_889_);
lean_dec_ref(v_val_882_);
v___x_902_ = lean_apply_1(v_lose_886_, lean_box(0));
return v___x_902_;
}
else
{
lean_object* v___x_903_; 
lean_dec_ref(v_lose_886_);
v___x_903_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_882_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; 
lean_dec_ref_known(v___x_903_, 1);
v___x_904_ = lean_uv_tcp_recv(v___x_883_, v_size_884_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_promise_889_);
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_919_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_919_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_919_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___f_909_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__1));
v___x_910_ = lean_io_promise_result_opt(v_a_905_);
lean_dec(v_a_905_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = 0;
v___x_913_ = lean_task_map(v___f_909_, v___x_910_, v___x_911_, v___x_912_);
v___x_914_ = lean_box(0);
v___x_915_ = lean_io_map_task(v___f_895_, v___x_913_, v___x_911_, v___x_912_);
lean_dec_ref(v___x_915_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_914_);
v___x_917_ = v___x_907_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_914_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
else
{
lean_object* v_a_920_; 
lean_dec_ref(v___f_895_);
v_a_920_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_904_, 1);
v_a_891_ = v_a_920_;
goto v___jp_890_;
}
}
else
{
lean_object* v_a_921_; 
lean_dec_ref(v___f_895_);
v_a_921_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_903_, 1);
v_a_891_ = v_a_921_;
goto v___jp_890_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_882_ = stack[0].m_obj;
lean_object* v___x_883_ = stack[1].m_obj;
uint64_t v_size_884_ = stack[2].m_num;
lean_object* v_w_885_ = stack[3].m_obj;
lean_object* v_lose_886_ = stack[4].m_obj;
lean_object* v_res_925_;
v_res_925_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_882_, v___x_883_, v_size_884_, v_w_885_, v_lose_886_);
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(lean_object* v_val_926_, lean_object* v___x_927_, lean_object* v_size_928_, lean_object* v_w_929_, lean_object* v_lose_930_, lean_object* v___y_931_){
_start:
{
uint64_t v_size_boxed_932_; lean_object* v_res_933_; 
v_size_boxed_932_ = lean_unbox_uint64(v_size_928_);
lean_dec_ref(v_size_928_);
v_res_933_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_926_, v___x_927_, v_size_boxed_932_, v_w_929_, v_lose_930_);
lean_dec(v___x_927_);
return v_res_933_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(lean_object* v_x_934_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
v_a_936_ = lean_ctor_get(v_x_934_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v_x_934_);
if (v_isSharedCheck_944_ == 0)
{
v___x_938_ = v_x_934_;
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v_x_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_943_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_954_; 
v_a_945_ = lean_ctor_get(v_x_934_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_x_934_);
if (v_isSharedCheck_954_ == 0)
{
v___x_947_ = v_x_934_;
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v_x_934_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_a_945_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_934_ = stack[0].m_obj;
lean_object* v_res_955_;
v_res_955_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(v_x_934_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(lean_object* v_x_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(v_x_956_);
return v_res_958_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_973_; 
v_a_965_ = lean_ctor_get(v_x_963_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v_x_963_);
if (v_isSharedCheck_973_ == 0)
{
v___x_967_ = v_x_963_;
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v_x_963_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_972_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
}
else
{
lean_object* v___x_974_; 
lean_dec_ref_known(v_x_963_, 1);
v___x_974_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___closed__1));
return v___x_974_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_963_ = stack[0].m_obj;
lean_object* v_res_975_;
v_res_975_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(v_x_963_);
stack->m_obj
 = v_res_975_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(lean_object* v_x_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(v_x_976_);
return v_res_978_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(lean_object* v_s_979_){
_start:
{
lean_object* v_val_982_; lean_object* v___x_984_; 
v___x_984_ = lean_uv_tcp_cancel_recv(v_s_979_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
v_val_982_ = v___x_990_;
goto v___jp_981_;
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_a_993_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_984_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_984_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set_tag(v___x_995_, 0);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
v_val_982_ = v___x_998_;
goto v___jp_981_;
}
}
}
v___jp_981_:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_val_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_979_ = stack[0].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(v_s_979_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(lean_object* v_s_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(v_s_1002_);
lean_dec(v_s_1002_);
return v_res_1004_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(lean_object* v_s_1005_, uint64_t v_size_1006_, lean_object* v_waiter_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_a_1011_; 
if (lean_obj_tag(v_a_1008_) == 0)
{
lean_object* v___x_1013_; 
lean_dec_ref(v_waiter_1007_);
v___x_1013_ = lean_box(0);
v_a_1011_ = v___x_1013_;
goto v___jp_1010_;
}
else
{
lean_object* v_val_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; 
v_val_1014_ = lean_ctor_get(v_a_1008_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v_a_1008_, 1);
v___f_1015_ = ((lean_object*)(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0));
v___x_1016_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_1014_, v_s_1005_, v_size_1006_, v_waiter_1007_, v___f_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v_a_1011_ = v_a_1017_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1016_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
v___jp_1010_:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_a_1011_);
return v___x_1012_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1005_ = stack[0].m_obj;
uint64_t v_size_1006_ = stack[1].m_num;
lean_object* v_waiter_1007_ = stack[2].m_obj;
lean_object* v_a_1008_ = stack[3].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(v_s_1005_, v_size_1006_, v_waiter_1007_, v_a_1008_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(lean_object* v_s_1027_, lean_object* v_size_1028_, lean_object* v_waiter_1029_, lean_object* v_a_1030_, lean_object* v___y_1031_){
_start:
{
uint64_t v_size_boxed_1032_; lean_object* v_res_1033_; 
v_size_boxed_1032_ = lean_unbox_uint64(v_size_1028_);
lean_dec_ref(v_size_1028_);
v_res_1033_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(v_s_1027_, v_size_boxed_1032_, v_waiter_1029_, v_a_1030_);
lean_dec(v_s_1027_);
return v_res_1033_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(lean_object* v___f_1038_, lean_object* v_x_1039_){
_start:
{
if (lean_obj_tag(v_x_1039_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___f_1038_);
v_a_1041_ = lean_ctor_get(v_x_1039_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v_x_1039_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v_x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_a_1050_ = lean_ctor_get(v_x_1039_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v_x_1039_, 1);
v___x_1051_ = lean_io_promise_result_opt(v_a_1050_);
lean_dec(v_a_1050_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = 0;
v___x_1054_ = lean_io_map_task(v___f_1038_, v___x_1051_, v___x_1052_, v___x_1053_);
lean_dec_ref(v___x_1054_);
v___x_1055_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1));
return v___x_1055_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1038_ = stack[0].m_obj;
lean_object* v_x_1039_ = stack[1].m_obj;
lean_object* v_res_1056_;
v_res_1056_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(v___f_1038_, v_x_1039_);
stack->m_obj
 = v_res_1056_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(lean_object* v___f_1057_, lean_object* v_x_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(v___f_1057_, v_x_1058_);
return v_res_1060_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(lean_object* v_s_1061_, uint64_t v_size_1062_, lean_object* v_waiter_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; lean_object* v_val_1071_; lean_object* v___x_1074_; 
v___x_1065_ = lean_box_uint64(v_size_1062_);
lean_inc(v_s_1061_);
v___f_1066_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed), 5, 3);
lean_closure_set(v___f_1066_, 0, v_s_1061_);
lean_closure_set(v___f_1066_, 1, v___x_1065_);
lean_closure_set(v___f_1066_, 2, v_waiter_1063_);
v___f_1067_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1067_, 0, v___f_1066_);
v___x_1068_ = lean_unsigned_to_nat(0u);
v___x_1069_ = 0;
v___x_1074_ = lean_uv_tcp_wait_readable(v_s_1061_);
lean_dec(v_s_1061_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 1);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v_val_1071_ = v___x_1080_;
goto v___jp_1070_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1074_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v_val_1071_ = v___x_1088_;
goto v___jp_1070_;
}
}
}
v___jp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_val_1071_);
v___x_1073_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1068_, v___x_1069_, v___x_1072_, v___f_1067_);
return v___x_1073_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1061_ = stack[0].m_obj;
uint64_t v_size_1062_ = stack[1].m_num;
lean_object* v_waiter_1063_ = stack[2].m_obj;
lean_object* v_res_1091_;
v_res_1091_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(v_s_1061_, v_size_1062_, v_waiter_1063_);
stack->m_obj
 = v_res_1091_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(lean_object* v_s_1092_, lean_object* v_size_1093_, lean_object* v_waiter_1094_, lean_object* v___y_1095_){
_start:
{
uint64_t v_size_boxed_1096_; lean_object* v_res_1097_; 
v_size_boxed_1096_ = lean_unbox_uint64(v_size_1093_);
lean_dec_ref(v_size_1093_);
v_res_1097_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(v_s_1092_, v_size_boxed_1096_, v_waiter_1094_);
return v_res_1097_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(lean_object* v___f_1098_, lean_object* v___x_1099_, uint8_t v___x_1100_, lean_object* v_x_1101_){
_start:
{
if (lean_obj_tag(v_x_1101_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v___x_1099_);
lean_dec_ref(v___f_1098_);
v_a_1103_ = lean_ctor_get(v_x_1101_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_x_1101_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1105_ = v_x_1101_;
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v_x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1112_; 
v_a_1112_ = lean_ctor_get(v_x_1101_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v_x_1101_, 1);
if (lean_obj_tag(v_a_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v___x_1099_);
lean_dec_ref(v___f_1098_);
v_a_1113_ = lean_ctor_get(v_a_1112_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_1112_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v_a_1112_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v_a_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1122_ = lean_ctor_get(v_a_1112_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v_a_1112_, 1);
v___x_1123_ = lean_io_promise_result_opt(v_a_1122_);
lean_dec(v_a_1122_);
v___x_1124_ = lean_task_map(v___f_1098_, v___x_1123_, v___x_1099_, v___x_1100_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1098_ = stack[0].m_obj;
lean_object* v___x_1099_ = stack[1].m_obj;
uint8_t v___x_1100_ = stack[2].m_num;
lean_object* v_x_1101_ = stack[3].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(v___f_1098_, v___x_1099_, v___x_1100_, v_x_1101_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(lean_object* v___f_1127_, lean_object* v___x_1128_, lean_object* v___x_1129_, lean_object* v_x_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v___x_3071__boxed_1132_; lean_object* v_res_1133_; 
v___x_3071__boxed_1132_ = lean_unbox(v___x_1129_);
v_res_1133_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(v___f_1127_, v___x_1128_, v___x_3071__boxed_1132_, v_x_1130_);
return v_res_1133_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(lean_object* v___f_1139_, lean_object* v_s_1140_, lean_object* v___f_1141_, uint64_t v_size_1142_, lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v___f_1141_);
lean_dec_ref(v___f_1139_);
v_a_1145_ = lean_ctor_get(v_x_1143_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1143_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v_x_1143_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v_x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1202_; 
v_a_1154_ = lean_ctor_get(v_x_1143_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_1143_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1156_ = v_x_1143_;
v_isShared_1157_ = v_isSharedCheck_1202_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v_x_1143_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1202_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_unbox(v_a_1154_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; lean_object* v_val_1161_; lean_object* v___x_1165_; 
lean_dec_ref(v___f_1141_);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1165_ = lean_uv_tcp_cancel_recv(v_s_1140_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v_a_1166_);
v___x_1168_ = v___x_1156_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v_val_1161_ = v___x_1168_;
goto v___jp_1160_;
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; 
v_a_1170_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1165_, 1);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 0);
lean_ctor_set(v___x_1156_, 0, v_a_1170_);
v___x_1172_ = v___x_1156_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v_val_1161_ = v___x_1172_;
goto v___jp_1160_;
}
}
v___jp_1160_:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_val_1161_);
v___x_1163_ = lean_unbox(v_a_1154_);
lean_dec(v_a_1154_);
v___x_1164_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1159_, v___x_1163_, v___x_1162_, v___f_1139_);
return v___x_1164_;
}
}
else
{
lean_object* v___x_1174_; uint8_t v___x_1175_; lean_object* v___f_1176_; lean_object* v_val_1178_; lean_object* v___x_1185_; 
lean_dec(v_a_1154_);
lean_dec_ref(v___f_1139_);
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = 0;
v___f_1176_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___closed__0));
v___x_1185_ = lean_uv_tcp_recv(v_s_1140_, v_size_1142_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set_tag(v___x_1188_, 1);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_val_1178_ = v___x_1191_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1185_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1185_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 0);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
v_val_1178_ = v___x_1199_;
goto v___jp_1177_;
}
}
}
v___jp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v_val_1178_);
v___x_1180_ = v___x_1156_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_val_1178_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
v___x_1182_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1174_, v___x_1175_, v___x_1181_, v___f_1176_);
v___x_1183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1174_, v___x_1175_, v___x_1182_, v___f_1141_);
return v___x_1183_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1139_ = stack[0].m_obj;
lean_object* v_s_1140_ = stack[1].m_obj;
lean_object* v___f_1141_ = stack[2].m_obj;
uint64_t v_size_1142_ = stack[3].m_num;
lean_object* v_x_1143_ = stack[4].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(v___f_1139_, v_s_1140_, v___f_1141_, v_size_1142_, v_x_1143_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(lean_object* v___f_1204_, lean_object* v_s_1205_, lean_object* v___f_1206_, lean_object* v_size_1207_, lean_object* v_x_1208_, lean_object* v___y_1209_){
_start:
{
uint64_t v_size_boxed_1210_; lean_object* v_res_1211_; 
v_size_boxed_1210_ = lean_unbox_uint64(v_size_1207_);
lean_dec_ref(v_size_1207_);
v_res_1211_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(v___f_1204_, v_s_1205_, v___f_1206_, v_size_boxed_1210_, v_x_1208_);
lean_dec(v_s_1205_);
return v_res_1211_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(lean_object* v___f_1212_, lean_object* v_x_1213_){
_start:
{
if (lean_obj_tag(v_x_1213_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___f_1212_);
v_a_1215_ = lean_ctor_get(v_x_1213_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v_x_1213_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v_x_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1237_; 
v_a_1224_ = lean_ctor_get(v_x_1213_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1213_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1226_ = v_x_1213_;
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v_x_1213_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1237_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = 0;
v___x_1230_ = l_IO_Promise_isResolved___redArg(v_a_1224_);
lean_dec(v_a_1224_);
v___x_1231_ = lean_box(v___x_1230_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v___x_1231_);
v___x_1233_ = v___x_1226_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
v___x_1235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1228_, v___x_1229_, v___x_1234_, v___f_1212_);
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1212_ = stack[0].m_obj;
lean_object* v_x_1213_ = stack[1].m_obj;
lean_object* v_res_1238_;
v_res_1238_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(v___f_1212_, v_x_1213_);
stack->m_obj
 = v_res_1238_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__8___boxed(lean_object* v___f_1239_, lean_object* v_x_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__8(v___f_1239_, v_x_1240_);
return v_res_1242_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(lean_object* v___f_1243_, lean_object* v_s_1244_){
_start:
{
lean_object* v___x_1246_; uint8_t v___x_1247_; lean_object* v_val_1249_; lean_object* v___x_1252_; 
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = 0;
v___x_1252_ = lean_uv_tcp_wait_readable(v_s_1244_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v_val_1249_ = v___x_1258_;
goto v___jp_1248_;
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1252_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1252_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 0);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v_val_1249_ = v___x_1266_;
goto v___jp_1248_;
}
}
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_val_1249_);
v___x_1251_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1246_, v___x_1247_, v___x_1250_, v___f_1243_);
return v___x_1251_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1243_ = stack[0].m_obj;
lean_object* v_s_1244_ = stack[1].m_obj;
lean_object* v_res_1269_;
v_res_1269_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(v___f_1243_, v_s_1244_);
stack->m_obj
 = v_res_1269_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(lean_object* v___f_1270_, lean_object* v_s_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(v___f_1270_, v_s_1271_);
lean_dec(v_s_1271_);
return v_res_1273_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_recvSelector(lean_object* v_s_1276_, uint64_t v_size_1277_){
_start:
{
lean_object* v___f_1278_; lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; 
v___f_1278_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__0));
v___f_1279_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_recvSelector___closed__1));
lean_inc_n(v_s_1276_, 3);
v___f_1280_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed), 2, 1);
lean_closure_set(v___f_1280_, 0, v_s_1276_);
v___x_1281_ = lean_box_uint64(v_size_1277_);
v___f_1282_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1282_, 0, v_s_1276_);
lean_closure_set(v___f_1282_, 1, v___x_1281_);
v___x_1283_ = lean_box_uint64(v_size_1277_);
v___f_1284_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed), 6, 4);
lean_closure_set(v___f_1284_, 0, v___f_1279_);
lean_closure_set(v___f_1284_, 1, v_s_1276_);
lean_closure_set(v___f_1284_, 2, v___f_1278_);
lean_closure_set(v___f_1284_, 3, v___x_1283_);
v___f_1285_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1285_, 0, v___f_1284_);
v___f_1286_ = lean_alloc_closure((void*)(l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed), 3, 2);
lean_closure_set(v___f_1286_, 0, v___f_1285_);
lean_closure_set(v___f_1286_, 1, v_s_1276_);
v___x_1287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1287_, 0, v___f_1286_);
lean_ctor_set(v___x_1287_, 1, v___f_1282_);
lean_ctor_set(v___x_1287_, 2, v___f_1280_);
return v___x_1287_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_recvSelector_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1276_ = stack[0].m_obj;
uint64_t v_size_1277_ = stack[1].m_num;
lean_object* v_res_1288_;
v_res_1288_ = l_Std_Async_TCP_Socket_Client_recvSelector(v_s_1276_, v_size_1277_);
stack->m_obj
 = v_res_1288_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_recvSelector___boxed(lean_object* v_s_1289_, lean_object* v_size_1290_){
_start:
{
uint64_t v_size_boxed_1291_; lean_object* v_res_1292_; 
v_size_boxed_1291_ = lean_unbox_uint64(v_size_1290_);
lean_dec_ref(v_size_1290_);
v_res_1292_ = l_Std_Async_TCP_Socket_Client_recvSelector(v_s_1289_, v_size_boxed_1291_);
return v_res_1292_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_shutdown(lean_object* v_s_1293_){
_start:
{
lean_object* v___f_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v_val_1299_; lean_object* v___x_1303_; 
v___f_1295_ = ((lean_object*)(l_Std_Async_TCP_Socket_Client_connect___closed__1));
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = 0;
v___x_1303_ = lean_uv_tcp_shutdown(v_s_1293_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set_tag(v___x_1306_, 1);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
v_val_1299_ = v___x_1309_;
goto v___jp_1298_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
v_a_1312_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1303_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1303_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 0);
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
v_val_1299_ = v___x_1317_;
goto v___jp_1298_;
}
}
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_val_1299_);
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
v___x_1302_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1296_, v___x_1297_, v___x_1301_, v___f_1295_);
return v___x_1302_;
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_shutdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1293_ = stack[0].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l_Std_Async_TCP_Socket_Client_shutdown(v_s_1293_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_shutdown___boxed(lean_object* v_s_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Std_Async_TCP_Socket_Client_shutdown(v_s_1321_);
lean_dec(v_s_1321_);
return v_res_1323_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_getPeerName(lean_object* v_s_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_uv_tcp_getpeername(v_s_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_getPeerName_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1324_ = stack[0].m_obj;
lean_object* v_res_1327_;
v_res_1327_ = l_Std_Async_TCP_Socket_Client_getPeerName(v_s_1324_);
stack->m_obj
 = v_res_1327_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getPeerName___boxed(lean_object* v_s_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Std_Async_TCP_Socket_Client_getPeerName(v_s_1328_);
lean_dec(v_s_1328_);
return v_res_1330_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_getSockName(lean_object* v_s_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_uv_tcp_getsockname(v_s_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_getSockName_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1331_ = stack[0].m_obj;
lean_object* v_res_1334_;
v_res_1334_ = l_Std_Async_TCP_Socket_Client_getSockName(v_s_1331_);
stack->m_obj
 = v_res_1334_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_getSockName___boxed(lean_object* v_s_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_Async_TCP_Socket_Client_getSockName(v_s_1335_);
lean_dec(v_s_1335_);
return v_res_1337_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_noDelay(lean_object* v_s_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_uv_tcp_nodelay(v_s_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_noDelay_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1338_ = stack[0].m_obj;
lean_object* v_res_1341_;
v_res_1341_ = l_Std_Async_TCP_Socket_Client_noDelay(v_s_1338_);
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_noDelay___boxed(lean_object* v_s_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_Async_TCP_Socket_Client_noDelay(v_s_1342_);
lean_dec(v_s_1342_);
return v_res_1344_;
}
}
static lean_object* _init_l_Std_Async_TCP_Socket_Client_keepAlive___auto__1(void){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_obj_once(&l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26, &l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once, _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26);
return v___x_1345_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg(lean_object* v_s_1346_, uint8_t v_enable_1347_, lean_object* v_delay_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_1348_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; uint8_t v___x_1352_; uint32_t v___x_1353_; lean_object* v___x_1354_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = lean_bool_to_int8(v_enable_1347_);
v___x_1353_ = lean_unbox_uint32(v_a_1351_);
lean_dec(v_a_1351_);
v___x_1354_ = lean_uv_tcp_keepalive(v_s_1346_, v___x_1352_, v___x_1353_);
return v___x_1354_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1350_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1350_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_keepAlive___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1346_ = stack[0].m_obj;
uint8_t v_enable_1347_ = stack[1].m_num;
lean_object* v_delay_1348_ = stack[2].m_obj;
lean_object* v_res_1363_;
v_res_1363_ = l_Std_Async_TCP_Socket_Client_keepAlive___redArg(v_s_1346_, v_enable_1347_, v_delay_1348_);
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___redArg___boxed(lean_object* v_s_1364_, lean_object* v_enable_1365_, lean_object* v_delay_1366_, lean_object* v_a_1367_){
_start:
{
uint8_t v_enable_boxed_1368_; lean_object* v_res_1369_; 
v_enable_boxed_1368_ = lean_unbox(v_enable_1365_);
v_res_1369_ = l_Std_Async_TCP_Socket_Client_keepAlive___redArg(v_s_1364_, v_enable_boxed_1368_, v_delay_1366_);
lean_dec(v_delay_1366_);
lean_dec(v_s_1364_);
return v_res_1369_;
}
}
lean_object* l_Std_Async_TCP_Socket_Client_keepAlive(lean_object* v_s_1370_, uint8_t v_enable_1371_, lean_object* v_delay_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Std_Async_TCP_0__Std_Async_TCP_Socket_keepAliveDelay(v_delay_1372_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; uint8_t v___x_1377_; uint32_t v___x_1378_; lean_object* v___x_1379_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = lean_bool_to_int8(v_enable_1371_);
v___x_1378_ = lean_unbox_uint32(v_a_1376_);
lean_dec(v_a_1376_);
v___x_1379_ = lean_uv_tcp_keepalive(v_s_1370_, v___x_1377_, v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1375_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1375_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_TCP_Socket_Client_keepAlive_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1370_ = stack[0].m_obj;
uint8_t v_enable_1371_ = stack[1].m_num;
lean_object* v_delay_1372_ = stack[2].m_obj;
lean_object* v_res_1388_;
v_res_1388_ = l_Std_Async_TCP_Socket_Client_keepAlive(v_s_1370_, v_enable_1371_, v_delay_1372_, lean_box(0));
stack->m_obj
 = v_res_1388_;
}
LEAN_EXPORT lean_object* l_Std_Async_TCP_Socket_Client_keepAlive___boxed(lean_object* v_s_1389_, lean_object* v_enable_1390_, lean_object* v_delay_1391_, lean_object* v_x_1392_, lean_object* v_a_1393_){
_start:
{
uint8_t v_enable_boxed_1394_; lean_object* v_res_1395_; 
v_enable_boxed_1394_ = lean_unbox(v_enable_1390_);
v_res_1395_ = l_Std_Async_TCP_Socket_Client_keepAlive(v_s_1389_, v_enable_boxed_1394_, v_delay_1391_, v_x_1392_);
lean_dec(v_delay_1391_);
lean_dec(v_s_1389_);
return v_res_1395_;
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
